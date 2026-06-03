#!/usr/bin/env python3
"""
prevalence_langgraph_example.py

A REAL LangGraph StateGraph, instrumented with prevalence_harness so each
node's shared-state read/write becomes an OpRecord, run across models
(OpenAI / Anthropic / any vLLM-served open-weights model) and across two
topologies. This is the runnable end-to-end for the real-deployment
prevalence study.

WHY TWO TOPOLOGIES
  The prevalence question is whether real graphs with shared mutable state
  exhibit A_1. We expose that directly:
    --topology sequential : planner -> executor -> reviewer. Each node reads
        the committed output of the previous superstep; no A_1 expected.
    --topology racy       : planner and executor BOTH fan out from START in
        the SAME superstep. The executor receives the PRE-superstep state, so
        it reads an empty/stale `plan` while the planner concurrently commits
        the real one -- the documented LangGraph foot-gun (concurrent nodes in
        a superstep see pre-superstep state). A_1 is expected here.
  Running both shows the detector fires exactly when the topology is unsafe,
  which is the realistic-misconfiguration prevalence claim.

INSTALL
  pip install langgraph openai anthropic

RUN (examples)
  # hosted
  python prevalence_langgraph_example.py --provider openai   --model gpt-4o            --topology racy       --n 100 --out ./oprecords
  python prevalence_langgraph_example.py --provider anthropic --model claude-sonnet-4-5 --topology sequential --n 100 --out ./oprecords
  # open-weights via a local vLLM OpenAI-compatible server:
  #   python -m vllm.entrypoints.openai.api_server --model meta-llama/Llama-3.1-8B-Instruct --port 8000
  python prevalence_langgraph_example.py --provider vllm --base-url http://localhost:8000/v1 \
         --model meta-llama/Llama-3.1-8B-Instruct --topology racy --n 100 --out ./oprecords

  then aggregate ALL collected sessions:
  python prevalence_harness.py analyze ./oprecords --out rates.json
"""
from __future__ import annotations
import argparse
import operator
import os
import sys
from pathlib import Path
from typing import Annotated, TypedDict

from prevalence_harness import SessionRecorder


# ---------------------------------------------------------------------
# Model client abstraction: one .complete(system, user) -> str
# ---------------------------------------------------------------------
class ModelClient:
    def __init__(self, provider: str, model: str, base_url: str | None = None):
        self.provider = provider
        self.model = model
        if provider in ("openai", "vllm"):
            from openai import OpenAI
            key = os.environ.get("OPENAI_API_KEY", "EMPTY" if provider == "vllm" else None)
            self._c = OpenAI(api_key=key, base_url=base_url) if base_url else OpenAI(api_key=key)
        elif provider == "anthropic":
            import anthropic
            self._c = anthropic.Anthropic()
        else:
            raise SystemExit(f"unknown provider {provider}")

    def complete(self, system: str, user: str, max_tokens: int = 120) -> str:
        try:
            if self.provider == "anthropic":
                r = self._c.messages.create(
                    model=self.model, max_tokens=max_tokens, system=system,
                    messages=[{"role": "user", "content": user}], temperature=0)
                return "".join(b.text for b in r.content if getattr(b, "type", "") == "text").strip()
            r = self._c.chat.completions.create(
                model=self.model, max_tokens=max_tokens, temperature=0,
                messages=[{"role": "system", "content": system},
                          {"role": "user", "content": user}])
            return (r.choices[0].message.content or "").strip()
        except Exception as e:
            print(f"  model error: {e}", file=sys.stderr)
            return ""


# ---------------------------------------------------------------------
# Shared state with last-write-wins reducers (so concurrent writes are
# allowed -- this is what lets the racy topology exhibit A_1 instead of
# raising InvalidUpdateError).
# ---------------------------------------------------------------------
def _lww(_a, b):           # last-write-wins reducer
    return b


class WS(TypedDict):
    task:   Annotated[str, _lww]
    plan:   Annotated[str, _lww]
    result: Annotated[str, _lww]
    review: Annotated[str, _lww]


def build_graph(client: ModelClient, rec: SessionRecorder, topology: str):
    from langgraph.graph import StateGraph, START, END

    def planner(state: WS) -> dict:
        plan = client.complete(
            "You are a planner. Output one concise sentence: the plan for the task.",
            f"Task: {state.get('task','')}")
        return {"plan": plan or "PLAN"}

    def executor(state: WS) -> dict:
        # reads `plan` from the state it was handed -- in the racy topology
        # this is the pre-superstep (empty) plan.
        result = client.complete(
            "You are an executor. Given the plan, output one sentence: the result.",
            f"Plan: {state.get('plan','')}")
        return {"result": result or "RESULT"}

    def reviewer(state: WS) -> dict:
        review = client.complete(
            "You are a reviewer. Given plan and result, output one sentence: the review.",
            f"Plan: {state.get('plan','')}\nResult: {state.get('result','')}")
        return {"review": review or "REVIEW"}

    g = StateGraph(WS)
    # superstep assignment encodes the topology's concurrency layers:
    #   racy:       planner & executor both in layer 0 (concurrent), reviewer 1
    #   sequential: planner 0, executor 1, reviewer 2 (no concurrency)
    if topology == "racy":
        ss_planner, ss_executor, ss_reviewer = 0, 0, 1
    else:
        ss_planner, ss_executor, ss_reviewer = 0, 1, 2
    g.add_node("planner",  rec.instrument(planner,  "planner",  superstep=ss_planner))
    g.add_node("executor", rec.instrument(executor, "executor", superstep=ss_executor))
    g.add_node("reviewer", rec.instrument(reviewer, "reviewer", superstep=ss_reviewer))

    if topology == "sequential":
        g.add_edge(START, "planner")
        g.add_edge("planner", "executor")
        g.add_edge("executor", "reviewer")
        g.add_edge("reviewer", END)
    elif topology == "racy":
        # planner and executor in the SAME first superstep: executor sees the
        # pre-superstep (empty) plan while planner commits the real one.
        g.add_edge(START, "planner")
        g.add_edge(START, "executor")
        g.add_edge("planner", "reviewer")
        g.add_edge("executor", "reviewer")
        g.add_edge("reviewer", END)
    else:
        raise SystemExit("topology must be sequential|racy")
    return g.compile()


TASKS = [
    "Summarise the quarterly sales report.",
    "Draft a migration plan for the auth service.",
    "Triage the incoming bug backlog.",
    "Design an onboarding checklist.",
    "Plan a load test for the API gateway.",
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--provider", required=True, choices=["openai", "vllm", "anthropic"])
    ap.add_argument("--model", required=True)
    ap.add_argument("--base-url", default=None)
    ap.add_argument("--topology", required=True, choices=["sequential", "racy"])
    ap.add_argument("--n", type=int, default=100)
    ap.add_argument("--out", default="./oprecords")
    args = ap.parse_args()

    client = ModelClient(args.provider, args.model, args.base_url)
    outdir = Path(args.out)
    safe_model = args.model.replace("/", "_")
    for i in range(args.n):
        sid = f"langgraph-{args.topology}-{safe_model}-{i:04d}"
        rec = SessionRecorder(outdir / f"{sid}.jsonl",
                              framework="langgraph", model=args.model,
                              scenario=args.topology, session_id=sid).open()
        try:
            app = build_graph(client, rec, args.topology)
            app.invoke({"task": TASKS[i % len(TASKS)], "plan": "", "result": "", "review": ""})
        finally:
            rec.close()
        if (i + 1) % 10 == 0:
            print(f"  {i+1}/{args.n} sessions")
    print(f"done; analyse with:  python prevalence_harness.py analyze {args.out} --out rates.json")


if __name__ == "__main__":
    main()