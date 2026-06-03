#!/usr/bin/env python3
"""
prevalence_corpus.py

Run the validated A_1 harness over a CORPUS of LangGraph graphs to estimate
how often real multi-agent graphs with shared state actually exhibit
cross-agent stale generation. Uses compute_layers() so each node's superstep
is its topological layer -- no hand assignment -- which lets you point this at
graphs you did NOT write.

THE HONEST BOUNDARY (read this before reporting any number)
  This is the INSTRUMENT. The prevalence CLAIM is only as good as the corpus.
  The example graphs below are illustrative PATTERNS (map-reduce fan-out,
  supervisor-workers, sequential pipeline), not a corpus -- they are still
  graphs we wrote. A defensible prevalence number requires REAL third-party
  graphs (GitHub apps, LangChain templates) added via add_graph(), run
  unmodified except for the light wrapping the recipe shows. Report:
  "X of N real graphs sampled from <source> exhibit cross-agent A_1", with the
  corpus described.

CAVEATS (disclose in the paper)
  * Layers are computed from STATIC edges; conditional edges / cycles are
    approximated (a node's layer = longest static-path depth). Graphs with
    data-dependent routing need runtime superstep capture; flagged per graph.
  * The detector is the verified superstep-scoped cross-agent A_1
    (lib_l2_safety.rs::a1_witness); any-agent reported alongside.
  * Rates are largely topology-driven, not model-driven; running multiple
    models mainly demonstrates model-independence of the structural rate.

RECIPE: add a real third-party graph
  Given someone else's graph that builds nodes {name: fn} and edges
  [(src,tgt),...], you do NOT rewrite it -- you wrap its nodes:

      from prevalence_harness import SessionRecorder, instrument_layered
      def build(client, rec):
          node_fns = { ... the graph's node callables ... }
          edges    = [ ... the graph's edges, START/END as "__start__"/"__end__" ... ]
          wrapped  = instrument_layered(rec, node_fns, edges)
          g = StateGraph(TheirStateType)
          for name, fn in wrapped.items(): g.add_node(name, fn)
          for a, b in edges: g.add_edge(a, b)
          return g.compile(), {initial state}
      add_graph("their_repo_name", build)

USAGE
  python prevalence_corpus.py --provider openai --model gpt-4o --n 50 --out ./corpus_oprecords
  python prevalence_corpus.py --provider vllm --base-url http://localhost:8000/v1 \
         --model meta-llama/Llama-3.1-8B-Instruct --n 50 --out ./corpus_oprecords
  python prevalence_harness.py analyze ./corpus_oprecords --out corpus_rates.json
"""
from __future__ import annotations
import argparse
from pathlib import Path
from typing import Annotated, Callable, TypedDict

from prevalence_harness import SessionRecorder, instrument_layered

try:
    from prevalence_langgraph_example import ModelClient
except Exception:
    ModelClient = None  # analysis-only environments


# registry: name -> build(client, recorder) -> (compiled_app, initial_input)
_GRAPHS: dict[str, Callable] = {}


def add_graph(name: str, build: Callable) -> None:
    _GRAPHS[name] = build


# ---------------------------------------------------------------------
# Illustrative patterns (NOT a corpus). Each shows a common shared-state
# topology. Replace/extend with real third-party graphs for a real study.
# ---------------------------------------------------------------------
def _lww(_a, b):
    return b


def _register_examples():
    from langgraph.graph import StateGraph, START, END

    class WS(TypedDict):
        task:   Annotated[str, _lww]
        plan:   Annotated[str, _lww]
        r1:     Annotated[str, _lww]
        r2:     Annotated[str, _lww]
        summary: Annotated[str, _lww]

    # (1) supervisor -> two workers (same layer, both read `plan`) -> reducer.
    #     Realistic shared-state fan-out; A_1 possible iff workers race on a
    #     shared cell they both read-then-depend-on.
    def build_supervisor(client, rec):
        def supervisor(s): return {"plan": client.complete(
            "Plan the task in one sentence.", f"Task: {s.get('task','')}") or "PLAN"}
        def worker1(s): return {"r1": client.complete(
            "Do part 1 given the plan, one sentence.", f"Plan: {s.get('plan','')}") or "R1"}
        def worker2(s): return {"r2": client.complete(
            "Do part 2 given the plan, one sentence.", f"Plan: {s.get('plan','')}") or "R2"}
        def reducer(s): return {"summary": client.complete(
            "Summarise results in one sentence.",
            f"R1: {s.get('r1','')}\nR2: {s.get('r2','')}") or "SUM"}
        node_fns = {"supervisor": supervisor, "worker1": worker1,
                    "worker2": worker2, "reducer": reducer}
        edges = [(START, "supervisor"), ("supervisor", "worker1"),
                 ("supervisor", "worker2"), ("worker1", "reducer"),
                 ("worker2", "reducer"), ("reducer", END)]
        wrapped = instrument_layered(rec, node_fns, edges)
        g = StateGraph(WS)
        for name, fn in wrapped.items():
            g.add_node(name, fn)
        for a, b in edges:
            g.add_edge(a, b)
        return g.compile(), {"task": "Audit the onboarding flow.",
                             "plan": "", "r1": "", "r2": "", "summary": ""}

    # (2) sequential pipeline (control: expect ~0% -- distinct layers).
    def build_pipeline(client, rec):
        def a(s): return {"plan": client.complete("Plan.", s.get("task","")) or "PLAN"}
        def b(s): return {"r1": client.complete("Execute the plan.", s.get("plan","")) or "R1"}
        def c(s): return {"summary": client.complete("Summarise.", s.get("r1","")) or "SUM"}
        node_fns = {"a": a, "b": b, "c": c}
        edges = [(START, "a"), ("a", "b"), ("b", "c"), ("c", END)]
        wrapped = instrument_layered(rec, node_fns, edges)
        g = StateGraph(WS)
        for name, fn in wrapped.items():
            g.add_node(name, fn)
        for x, y in edges:
            g.add_edge(x, y)
        return g.compile(), {"task": "Audit the onboarding flow.",
                             "plan": "", "r1": "", "r2": "", "summary": ""}

    add_graph("supervisor_fanout", build_supervisor)
    add_graph("sequential_pipeline", build_pipeline)

    # (3) racy positive control: two same-layer nodes where one writes a cell
    #     the other reads (writer & reader in the SAME superstep). Expect A_1.
    def build_racy(client, rec):
        def producer(s): return {"plan": client.complete("Plan.", s.get("task","")) or "PLAN"}
        def consumer(s): return {"r1": client.complete("Use the plan.", s.get("plan","")) or "R1"}
        node_fns = {"producer": producer, "consumer": consumer}
        edges = [(START, "producer"), (START, "consumer"),
                 ("producer", END), ("consumer", END)]
        wrapped = instrument_layered(rec, node_fns, edges)
        g = StateGraph(WS)
        for name, fn in wrapped.items():
            g.add_node(name, fn)
        for a, b in edges:
            g.add_edge(a, b)
        return g.compile(), {"task": "Audit the onboarding flow.",
                             "plan": "", "r1": "", "r2": "", "summary": ""}

    add_graph("racy_control", build_racy)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--provider", required=True, choices=["openai", "vllm", "anthropic"])
    ap.add_argument("--model", required=True)
    ap.add_argument("--base-url", default=None)
    ap.add_argument("--n", type=int, default=50)
    ap.add_argument("--out", default="./corpus_oprecords")
    args = ap.parse_args()

    if ModelClient is None:
        raise SystemExit("ModelClient unavailable; install openai/anthropic and langgraph.")
    _register_examples()
    client = ModelClient(args.provider, args.model, args.base_url)
    outdir = Path(args.out)
    safe = args.model.replace("/", "_")

    for gname, build in _GRAPHS.items():
        for i in range(args.n):
            sid = f"langgraph-{gname}-{safe}-{i:04d}"
            rec = SessionRecorder(outdir / f"{sid}.jsonl", framework="langgraph",
                                  model=args.model, scenario=gname, session_id=sid).open()
            try:
                app, init = build(client, rec)
                app.invoke(init)
            finally:
                rec.close()
        print(f"  {gname}: {args.n} sessions")
    print(f"done; analyse with:  python prevalence_harness.py analyze {args.out} --out corpus_rates.json")


if __name__ == "__main__":
    main()