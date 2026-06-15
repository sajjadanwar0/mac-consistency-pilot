#!/usr/bin/env python3
"""
langgraph_a6.py -- A6 (tool-effect reordering) in LangGraph's ToolNode, live.

A real LangGraph agent: a chat model bound to N order-dependent stateful tools
emits its tool_calls for one turn; the DEFAULT ToolNode runs them via
asyncio.gather and commits their side effects in COMPLETION order (baseline),
while a sequenced executor commits them in tool_calls order (L3). Each turn is
replayed under both policies on the SAME model-emitted calls and scored with the
verified a6_witness predicate.

Two findings, of very different strength:

  STRUCTURAL (certain, proven by mechanism + reproduction):
    ToolNode does not serialize tool side effects, so any latency heterogeneity
    reorders them -- and because asyncio.gather preserves the result list, the
    ToolMessage order stays in call order, so the reorder is INVISIBLE in the
    conversation transcript. Corroborated by langchain-ai/langgraph#861 (stateful
    tools needing order), #6624 (parallel ToolNode via asyncio.gather), and a
    reported forum race (tool responses out of order).

  RATE (illustration only, NOT prevalence):
    Under a given tool-latency profile, A6 occurs in X% of the multi-tool turns a
    model emits. The rate is parameterized by the latency profile and by how often
    each model batches order-dependent calls into one turn; it is not a claim about
    A6 prevalence in deployed systems (that depends on each deployment's tools).

Lead with the structural finding; present the rate as an illustration; present
the sequenced ToolNode as the L3 discipline realized against a real framework
(and a drop-in fix for #861).

Latency modes:
  --latency modeled  (default) asyncio.sleep drawn from a heterogeneous range,
                     justified as modeling real tool-latency heterogeneity (#861).
                     Tunable, gives a clear illustrative rate; a reviewer may call
                     the rate constructed, which is why it stays an illustration.
  --latency real-io  each tool's side effect is a real append+fsync to a shared
                     file; latency is genuine but low-variance, so this is the
                     defensible FLOOR (real heterogeneous tools reorder more).

--dry-run skips the LLM and replays a hand-built ordered batch (step_0..step_{w-1}),
so you can validate the wiring against the real ToolNode without an API key.
"""

import argparse
import asyncio
import json
import os
import random
import time
from pathlib import Path
from typing import Annotated, TypedDict

from langchain_core.messages import AIMessage, ToolMessage
from langchain_core.tools import tool
from langgraph.prebuilt import ToolNode
from langgraph.graph import StateGraph, START, END
from langgraph.graph.message import add_messages


# ---- verified predicate (mirror of l3_sequencer::a6_witness in the runtime) ----
def a6_witness(io, co):
    return len(io) >= 2 and len(io) == len(co) and io != co


def inversions(co):
    return sum(1 for i in range(len(co)) for j in range(i + 1, len(co)) if co[i] > co[j])


# ---- shared, order-sensitive side-effect sink (reset per run) ----
class World:
    def __init__(self):
        self.effect_log = []   # step indices in COMMIT order  -> this is `co`
        self.timings = []      # (step, start, end)

    def reset(self):
        self.effect_log = []
        self.timings = []


WORLD = World()
_DELAYS = {}   # per-session modeled latency, redrawn each turn (see amain)


def make_tools(width, latency_mode, sink_path):
    """N order-dependent stateful tools over the shared sink."""
    def mk(i):
        async def _f(note: str = "") -> str:
            t0 = time.perf_counter()
            if latency_mode == "modeled":
                await asyncio.sleep(_DELAYS[i])
            else:  # real-io: a genuine append+fsync IS the side effect and the latency
                def _io():
                    with open(sink_path, "a") as fh:
                        fh.write(f"{i}\n")
                        fh.flush()
                        os.fsync(fh.fileno())
                await asyncio.to_thread(_io)
            WORLD.effect_log.append(i)              # observable commit order
            WORLD.timings.append((i, t0, time.perf_counter()))
            return f"step {i} committed"
        _f.__name__ = f"step_{i}"
        _f.__doc__ = (f"Perform ordered step {i} against the shared stateful system. "
                      f"Must take effect strictly after step {i - 1}.")
        return tool(_f)
    return [mk(i) for i in range(width)]


def build_baseline_graph(tools):
    class S(TypedDict):
        messages: Annotated[list, add_messages]
    g = StateGraph(S)
    g.add_node("tools", ToolNode(tools))   # the REAL default ToolNode
    g.add_edge(START, "tools")
    g.add_edge("tools", END)
    return g.compile()


async def run_sequenced(tools_by_name, calls):
    """L3 discipline: await each tool in tool_calls order so co == io."""
    msgs = []
    for c in calls:
        out = await tools_by_name[c["name"]].ainvoke(c["args"])
        msgs.append(ToolMessage(content=str(out), name=c["name"], tool_call_id=c["id"]))
    return msgs


# ---- live LLM: bind tools, get one turn's emitted tool_calls (lazy import) ----
def make_chat(provider, model, base_url, api_key):
    if provider == "anthropic":
        from langchain_anthropic import ChatAnthropic
        return ChatAnthropic(model=model, api_key=api_key, max_tokens=512, temperature=0.7)
    from langchain_openai import ChatOpenAI  # openai or vllm/ollama (OpenAI-compatible)
    kw = dict(model=model, temperature=0.7, max_tokens=512, api_key=(api_key or "sk-noauth"))
    if base_url:
        kw["base_url"] = base_url
    return ChatOpenAI(**kw)


SYSTEM = ("You operate an ordered, strictly dependent procedure against a shared stateful "
          "system. Issue ALL the required step tool calls now, in the exact order they must "
          "take effect. Each step depends on the previous one having already taken effect.")

TASKS = [
    "Set up the service: step_0 then step_1 then step_2 then step_3 then step_4, in that order.",
    "Run the deploy sequence step_0 through step_4; each must complete before the next begins.",
    "Execute the migration in order: step_0, step_1, step_2, step_3, step_4.",
    "Perform the ordered rollout step_0..step_4; later steps assume earlier effects are live.",
]


async def emit_tool_calls(chat, tools, task):
    bound = chat.bind_tools(tools)
    msg = await bound.ainvoke([("system", SYSTEM), ("human", task)])
    return msg.tool_calls or []


def hand_built_calls(width):
    return [{"name": f"step_{i}", "args": {"note": f"do {i}"}, "id": f"c{i}"} for i in range(width)]


async def one_session(s, args, tools, tools_by_name, baseline_app, sink_path):
    """Get one turn's calls, replay under baseline and L3, score both."""
    if args.dry_run:
        calls = hand_built_calls(args.width)
    else:
        calls = await emit_tool_calls(args._chat, tools, TASKS[s % len(TASKS)])

    io = [int(c["name"].split("_")[1]) for c in calls if c["name"].startswith("step_")]
    if len(io) < 2:
        # not a batch: record how many calls the model emitted so the batch rate is interpretable
        return {"session": s, "batched": False,
                "n_tool_calls": len(calls), "n_step_calls": len(io)}

    # baseline: the real default ToolNode (parallel)
    WORLD.reset()
    if latency_is_real(args):
        open(sink_path, "w").close()
    out = await baseline_app.ainvoke({"messages": [AIMessage(content="", tool_calls=calls)]})
    co_base = list(WORLD.effect_log)
    tmsgs = [m for m in out["messages"] if m.__class__.__name__ == "ToolMessage"]
    msg_order = [int(m.name.split("_")[1]) for m in tmsgs if m.name and m.name.startswith("step_")]

    # L3: sequenced execution on the SAME calls
    WORLD.reset()
    if latency_is_real(args):
        open(sink_path, "w").close()
    await run_sequenced(tools_by_name, calls)
    co_l3 = list(WORLD.effect_log)

    return {
        "session": s,
        "batched": True,
        "io": io,
        "baseline_co": co_base,
        "baseline_a6": a6_witness(io, co_base),
        "baseline_inversions": inversions(co_base),
        "toolmessage_order": msg_order,
        "toolmessage_preserved": msg_order == io,   # the invisible-in-transcript check
        "l3_co": co_l3,
        "l3_a6": a6_witness(io, co_l3),
    }


def latency_is_real(args):
    return args.latency == "real-io"


def parse_args():
    p = argparse.ArgumentParser(description="A6 (tool-effect reordering) in LangGraph ToolNode, live.")
    p.add_argument("--provider", default="openai", choices=["openai", "anthropic", "vllm"])
    p.add_argument("--model", default="gpt-4o-mini")
    p.add_argument("--base-url", default=None)
    p.add_argument("--api-key", default=None)
    p.add_argument("--n", type=int, default=30)
    p.add_argument("--width", type=int, default=5, help="ordered steps per turn (>=2)")
    p.add_argument("--latency", default="modeled", choices=["modeled", "real-io"])
    p.add_argument("--seed", type=int, default=0xC0FFEE)
    p.add_argument("--out", default="./langgraph_a6_out")
    p.add_argument("--dry-run", action="store_true")
    a = p.parse_args()
    if a.width < 2:
        p.error("--width must be >= 2 (A6 is undefined for fewer than two effects)")
    if a.api_key is None and not a.dry_run:
        a.api_key = (os.environ.get("ANTHROPIC_API_KEY") if a.provider == "anthropic"
                     else os.environ.get("OPENAI_API_KEY"))
    return a


async def amain():
    args = parse_args()
    model_safe = args.model.replace("/", "_")
    out_dir = Path(args.out) / model_safe
    out_dir.mkdir(parents=True, exist_ok=True)
    sink_path = str(out_dir / "_sink.tmp")

    tools = make_tools(args.width, args.latency, sink_path)
    tools_by_name = {t.name: t for t in tools}
    baseline_app = build_baseline_graph(tools)

    if not args.dry_run:
        args._chat = make_chat(args.provider, args.model, args.base_url, args.api_key)

    batch = 0          # turns with >=2 ordered calls
    base_a6 = 0
    l3_a6 = 0
    inv_total = 0
    msg_preserved = 0
    skipped = 0
    skip_calls = []    # n_step_calls for non-batched turns (to explain the batch rate)
    errors = 0

    mseed = args.seed ^ (hash(model_safe) & 0xFFFFFFFF)
    for s in range(args.n):
        if not args.dry_run:
            print(f"\r  running session {s + 1}/{args.n} ...", end="", flush=True)
        if args.latency == "modeled":
            # FRESH heterogeneous latency each turn (and per model) so the reorder
            # reflects real per-turn latency variation, not one frozen profile.
            rs = random.Random(mseed ^ (s * 0x9E3779B1))
            _DELAYS.clear()
            _DELAYS.update({i: round(rs.uniform(0.01, 0.20), 3) for i in range(args.width)})
        try:
            r = await one_session(s, args, tools, tools_by_name, baseline_app, sink_path)
        except Exception as e:
            print(f"\n  session {s}: error {e}; skipping")
            errors += 1
            continue
        with open(out_dir / f"sess-{s:04}.jsonl", "w") as fh:
            fh.write(json.dumps(r) + "\n")
        if not r["batched"]:
            skipped += 1
            skip_calls.append(r["n_step_calls"])
            continue
        batch += 1
        base_a6 += 1 if r["baseline_a6"] else 0
        l3_a6 += 1 if r["l3_a6"] else 0
        inv_total += r["baseline_inversions"]
        msg_preserved += 1 if r["toolmessage_preserved"] else 0

    if not args.dry_run:
        print()
    try:
        os.remove(sink_path)
    except OSError:
        pass

    rate = (base_a6 / batch) if batch else 0.0
    l3_rate = (l3_a6 / batch) if batch else 0.0
    mean_inv = (inv_total / batch) if batch else 0.0
    max_inv = args.width * (args.width - 1) // 2

    print()
    print("=== A6 (tool-effect reordering) in LangGraph ToolNode -- live ===")
    print(f"provider={args.provider}  model={args.model}  sessions={args.n}  width={args.width}  "
          f"latency={args.latency}  dry_run={args.dry_run}")
    completed = batch + skipped
    batch_rate = (batch / completed) if completed else 0.0
    print(f"BATCH RATE (model behavior): emitted >=2 ordered calls in {batch}/{completed} turns "
          f"({batch_rate*100:.0f}%)" + (f"   [{errors} API errors excluded]" if errors else ""))
    if skipped:
        from collections import Counter
        dist = dict(sorted(Counter(skip_calls).items()))
        print(f"  non-batched turns by # step-calls emitted: {dist}  "
              f"(0/1 => model sequenced or declined; this is itself a finding)")
    if batch:
        print(f"baseline (default ToolNode)   A6 = {base_a6}/{batch} ({rate*100:.1f}%)   "
              f"mean-inversions = {mean_inv:.2f}/{max_inv}")
        print(f"L3 (sequenced ToolNode)       A6 = {l3_a6}/{batch} ({l3_rate*100:.1f}%)")
        print(f"ToolMessage order preserved (anomaly invisible in transcript): "
              f"{msg_preserved}/{batch}")
        print()
        if rate > 0:
            print("VERDICT: the real signal here is the BATCH RATE above (model behavior, varies by model).")
            print(f"         Once a model batches, the default ToolNode reordered effects in {rate*100:.0f}% of")
            print(f"         those turns and the sequenced ToolNode prevented every one, invisibly to the")
            print(f"         transcript ({msg_preserved}/{batch}). Lead with the STRUCTURAL defect + #861; the A6")
            print("         rate is an illustration of the latency profile, NOT a prevalence or per-model result.")
        else:
            print("VERDICT: no reorder under this profile (uniform/low-variance latency, or the model")
            print("         sequenced its own calls). The structural defect still holds; the rate does not.")
    else:
        print("no batched turns: the model issued <2 ordered tool calls per turn. That is itself a")
        print("finding (this model sequences dependent calls), but yields no A6 to measure here.")
    print(f"\ntraces under: {out_dir}")


if __name__ == "__main__":
    asyncio.run(amain())