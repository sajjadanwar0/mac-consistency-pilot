#!/usr/bin/env python3
"""
langgraph_a6_experiment.py

Measures A6 (tool-effect reordering, co != io) on the REAL LangGraph ToolNode
under a real LLM that emits order-dependent tool calls, and shows the L3
sequencing discipline prevents it. Improvement over the first harness:

  * records per-tool dispatch/complete timing in every trace (re-derivable;
    proves the reorder is latency-driven, not constructed);
  * runs an automatic UNIFORM-LATENCY CONTROL (equal latencies -> effects
    preserved, A6=0) -- the key artifact that rebuts "you just scrambled it";
  * computes per-model + pooled aggregates with a rule-of-three CI in-harness;
  * makes the batched/non-batched denominator explicit (A6 is only defined when
    the model batches >=2 calls into one turn; the batching rate is itself a
    per-model finding).

Honesty notes baked into the framing this prints:
  - The baseline is LangGraph's DEFAULT ToolNode (asyncio.gather), not a harness
    contrivance; corroborated by langchain-ai/langgraphjs#861.
  - Tool latency is MODELED (seeded heterogeneous draws) to stand in for the
    real latency heterogeneity of stateful tools (#861: move/click/type, or a
    cache-read vs an external-API-write). The uniform control proves the reorder
    is a function of latency *differences*, a real property of real tools. The
    STRUCTURAL claim -- ToolNode commits effects in completion order, invisibly
    in the transcript -- is the robust finding; the rate is its consequence.
    To remove all modeling, swap the tool body (see make_tool) for a real I/O op.

Usage:
  python3 langgraph_a6_experiment.py --provider openai    --model gpt-4o-mini      --n 30 --width 5 --out langgraph_a6_out
  python3 langgraph_a6_experiment.py --provider anthropic --model claude-haiku-4-5 --n 30 --width 5 --out langgraph_a6_out
  python3 langgraph_a6_experiment.py --provider vllm --base-url http://localhost:11434/v1 --model llama3.2:latest --n 30 --out langgraph_a6_out
  python3 langgraph_a6_experiment.py --dry-run --n 10      # no LLM; hand-built ordered calls, tests mechanics
"""
import argparse, asyncio, json, os, random, time
from pathlib import Path
from langchain_core.messages import AIMessage, ToolMessage
from langchain_core.tools import tool
from langgraph.prebuilt import ToolNode
from langgraph.graph import StateGraph, START, END
from langgraph.graph.message import add_messages
from typing import Annotated, TypedDict

# ---- shared side-effect sink + per-session latency table ----
SINK = []            # list of (step_idx, dispatch_ms, complete_ms) in COMMIT order
DELAYS = {}          # per-step modeled latency (seconds)
T0 = 0.0

def make_tool(i: int):
    async def _f(note: str = "") -> str:
        disp = (time.perf_counter() - T0) * 1000.0
        # --- modeled tool latency (swap this line for a real I/O op to de-model) ---
        await asyncio.sleep(DELAYS[i])
        SINK.append((i, disp, (time.perf_counter() - T0) * 1000.0))   # effect commits here
        return f"step {i} committed"
    _f.__name__ = f"step_{i}"
    _f.__doc__ = f"Perform ordered step {i} against the shared stateful system; must run after step {i-1}."
    return tool(_f)

def build_graph(width):
    tools = [make_tool(i) for i in range(width)]
    class S(TypedDict):
        messages: Annotated[list, add_messages]
    g = StateGraph(S)
    g.add_node("tools", ToolNode(tools))
    g.add_edge(START, "tools"); g.add_edge("tools", END)
    return g.compile(), {f"step_{i}": tools[i] for i in range(width)}

# order-dependent tasks; the model is asked to emit the steps in strict order
TASKS = [
    "Provision the database, then migrate the schema, then seed reference data, then enable backups, then verify health.",
    "Create the customer, then charge the card, then generate the invoice, then email the receipt, then close the ticket.",
    "Allocate the VM, then attach the disk, then install the runtime, then register with the load balancer, then run a smoke test.",
    "Open the incident, then page the on-call, then post a status update, then apply the mitigation, then resolve.",
]

def a6_witness(io, co):  # mirrors l3_sequencer::a6_witness
    return len(io) >= 2 and len(io) == len(co) and io != co
def inversions(co):
    return sum(1 for i in range(len(co)) for j in range(i+1, len(co)) if co[i] > co[j])

def het_delays(width, rng):
    return {i: round(rng.uniform(0.01, 0.20), 3) for i in range(width)}
def uniform_delays(width, d=0.05):
    return {i: d for i in range(width)}

async def run_calls_baseline(app, calls):
    """default ToolNode (gather) on the model's tool_calls; returns (effect_order, msg_order)."""
    global SINK, T0
    SINK = []; T0 = time.perf_counter()
    out = await app.ainvoke({"messages": [AIMessage(content="", tool_calls=calls)]})
    co = [s[0] for s in SINK]
    timing = list(SINK)
    tmsgs = [m for m in out["messages"] if isinstance(m, ToolMessage)]
    msg_order = [int(m.name.split("_")[1]) for m in tmsgs]
    return co, msg_order, timing

async def run_calls_l3(toolmap, calls):
    """L3 discipline: await tools in tool_calls order; returns effect_order (==io)."""
    global SINK, T0
    SINK = []; T0 = time.perf_counter()
    for c in calls:
        await toolmap[c["name"]].ainvoke(c["args"])
    return [s[0] for s in SINK]

def ordered_calls(width):
    return [{"name": f"step_{i}", "args": {"note": f"do {i}"}, "id": f"c{i}"} for i in range(width)]

async def get_model_calls(provider, model, base_url, api_key, task, width):
    """Ask a real LLM to emit the ordered tool calls; return the tool_calls list (model's order)."""
    tools = [make_tool(i) for i in range(width)]
    if provider == "anthropic":
        from langchain_anthropic import ChatAnthropic
        llm = ChatAnthropic(model=model, api_key=api_key, max_tokens=1024, temperature=0.7)
    else:  # openai or vllm (OpenAI-compatible)
        from langchain_openai import ChatOpenAI
        kw = dict(model=model, temperature=0.7)
        if base_url: kw["base_url"] = base_url
        if api_key:  kw["api_key"] = api_key
        elif provider == "vllm": kw["api_key"] = "not-needed"
        llm = ChatOpenAI(**kw)
    bound = llm.bind_tools(tools)
    sys = ("You control a stateful system through tools that MUST run in the order given. "
           f"Call all {width} steps now, in the exact order step_0, step_1, ..., step_{width-1}.")
    msg = await bound.ainvoke([("system", sys), ("user", task)])
    return getattr(msg, "tool_calls", []) or []

async def one_session(app, toolmap, width, provider, model, base_url, api_key, task, rng, dry_run):
    if dry_run:
        calls = ordered_calls(width)
    else:
        raw = await get_model_calls(provider, model, base_url, api_key, task, width)
        # keep only known step_ tools, in the model's emitted order, dedup by name
        seen = set(); calls = []
        for c in raw:
            nm = c.get("name", "")
            if nm.startswith("step_") and nm not in seen:
                seen.add(nm); calls.append({"name": nm, "args": c.get("args", {}) or {}, "id": c.get("id", nm)})
    if len(calls) < 2:
        return {"batched": False, "n_tool_calls": len(calls)}
    io = [int(c["name"].split("_")[1]) for c in calls]

    global DELAYS
    DELAYS = het_delays(width, rng)
    base_co, msg_order, timing = await run_calls_baseline(app, calls)
    l3_co = await run_calls_l3(toolmap, calls)
    return {
        "batched": True, "io": io,
        "baseline_co": base_co, "baseline_a6": a6_witness(io, base_co), "baseline_inversions": inversions(base_co),
        "toolmessage_order": msg_order, "toolmessage_preserved": msg_order == io,
        "l3_co": l3_co, "l3_a6": a6_witness(io, l3_co),
        "delays_ms": {i: round(DELAYS[i]*1000) for i in range(width)},
        "effect_timing": [{"step": s[0], "dispatch_ms": round(s[1],1), "complete_ms": round(s[2],1)} for s in timing],
    }

async def uniform_control(app, width, trials=5):
    global DELAYS
    io = list(range(width)); leaks = 0
    for _ in range(trials):
        DELAYS = uniform_delays(width)
        co, _, _ = await run_calls_baseline(app, ordered_calls(width))
        if a6_witness(io, co): leaks += 1
    return trials, leaks

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--provider", default="openai")
    ap.add_argument("--model", default="gpt-4o-mini")
    ap.add_argument("--base-url", default=None)
    ap.add_argument("--n", type=int, default=30)
    ap.add_argument("--width", type=int, default=5)
    ap.add_argument("--out", default="langgraph_a6_out")
    ap.add_argument("--seed", type=int, default=0xA6)
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    if a.width < 2: raise SystemExit("--width must be >= 2")
    api_key = ""
    if not a.dry_run:
        api_key = (os.environ.get("ANTHROPIC_API_KEY","") if a.provider=="anthropic"
                   else os.environ.get("OPENAI_API_KEY",""))

    asyncio.run(_run(a, api_key))

async def _run(a, api_key):
    app, toolmap = build_graph(a.width)
    model_safe = a.model.replace("/", "_")
    outdir = Path(a.out)/model_safe; outdir.mkdir(parents=True, exist_ok=True)
    rng = random.Random(a.seed)

    # mechanism control first (no LLM): equal latencies must preserve order
    ctrl_trials, ctrl_leaks = await uniform_control(app, a.width)

    bat=base=l3=pres=0; invs=0; nonbat=0
    for s in range(a.n):
        if not a.dry_run:
            print(f"\r  session {s+1}/{a.n} ...", end="", flush=True)
        task = TASKS[s % len(TASKS)]
        rec = await one_session(app, toolmap, a.width, a.provider, a.model, a.base_url, api_key, task,
                                random.Random(a.seed ^ (s*2654435761)), a.dry_run)
        rec["session"] = s
        (outdir/f"sess-{s:04}.jsonl").write_text(json.dumps(rec))
        if rec["batched"]:
            bat += 1; invs += rec["baseline_inversions"]
            base += rec["baseline_a6"]; l3 += rec["l3_a6"]; pres += rec["toolmessage_preserved"]
        else:
            nonbat += 1
    if not a.dry_run: print()

    print("\n=== LangGraph ToolNode A6 (tool-effect reordering) experiment ===")
    print(f"provider={a.provider} model={a.model} sessions={a.n} width={a.width} dry_run={a.dry_run}")
    print(f"uniform-latency CONTROL: A6 = {ctrl_leaks}/{ctrl_trials}  "
          f"(equal latencies preserve effect order -> reorder is latency-driven, not constructed)")
    print(f"batching: model emitted >=2 tool calls in {bat}/{a.n} turns "
          f"({bat/a.n*100:.0f}%); the other {nonbat} were single-call (A6 not applicable)")
    if bat:
        ci = f"[0, {3/bat*100:.1f}%]" if l3==0 else "L3 LEAKED"
        print(f"baseline (default ToolNode)  A6 = {base}/{bat} ({base/bat*100:.1f}% of batched)  "
              f"mean-inversions = {invs/bat:.2f}/{a.width*(a.width-1)//2}")
        print(f"L3 (sequenced ToolNode)      A6 = {l3}/{bat}  rule-of-three 95% CI {ci}")
        print(f"transcript-invisibility: ToolMessage order matched intended order in {pres}/{bat} "
              f"({pres/bat*100:.0f}%) -- the reorder is invisible in the conversation log")
    print(f"\ntraces with per-tool timing under: {outdir}")

if __name__ == "__main__":
    main()