#!/usr/bin/env python3
"""
langgraph_a6_experiment.py  (natural-prompt edition)

Measures A6 (tool-effect reordering, co != io) on the REAL LangGraph ToolNode
under a real LLM, using a NATURAL prompt: the model is given an order-dependent
pipeline of tools (each tool's docstring states its dependency) and asked only to
fulfill the request. Whether it batches the calls into one turn -- the trigger
for ToolNode's parallel execution -- is therefore the MODEL'S OWN CHOICE, not an
instruction. This is the defensible way to report a batching rate.

io = the order the MODEL emitted the tool calls (its intended order).
co = the order the side effects actually committed (completion order).
A6 = co != io.  L3 = await tools in emitted order (-> co == io).

Records per-tool timing; runs a uniform-latency control (equal latency -> no
reorder, proving it is latency-driven); prints per-model + pooled aggregates with
a rule-of-three CI. Baseline is LangGraph's DEFAULT ToolNode (asyncio.gather),
corroborated by langchain-ai/langgraphjs#861. Tool latency is MODELED to stand
in for real stateful-tool latency heterogeneity; the structural defect and the
transcript-invisibility are the robust findings, the rate is their consequence.

--prompt natural   (default) gives the task only; the model chooses to batch
--prompt instructed          tells the model to call all tools at once (for A/B)

Usage:
  python3 langgraph_a6_experiment.py --provider openai    --model gpt-4o-mini      --n 30 --out langgraph_a6_out
  python3 langgraph_a6_experiment.py --provider anthropic --model claude-haiku-4-5 --n 30 --out langgraph_a6_out
  python3 langgraph_a6_experiment.py --provider vllm --base-url http://localhost:11434/v1 --model llama3.2:latest --n 30 --out langgraph_a6_out
  python3 langgraph_a6_experiment.py --dry-run --n 8     # no LLM; hand-built batched call, tests mechanics
"""
import argparse, asyncio, json, os, random, time
from pathlib import Path
from typing import Annotated, TypedDict
from langchain_core.messages import AIMessage, ToolMessage
from langchain_core.tools import tool
from langgraph.prebuilt import ToolNode
from langgraph.graph import StateGraph, START, END
from langgraph.graph.message import add_messages

# --- an order-dependent pipeline; each docstring states the hard dependency ---
PIPELINE = ["create_database", "run_migrations", "seed_reference_data", "build_search_index", "enable_live_traffic"]
PURPOSE = {
    "create_database":     "Create the empty production database instance. Must run first.",
    "run_migrations":      "Apply schema migrations. Requires the database to already exist.",
    "seed_reference_data": "Load reference data. Requires migrations to have been applied.",
    "build_search_index":  "Build the search index. Requires reference data to be present.",
    "enable_live_traffic": "Route live traffic to the database. Requires the search index to be built.",
}
SCENARIOS = ["analytics", "billing", "checkout", "messaging", "recommendations", "inventory"]

SINK = []          # (tool_name, dispatch_ms, complete_ms) in COMMIT order
DELAYS = {}        # tool_name -> modeled latency (s)
T0 = 0.0

def make_tool(name):
    async def _f(target: str = "production") -> str:
        disp = (time.perf_counter() - T0) * 1000.0
        await asyncio.sleep(DELAYS[name])          # MODELED latency (swap for real I/O to de-model)
        SINK.append((name, disp, (time.perf_counter() - T0) * 1000.0))   # effect commits here
        return f"{name}: completed for {target}"
    _f.__name__ = name
    _f.__doc__ = PURPOSE[name]
    return tool(_f)

def build_graph():
    tools = [make_tool(n) for n in PIPELINE]
    class S(TypedDict):
        messages: Annotated[list, add_messages]
    g = StateGraph(S)
    g.add_node("tools", ToolNode(tools))
    g.add_edge(START, "tools"); g.add_edge("tools", END)
    return g.compile(), {n: t for n, t in zip(PIPELINE, tools)}, tools

def a6_witness(io, co):
    return len(io) >= 2 and len(io) == len(co) and io != co
def inversions(co):
    return sum(1 for i in range(len(co)) for j in range(i+1, len(co)) if co[i] > co[j])

def het_delays(rng): return {n: round(rng.uniform(0.01, 0.20), 3) for n in PIPELINE}
def uniform_delays(d=0.05): return {n: d for n in PIPELINE}

async def baseline_run(app, calls):
    """default ToolNode (parallel) on the model's emitted calls."""
    global SINK, T0
    SINK = []; T0 = time.perf_counter()
    out = await app.ainvoke({"messages": [AIMessage(content="", tool_calls=calls)]})
    committed = list(SINK)
    tmsgs = [m for m in out["messages"] if isinstance(m, ToolMessage)]
    return committed, [m.name for m in tmsgs]

async def l3_run(toolmap, calls):
    """L3: await tools in emitted order -> effects commit in emitted order."""
    global SINK, T0
    SINK = []; T0 = time.perf_counter()
    for c in calls:
        await toolmap[c["name"]].ainvoke(c["args"])
    return [s[0] for s in SINK]

def emitted_calls_canonical():
    return [{"name": n, "args": {"target": "production"}, "id": f"c{i}"} for i, n in enumerate(PIPELINE)]

async def model_calls(provider, model, base_url, api_key, scenario, prompt_mode):
    tools = [make_tool(n) for n in PIPELINE]
    if provider == "anthropic":
        from langchain_anthropic import ChatAnthropic
        llm = ChatAnthropic(model=model, api_key=api_key, max_tokens=1024, temperature=0.7)
    else:
        from langchain_openai import ChatOpenAI
        kw = dict(model=model, temperature=0.7)
        if base_url: kw["base_url"] = base_url
        kw["api_key"] = api_key or "not-needed"
        llm = ChatOpenAI(**kw)
    if prompt_mode == "instructed":
        sys = ("You are an infrastructure automation agent. Call ALL of the following tools NOW, "
               "in a single batch, in this exact order: " + ", ".join(PIPELINE) + ".")
    else:  # natural
        sys = ("You are an infrastructure automation agent. Use the available tools to fulfill the "
               "user's request. The tools' descriptions explain what each does.")
    user = f"Set up the production database for our new {scenario} service so it is ready to serve live traffic."
    msg = await llm.bind_tools(tools).ainvoke([("system", sys), ("user", user)])
    return getattr(msg, "tool_calls", []) or []

async def one_session(app, toolmap, provider, model, base_url, api_key, scenario, prompt_mode, rng, dry_run):
    if dry_run:
        calls = emitted_calls_canonical()
    else:
        raw = await model_calls(provider, model, base_url, api_key, scenario, prompt_mode)
        seen = set(); calls = []
        for c in raw:                                  # keep known pipeline tools, model's order, dedup
            nm = c.get("name", "")
            if nm in PURPOSE and nm not in seen:
                seen.add(nm); calls.append({"name": nm, "args": c.get("args", {}) or {"target": "production"}, "id": c.get("id", nm)})
    if len(calls) < 2:
        return {"batched": False, "n_tool_calls": len(calls),
                "emitted": [c["name"] for c in calls]}

    emitted = [c["name"] for c in calls]
    pos = {nm: i for i, nm in enumerate(emitted)}
    io = list(range(len(emitted)))

    global DELAYS
    DELAYS = het_delays(rng)
    committed, msg_names = await baseline_run(app, calls)
    base_co = [pos[nm] for nm, _, _ in committed if nm in pos]
    msg_order = [pos[nm] for nm in msg_names if nm in pos]
    l3_names = await l3_run(toolmap, calls)
    l3_co = [pos[nm] for nm in l3_names if nm in pos]
    return {
        "batched": True, "emitted": emitted, "io": io,
        "baseline_co": base_co, "baseline_a6": a6_witness(io, base_co), "baseline_inversions": inversions(base_co),
        "toolmessage_order": msg_order, "toolmessage_preserved": msg_order == io,
        "l3_co": l3_co, "l3_a6": a6_witness(io, l3_co),
        "delays_ms": {nm: round(DELAYS[nm]*1000) for nm in emitted},
        "effect_timing": [{"tool": nm, "dispatch_ms": round(d,1), "complete_ms": round(c,1)} for nm, d, c in committed],
    }

async def uniform_control(app, trials=5):
    global DELAYS
    io = list(range(len(PIPELINE))); leaks = 0
    for _ in range(trials):
        DELAYS = uniform_delays()
        committed, _ = await baseline_run(app, emitted_calls_canonical())
        pos = {n: i for i, n in enumerate(PIPELINE)}
        co = [pos[nm] for nm, _, _ in committed]
        if a6_witness(io, co): leaks += 1
    return trials, leaks

async def _run(a, api_key):
    app, toolmap, _ = build_graph()
    outdir = Path(a.out)/a.model.replace("/", "_"); outdir.mkdir(parents=True, exist_ok=True)
    ctrl_trials, ctrl_leaks = await uniform_control(app)

    bat=base=l3=pres=invs=nonbat=0
    for s in range(a.n):
        if not a.dry_run: print(f"\r  session {s+1}/{a.n} ...", end="", flush=True)
        rec = await one_session(app, toolmap, a.provider, a.model, a.base_url, api_key,
                                SCENARIOS[s % len(SCENARIOS)], a.prompt,
                                random.Random(a.seed ^ (s*2654435761)), a.dry_run)
        rec["session"] = s; rec["prompt_mode"] = a.prompt
        (outdir/f"sess-{s:04}.jsonl").write_text(json.dumps(rec))
        if rec["batched"]:
            bat += 1; invs += rec["baseline_inversions"]; base += rec["baseline_a6"]
            l3 += rec["l3_a6"]; pres += rec["toolmessage_preserved"]
        else:
            nonbat += 1
    if not a.dry_run: print()

    print("\n=== LangGraph ToolNode A6 experiment (prompt=%s) ===" % a.prompt)
    print(f"provider={a.provider} model={a.model} sessions={a.n} dry_run={a.dry_run}")
    print(f"uniform-latency CONTROL: A6 = {ctrl_leaks}/{ctrl_trials} (equal latency preserves order -> latency-driven)")
    print(f"batching: model CHOSE to batch >=2 order-dependent calls in {bat}/{a.n} turns "
          f"({bat/a.n*100:.0f}%); {nonbat} turns were single-call (A6 not applicable)")
    if bat:
        ci = f"[0, {3/bat*100:.1f}%]" if l3 == 0 else "L3 LEAKED"
        print(f"baseline (default ToolNode)  A6 = {base}/{bat} ({base/bat*100:.1f}% of batched)  "
              f"mean-inversions = {invs/bat:.2f}/{len(PIPELINE)*(len(PIPELINE)-1)//2}")
        print(f"L3 (sequenced)               A6 = {l3}/{bat}   rule-of-three 95% CI {ci}")
        print(f"transcript-invisibility: ToolMessage order matched intended in {pres}/{bat} "
              f"({pres/bat*100:.0f}%)")
    print(f"\ntraces under: {outdir}")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--provider", default="openai")
    ap.add_argument("--model", default="gpt-4o-mini")
    ap.add_argument("--base-url", default=None)
    ap.add_argument("--n", type=int, default=30)
    ap.add_argument("--out", default="langgraph_a6_out")
    ap.add_argument("--seed", type=int, default=0xA6)
    ap.add_argument("--prompt", choices=["natural", "instructed"], default="natural")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    api_key = ""
    if not a.dry_run:
        api_key = (os.environ.get("ANTHROPIC_API_KEY", "") if a.provider == "anthropic"
                   else os.environ.get("OPENAI_API_KEY", ""))
    asyncio.run(_run(a, api_key))

if __name__ == "__main__":
    main()