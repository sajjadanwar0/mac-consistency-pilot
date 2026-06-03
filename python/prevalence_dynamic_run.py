#!/usr/bin/env python3
"""
prevalence_dynamic_run.py  (self-contained)

DYNAMIC cross-agent A_1 prevalence: run each topology with LIVE LLM agents and
count how often cross-agent A_1 actually fires. Dynamic companion to
prevalence_static.py's structural upper bound (k of N topologies SUSCEPTIBLE)
and the MAST 0/600 dataset lower bound.

This file is SELF-CONTAINED: it inlines the superstep layering, the A_1
detector (the verified cross-agent predicate, superstep form), the
Clopper-Pearson interval, the op-record type, and a minimal model client, so it
does not import prevalence_harness (whose local copy may predate
compute_layers). The inlined a1_firings is identical to
prevalence_harness.a1_firings and to lib_l2_safety.rs::a1_witness evaluated at
the superstep-commit point.

EXECUTION MODEL
  BSP / Pregel supersteps -- the model LangGraph and CrewAI parallel steps use:
  every node in one topological layer reads the state committed at layer start,
  writes are merged at the layer boundary. Each node is a live LLM call
  (read shared cells -> generate -> write). State is pre-populated with every
  cell = "NULL" so first-layer reads are recorded (an unread cell cannot
  witness A_1).

USAGE
  pip install openai anthropic
  export OPENAI_API_KEY=...
  python prevalence_dynamic_run.py --provider openai    --model gpt-4o-mini --n 20
  export ANTHROPIC_API_KEY=...
  python prevalence_dynamic_run.py --provider anthropic --model claude-haiku-4-5 --n 20
  python prevalence_dynamic_run.py --provider vllm --model <oss> --base-url http://localhost:8000/v1 --n 20
"""
from __future__ import annotations
import argparse
import json
import math
from collections import deque
from dataclasses import dataclass, field, asdict
from pathlib import Path

START = "__start__"
END = "__end__"


# =====================================================================
# Inlined record type + detector + stats (mirror prevalence_harness)
# =====================================================================
@dataclass
class OpRecord:
    agent_id: str
    op_index: int
    read_set: list
    read_values: dict
    read_time: int
    write_set: list
    write_values: dict
    write_time: int
    superstep: int
    scenario: str = ""
    model: str = ""


def compute_layers(edges, start=START, end=END):
    """Longest-path depth from start; nodes with equal depth share a superstep.
    Sentinels dropped, layers re-based to 0."""
    succ, nodes, indeg = {}, set(), {}
    for (a, b) in edges:
        succ.setdefault(a, []).append(b)
        nodes.add(a); nodes.add(b)
        indeg[b] = indeg.get(b, 0) + 1
        indeg.setdefault(a, indeg.get(a, 0))
    depth = {n: 0 for n in nodes}
    ind = dict(indeg)
    q = deque([n for n in nodes if indeg.get(n, 0) == 0])
    while q:
        n = q.popleft()
        for m in succ.get(n, []):
            depth[m] = max(depth[m], depth[n] + 1)
            ind[m] -= 1
            if ind[m] == 0:
                q.append(m)
    real = {n: depth[n] for n in nodes if n not in (start, end)}
    if not real:
        return {}
    base = min(real.values())
    return {n: d - base for n, d in real.items()}


def a1_firings(records):
    """Cross-agent A_1 under the superstep model: op O (superstep k, agent A)
    reading cell c=v fires iff some op O' in superstep k, by a DIFFERENT agent,
    writes c=v' with v' != v. Identical to prevalence_harness.a1_firings."""
    by_ss = {}
    for r in records:
        by_ss.setdefault(r.superstep, []).append(r)
    firings = []
    for ss, ops in by_ss.items():
        for r in ops:
            for c in r.read_set:
                v = r.read_values.get(c, "")
                hit = False
                for w in ops:
                    if w.agent_id == r.agent_id:
                        continue
                    if c in w.write_set and w.write_values.get(c, "") != v:
                        firings.append({"superstep": ss, "agent": r.agent_id, "cell": c,
                                        "read_value": v, "superseding_value": w.write_values.get(c, ""),
                                        "by_agent": w.agent_id})
                        hit = True
                        break
                if hit:
                    break
    return firings


def clopper_pearson(k, n, alpha=0.05):
    if n == 0:
        return (0.0, 1.0)
    try:
        from scipy.stats import beta
        lo = 0.0 if k == 0 else beta.ppf(alpha / 2, k, n - k + 1)
        hi = 1.0 if k == n else beta.ppf(1 - alpha / 2, k + 1, n - k)
        return (float(lo), float(hi))
    except Exception:
        p = k / n
        se = math.sqrt(p * (1 - p) / n) if 0 < p < 1 else 0.0
        return (max(0.0, p - 1.96 * se), min(1.0, p + 1.96 * se))


# =====================================================================
# Minimal model client (openai / vllm / anthropic)
# =====================================================================
class ModelClient:
    def __init__(self, provider, model, base_url=None):
        self.provider = provider
        self.model = model
        if provider in ("openai", "vllm"):
            from openai import OpenAI
            if base_url:
                self.client = OpenAI(base_url=base_url, api_key="EMPTY")
            else:
                self.client = OpenAI()
        elif provider == "anthropic":
            import anthropic
            self.client = anthropic.Anthropic()
        else:
            raise ValueError(f"unknown provider {provider}")

    def complete(self, system, user, max_tokens=32):
        if self.provider in ("openai", "vllm"):
            r = self.client.chat.completions.create(
                model=self.model, max_tokens=max_tokens,
                messages=[{"role": "system", "content": system},
                          {"role": "user", "content": user}])
            return (r.choices[0].message.content or "").strip()
        else:
            r = self.client.messages.create(
                model=self.model, max_tokens=max_tokens, system=system,
                messages=[{"role": "user", "content": user}])
            return (r.content[0].text if r.content else "").strip()


# =====================================================================
# Topologies (same structural specs as prevalence_static.py)
# expect: "fire" (susceptible) | "silent" (safe / negative control)
# =====================================================================
TOPOLOGIES: dict = {
    "sequential_pipeline": {
        "edges": [(START, "plan"), ("plan", "exec"), ("exec", "summarise"), ("summarise", END)],
        "nodes": {"plan": (["task"], ["plan"]), "exec": (["plan"], ["result"]),
                  "summarise": (["result"], ["summary"])},
        "expect": "silent"},
    "racy_shared_cell": {
        "edges": [(START, "producer"), (START, "consumer"), ("producer", END), ("consumer", END)],
        "nodes": {"producer": (["task"], ["plan"]), "consumer": (["plan"], ["answer"])},
        "expect": "fire"},
    "supervisor_fanout_disjoint": {
        "edges": [(START, "supervisor"), ("supervisor", "worker_a"), ("supervisor", "worker_b"),
                  ("worker_a", "reducer"), ("worker_b", "reducer"), ("reducer", END)],
        "nodes": {"supervisor": (["task"], ["plan"]), "worker_a": (["plan"], ["out_a"]),
                  "worker_b": (["plan"], ["out_b"]), "reducer": (["out_a", "out_b"], ["summary"])},
        "expect": "silent"},
    "map_reduce_reducer_channel": {
        "edges": [(START, "mapper"), ("mapper", "w0"), ("mapper", "w1"), ("mapper", "w2"),
                  ("w0", "aggregate"), ("w1", "aggregate"), ("w2", "aggregate"), ("aggregate", END)],
        "nodes": {"mapper": (["items"], ["items"]), "w0": (["items"], ["results"]),
                  "w1": (["items"], ["results"]), "w2": (["items"], ["results"]),
                  "aggregate": (["results"], ["final"])},
        "expect": "silent"},
    "blackboard_multiwriter": {
        "edges": [(START, "ks1"), (START, "ks2"), (START, "ks3"),
                  ("ks1", "control"), ("ks2", "control"), ("ks3", "control"), ("control", END)],
        "nodes": {"ks1": (["blackboard"], ["blackboard"]), "ks2": (["blackboard"], ["blackboard"]),
                  "ks3": (["blackboard"], ["blackboard"]), "control": (["blackboard"], ["decision"])},
        "expect": "fire"},
    "collaboration_shared_messages": {
        "edges": [(START, "agent_x"), (START, "agent_y"),
                  ("agent_x", "route"), ("agent_y", "route"), ("route", END)],
        "nodes": {"agent_x": (["messages"], ["messages"]), "agent_y": (["messages"], ["messages"]),
                  "route": (["messages"], ["next"])},
        "expect": "fire"},
    "hierarchical_teams": {
        "edges": [(START, "top"), ("top", "team1_lead"), ("top", "team2_lead"),
                  ("team1_lead", "join"), ("team2_lead", "join"), ("join", END)],
        "nodes": {"top": (["task"], ["task"]),
                  "team1_lead": (["task", "shared_scratch"], ["team1_out", "shared_scratch"]),
                  "team2_lead": (["task", "shared_scratch"], ["team2_out", "shared_scratch"]),
                  "join": (["team1_out", "team2_out"], ["final"])},
        "expect": "fire"},
    "competing_agents_consensus": {
        "edges": [(START, "proposer_a"), (START, "proposer_b"),
                  ("proposer_a", "decide"), ("proposer_b", "decide"), ("decide", END)],
        "nodes": {"proposer_a": (["proposals"], ["proposals"]),
                  "proposer_b": (["proposals"], ["proposals"]), "decide": (["proposals"], ["decision"])},
        "expect": "fire"},
    "map_reduce_no_reducer_accumulator": {
        "edges": [(START, "split"), ("split", "m0"), ("split", "m1"), ("split", "m2"),
                  ("m0", "done"), ("m1", "done"), ("m2", "done"), ("done", END)],
        "nodes": {"split": (["items"], ["items"]),
                  "m0": (["accumulator"], ["accumulator"]), "m1": (["accumulator"], ["accumulator"]),
                  "m2": (["accumulator"], ["accumulator"]), "done": (["accumulator"], ["final"])},
        "expect": "fire"},
}


def all_cells(spec):
    cells = set()
    for (reads, writes) in spec["nodes"].values():
        cells.update(reads); cells.update(writes)
    return cells


def run_once(client, name, spec, jsonl_path=None):
    """Execute one topology once with live LLM nodes under the BSP superstep
    model; return the recorded OpRecords."""
    layers = compute_layers(spec["edges"])
    by_layer = {}
    for n, ss in layers.items():
        by_layer.setdefault(ss, []).append(n)
    state = {c: "NULL" for c in all_cells(spec)}
    records = []
    op = 0
    for ss in sorted(by_layer):
        updates = {}
        for n in by_layer[ss]:
            reads, writes = spec["nodes"][n]
            read_state = {c: state.get(c, "NULL") for c in reads}
            if reads:
                user = (f"You are agent '{n}' in a multi-agent workflow. "
                        f"Current shared state: {json.dumps(read_state)}. "
                        f"Produce a concise updated value (at most 8 words). Output only the value.")
            else:
                user = (f"You are agent '{n}'. Produce a concise value "
                        f"(at most 8 words). Output only the value.")
            try:
                out = client.complete("Multi-agent workflow node. Reply with only a short value.",
                                      user, max_tokens=32)
            except Exception:
                out = f"ERR_{n}"
            op += 1
            records.append(OpRecord(
                agent_id=n, op_index=op,
                read_set=sorted(reads), read_values={c: str(v)[:500] for c, v in read_state.items()},
                read_time=2 * ss,
                write_set=sorted(writes), write_values={c: str(out)[:500] for c in writes},
                write_time=2 * ss + 1, superstep=ss, scenario=name, model=client.model))
            for c in writes:
                updates[c] = out
        state.update(updates)
    if jsonl_path:
        with open(jsonl_path, "w") as fh:
            for r in records:
                fh.write(json.dumps(asdict(r), separators=(",", ":")) + "\n")
    return records


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--provider", required=True, help="openai | anthropic | vllm")
    ap.add_argument("--model", required=True)
    ap.add_argument("--base-url", default=None)
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--out", default="./dynamic_oprecords")
    args = ap.parse_args()

    client = ModelClient(args.provider, args.model, base_url=args.base_url)
    outdir = Path(args.out); outdir.mkdir(parents=True, exist_ok=True)
    msafe = args.model.replace("/", "_")

    print(f"{'topology':36}{'expect':9}{'A1 fired':>10}{'rate':>8}   95% CI")
    print("-" * 86)
    summary = {}
    controls_ok = True
    for name, spec in TOPOLOGIES.items():
        fired = 0
        for t in range(args.n):
            recs = run_once(client, name, spec, outdir / f"{name}__{msafe}__{t}.jsonl")
            if a1_firings(recs):
                fired += 1
        lo, hi = clopper_pearson(fired, args.n)
        rate = fired / args.n if args.n else 0.0
        summary[name] = {"fired": fired, "n": args.n, "rate": rate, "ci": [lo, hi],
                         "expect": spec["expect"]}
        if name == "racy_shared_cell" and fired == 0:
            controls_ok = False
        if spec["expect"] == "silent" and fired > 0:
            controls_ok = False
        print(f"{name:36}{spec['expect']:9}{fired:>7}/{args.n:<2}{rate:>8.2f}   [{lo:.2f}, {hi:.2f}]")

    susc = [v["rate"] for k, v in summary.items() if v["expect"] == "fire" and k != "racy_shared_cell"]
    print("-" * 86)
    print(f"Controls: {'PASS' if controls_ok else 'FAIL'} "
          f"(racy fires; sequential/disjoint/reducer silent)")
    if susc:
        print(f"Dynamic A_1 rate across susceptible canonical topologies: "
              f"{min(susc):.2f}-{max(susc):.2f} (model {args.model})")
    out_summary = outdir / f"summary__{msafe}.json"
    json.dump({"model": args.model, "provider": args.provider,
               "controls_ok": controls_ok, "topologies": summary},
              open(out_summary, "w"), indent=2)
    print(f"wrote {out_summary}")


if __name__ == "__main__":
    main()