#!/usr/bin/env python3
"""
analyze_production.py — score op-record sessions with Definition 1 exactly.

WHY THIS FILE WAS REWRITTEN (13 Sep 2026, post-ICECCS round 4 / E2)
--------------------------------------------------------------------
The previous predicate fired when `write_time(j) > read_time(i)` and the
values differed. That is NOT stale-generation. Definition 1 (paper Sec 3.1,
rust-analyser/src/anomalies.rs, the Verus-verified detect_a1) requires the
write to land STRICTLY INSIDE the reader's window:

    read_time(i) < write_time(j) < write_time(i),  agents differ,
    c in read_set(i) ∩ write_set(j),  read_values(i)[c] != write_values(j)[c]

Without the upper bound, any later rewrite of a cell the reader had read
counted as A_1 — including rewrites that landed after the reader had
already committed. On the 600 cookbook sessions (production_traces/) every
op has write_time - read_time == 1, so Definition 1 CANNOT fire; the
previously reported 90/100 on shared_workspace was entirely the missing
conjunct. The same holds for the MAST adapter's op-records (read_time,
write_time stamped as consecutive steps).

The old quantity is still meaningful — a slot one agent read was later
rewritten by another — as the structural PRECONDITION of A_1, so it is kept
under its true name (`later_rewrite`), never as A_1.

Schema: `agent` (rust-analyser/oprecord.rs, instrument.py) or `agent_id`
(production_extractor.py, mast_adapter.py) are both accepted.

USAGE
  python analyze_production.py production_traces --out cookbook_rates.json
"""
from __future__ import annotations
import argparse
import json
import random
import sys
from collections import defaultdict
from pathlib import Path
from statistics import mean

NULL = "NULL"


def load_session(path: Path) -> list[dict]:
    events = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        events.append(json.loads(line))
    return events


def agent_of(e: dict) -> str:
    return e.get("agent", e.get("agent_id", "?"))


def detect_a1(events: list[dict]) -> list[dict]:
    """Definition 1, verbatim. Returns the witnesses (i, j, cell)."""
    out = []
    for i, ri in enumerate(events):
        rt, wt_i, ra = ri.get("read_time", 0), ri.get("write_time", 0), agent_of(ri)
        rvals = ri.get("read_values", {})
        for j, rj in enumerate(events):
            if i == j or agent_of(rj) == ra:
                continue
            wt_j = rj.get("write_time", 0)
            if not (rt < wt_j < wt_i):
                continue
            wvals = rj.get("write_values", {})
            for c in ri.get("read_set", []):
                if c in rj.get("write_set", []) and rvals.get(c, NULL) != wvals.get(c, NULL):
                    out.append({"i": i, "j": j, "cell": c, "reader": ra, "writer": agent_of(rj),
                                "read_time": rt, "write_time": wt_j, "reader_write_time": wt_i})
    return out


def detect_later_rewrite(events: list[dict]) -> tuple[bool, bool]:
    """The PRE-ROUND-4 quantity, under its true name: some other record wrote a
    different value to a cell this record read, at any time after the read
    (inside OR after the window). Returns (cross_agent, self_agent). It is the
    structural precondition of A_1, not A_1."""
    cross = selfw = False
    for i, ri in enumerate(events):
        rt, ra = ri.get("read_time", 0), agent_of(ri)
        rvals = ri.get("read_values", {})
        for j, rj in enumerate(events):
            if i == j:
                continue
            if rj.get("write_time", 0) <= rt:
                continue
            wvals = rj.get("write_values", {})
            for c in ri.get("read_set", []):
                if c in rj.get("write_set", []) and rvals.get(c, NULL) != wvals.get(c, NULL):
                    if agent_of(rj) != ra:
                        cross = True
                    else:
                        selfw = True
    return cross, selfw


def window_widths(events: list[dict]) -> list[int]:
    return [e.get("write_time", 0) - e.get("read_time", 0) for e in events]


def bootstrap_ci(values: list[float], n: int = 1000, alpha: float = 0.05) -> tuple[float, float]:
    if not values:
        return (0.0, 0.0)
    rng = random.Random(0)
    k = len(values)
    means = []
    for _ in range(n):
        sample = [values[rng.randint(0, k - 1)] for _ in range(k)]
        means.append(sum(sample) / k)
    means.sort()
    return (means[int((alpha / 2) * n)], means[int((1 - alpha / 2) * n)])


def scenario_of(stem: str) -> str:
    return stem.split("-", 1)[0] if "-" in stem else stem


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("traces_dir", type=Path)
    ap.add_argument("--out", type=Path, default=None)
    ap.add_argument("--provider", default="mast")
    args = ap.parse_args()
    if not args.traces_dir.exists():
        raise SystemExit(f"directory {args.traces_dir} does not exist")

    files = sorted(args.traces_dir.glob("*.jsonl"))
    n_found = len(files)
    by_scn: dict[str, list[Path]] = defaultdict(list)
    for p in files:
        by_scn[scenario_of(p.stem)].append(p)
    n_scored = sum(len(v) for v in by_scn.values())
    print(f"files found: {n_found}   files scored: {n_scored}")
    assert n_scored == n_found

    hdr = (f"{'scenario':20} {'n':>4} {'A1 (Def.1)':>11} {'95% CI':>13} "
           f"{'later-rw cross':>15} {'later-rw self':>14} {'ops':>6} {'win=1':>7} {'win>=2':>7}")
    print(hdr)
    print("-" * len(hdr))
    results, grand_n, grand_a1, grand_lr = [], 0, 0, 0
    for scn, paths in sorted(by_scn.items()):
        a1_flags, lr_cross, lr_self, ops, w1, w2 = [], [], [], 0, 0, 0
        for path in paths:
            ev = load_session(path)
            ops += len(ev)
            ww = window_widths(ev)
            w1 += sum(1 for w in ww if w <= 1)
            w2 += sum(1 for w in ww if w >= 2)
            a1_flags.append(1.0 if detect_a1(ev) else 0.0)
            c, s = detect_later_rewrite(ev)
            lr_cross.append(1.0 if c else 0.0)
            lr_self.append(1.0 if s else 0.0)
        a1_r = mean(a1_flags)
        lo, hi = bootstrap_ci(a1_flags)
        grand_n += len(paths)
        grand_a1 += int(sum(a1_flags))
        grand_lr += int(sum(lr_cross))
        print(f"{scn:20} {len(paths):>4} {int(sum(a1_flags)):>4}/{len(paths):<4} "
              f"[{lo*100:>4.0f},{hi*100:>4.0f}]  "
              f"{int(sum(lr_cross)):>7}/{len(paths):<6} {int(sum(lr_self)):>6}/{len(paths):<6} "
              f"{ops:>6} {w1:>7} {w2:>7}")
        results.append({
            "scenario": scn, "provider": args.provider, "n_sessions": len(paths),
            "a1_sessions": int(sum(a1_flags)), "a1_rate": a1_r, "a1_ci95": [lo, hi],
            "later_rewrite_cross_sessions": int(sum(lr_cross)),
            "later_rewrite_self_sessions": int(sum(lr_self)),
            "ops": ops, "ops_window_1": w1, "ops_window_ge2": w2,
        })
    print("-" * len(hdr))
    print(f"TOTAL {grand_n}: A1 (Definition 1) in {grand_a1}/{grand_n} sessions; "
          f"cross-agent later rewrites in {grand_lr}/{grand_n}")
    if args.out is not None:
        args.out.write_text(json.dumps({"cells": results, "n_total_scored": grand_n,
                                        "n_a1_sessions": grand_a1,
                                        "n_later_rewrite_sessions": grand_lr,
                                        "predicate": "Definition 1 (read_time < write_time_j < write_time_i, cross-agent, value mismatch)"},
                                       indent=2))
        print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
