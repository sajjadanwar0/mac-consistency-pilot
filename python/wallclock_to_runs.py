#!/usr/bin/env python3
"""
wallclock_to_runs.py

Convert an existing per-session wallclock_results.json into the runs.csv that
paired_cost_analysis.py consumes. No re-run needed: your file already has one
row per session with workload/strategy/seed/tokens/wallclock/aborts.

USAGE
  python wallclock_to_runs.py wallclock_results.json --out runs.csv
  python paired_cost_analysis.py runs.csv --metric total_tokens
  python paired_cost_analysis.py runs.csv --metric wallclock_s

It reports how many (workload, seed) cells have all strategies present, so you
know the paired analysis is well-formed.
"""
from __future__ import annotations
import argparse
import csv
import json
import sys
from collections import defaultdict


def total_tokens(r: dict) -> int:
    if "total_tokens" in r:
        return int(r["total_tokens"])
    return int(r.get("prompt_tokens", 0)) + int(r.get("completion_tokens", 0))


def wallclock_s(r: dict):
    for k in ("wallclock_s", "wall_clock_seconds", "wall_clock_s", "wallclock_seconds"):
        if k in r:
            return r[k]
    if "wall_clock_ms" in r:
        return float(r["wall_clock_ms"]) / 1000.0
    return ""


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("json_path")
    ap.add_argument("--out", default="runs.csv")
    args = ap.parse_args()

    data = json.load(open(args.json_path))
    if isinstance(data, dict):
        for k in ("sessions", "rows", "results", "data"):
            if isinstance(data.get(k), list):
                data = data[k]; break
        else:
            raise SystemExit("expected a list of per-session rows; got a dict "
                             "without a recognised list field")
    if not isinstance(data, list) or not data:
        raise SystemExit("no per-session rows found")

    required = {"workload", "strategy", "seed"}
    missing = required - set(data[0])
    if missing:
        raise SystemExit(f"rows are missing required fields: {missing}; "
                         f"saw keys {sorted(data[0])}")

    rows = []
    for r in data:
        rows.append([r["workload"], r["strategy"], r["seed"],
                     total_tokens(r), wallclock_s(r), r.get("aborts", 0)])

    with open(args.out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["workload", "strategy", "seed", "total_tokens", "wallclock_s", "aborts"])
        w.writerows(rows)

    strategies = sorted({r[1] for r in rows})
    by_pair = defaultdict(set)
    for wl, st, sd, *_ in rows:
        by_pair[(wl, sd)].add(st)
    full = sum(1 for v in by_pair.values() if len(v) == len(strategies))
    print(f"wrote {args.out}: {len(rows)} sessions, strategies={strategies}")
    print(f"matched (workload,seed) cells with ALL strategies present: {full}/{len(by_pair)}")
    if full < len(by_pair):
        print("  NOTE: only fully-matched cells feed the paired analysis.")


if __name__ == "__main__":
    main()