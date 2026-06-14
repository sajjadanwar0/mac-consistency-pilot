#!/usr/bin/env python3
"""
build_runs_csv.py

Assemble the runs.csv that paired_cost_analysis.py consumes, from the per-call
token sidecar files that autogen_pilot.py already writes:
    {workload}-{runtime}-{scenario_id:04d}.tokens.jsonl
(e.g. edit-review-vanilla-0003.tokens.jsonl). One sidecar = one session; this
script sums tokens and wall-clock per session and emits one CSV row per session.

The pairing key is (workload, seed) where seed = scenario_id. For the paired
analysis to mean anything, the SAME scenario_id must have been run under each
runtime (see the IMPORTANT pairing note at the bottom).

USAGE
-----
  # point at every token-output dir you produced (one per runtime is fine;
  # the runtime is read from each filename, not the dir name):
  python build_runs_csv.py ../tok_vanilla ../tok_pess ../tok_si --out runs.csv

  # optional: supply runtime trace dirs to fill the 'aborts' column
  python build_runs_csv.py ../tok_* --traces ../triage-traces --out runs.csv

  then:
  python paired_cost_analysis.py runs.csv --metric total_tokens
  python paired_cost_analysis.py runs.csv --metric wallclock_s

If you instead already have a per-session table (e.g. wallclock_results.json
with rows carrying workload/strategy/seed/tokens/wallclock), you do not need
this script -- just rename those fields to the six columns above. Run
  python -c "import json,sys;d=json.load(open('wallclock_results.json'));print(type(d), (d[0] if isinstance(d,list) else list(d)[:5]))"
to inspect its shape first.
"""
from __future__ import annotations
import argparse
import csv
import glob
import json
import os
import sys
from collections import defaultdict

RUNTIME_TO_STRATEGY = {
    "vanilla": "vanilla",
    "pessimistic": "pessimistic",
    "snapshot_isolation": "ssi",
    "ssi": "ssi",
}


def session_tokens_and_wall(path: str) -> tuple[int, float]:
    """Sum per-call usage in one sidecar JSONL. Defensive about field names."""
    total = 0
    wall_ms = 0.0
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        try:
            r = json.loads(line)
        except Exception:
            continue
        if "total_tokens" in r and isinstance(r["total_tokens"], (int, float)):
            total += int(r["total_tokens"])
        else:
            total += int(r.get("prompt_tokens", 0)) + int(r.get("completion_tokens", 0))
        for k in ("wall_clock_ms", "elapsed_ms", "latency_ms"):
            if k in r:
                wall_ms += float(r[k]); break
    return total, wall_ms / 1000.0


def parse_name(stem: str) -> tuple[str, str, str] | None:
    """'edit-review-vanilla-0003' -> ('edit-review','vanilla','0003').
    rsplit on '-' twice: workload may contain hyphens, runtime/seed do not."""
    parts = stem.rsplit("-", 2)
    if len(parts) != 3:
        return None
    return parts[0], parts[1], parts[2]


def abort_counts(trace_dirs: list[str]) -> dict[tuple[str, str, str], int]:
    """Optional: count 'aborted' events per (workload, runtime, seed) if the
    runtime trace files record them. Filenames assumed like
    {workload}-{runtime}-trace-{id}.jsonl or {workload}-trace-{id}.jsonl."""
    out: dict[tuple[str, str, str], int] = {}
    for d in trace_dirs:
        for f in glob.glob(os.path.join(d, "*.jsonl")):
            n = 0
            for line in open(f):
                try:
                    e = json.loads(line)
                except Exception:
                    continue
                if e.get("aborted") or e.get("event") == "abort" or e.get("status") == "aborted":
                    n += 1
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("dirs", nargs="+", help="token-sidecar directories")
    ap.add_argument("--out", default="runs.csv")
    ap.add_argument("--traces", nargs="*", default=[], help="optional runtime trace dirs for aborts")
    args = ap.parse_args()

    sidecars = []
    for d in args.dirs:
        sidecars += glob.glob(os.path.join(d, "*.tokens.jsonl"))
    if not sidecars:
        raise SystemExit(
            "no *.tokens.jsonl files found. Point at the --tokens-output dirs "
            "autogen_pilot.py wrote (one per runtime)."
        )

    rows = []
    skipped = []
    seen_strategies = set()
    for path in sorted(sidecars):
        stem = os.path.basename(path)[:-len(".tokens.jsonl")]
        parsed = parse_name(stem)
        if parsed is None:
            skipped.append(os.path.basename(path)); continue
        workload, runtime, seed = parsed
        strategy = RUNTIME_TO_STRATEGY.get(runtime, runtime)
        seen_strategies.add(strategy)
        tot, wall = session_tokens_and_wall(path)
        rows.append((workload, strategy, seed, tot, round(wall, 3), 0))

    if skipped:
        print(f"WARNING: {len(skipped)} files had unparseable names and were skipped:",
              file=sys.stderr)
        for s in skipped[:10]:
            print("  " + s, file=sys.stderr)

    with open(args.out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["workload", "strategy", "seed", "total_tokens", "wallclock_s", "aborts"])
        w.writerows(rows)

    by_pair = defaultdict(set)
    for wl, st, sd, *_ in rows:
        by_pair[(wl, sd)].add(st)
    full = sum(1 for v in by_pair.values() if len(v) == len(seen_strategies))
    print(f"wrote {args.out}: {len(rows)} sessions, strategies={sorted(seen_strategies)}")
    print(f"matched (workload,seed) cells with ALL strategies present: "
          f"{full}/{len(by_pair)}")
    if full < len(by_pair):
        print("  NOTE: only fully-matched cells contribute to the paired analysis. "
              "If this is low, your runtimes did not share scenario_ids -- re-run "
              "each runtime with the same --n and scenario range.")


if __name__ == "__main__":
    main()