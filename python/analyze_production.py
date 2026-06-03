#!/usr/bin/env python3
"""
analyze_production_fixed.py

Drop-in replacement for analyze_production.py.

WHY THIS EXISTS
---------------
The original analyzer derived the scenario name from the file stem with
`parts = stem.rsplit("-", 2); if len(parts) != 3: continue`. Any op-record
file whose name did not split into exactly three hyphen-separated parts was
SILENTLY skipped (the "skip ... cannot parse" message went to stderr). On the
full MAST run the adapter wrote 600 files but only 410 had names that parsed,
so 190 were dropped without appearing in the table. The 0% A1 rate is real on
what was scored, but the denominator was wrong.

This version:
  * derives scenario from the leading hyphen token (robust to ids that contain
    hyphens/underscores),
  * NEVER silently skips: any file that cannot be grouped is collected and the
    run fails loudly at the end with the offending names,
  * prints n_files_found and asserts n_scored == n_files_found.

USAGE
-----
  python analyze_production_fixed.py mast_oprecords --out mast_rates.json

Schema per JSONL line (unchanged): each event may carry
  read_set: [cell], write_set: [cell],
  read_time: int, write_time: int,
  read_values: {cell: str}, write_values: {cell: str},
  agent_id: str
"""
from __future__ import annotations
import argparse
import json
import random
import sys
from collections import defaultdict
from pathlib import Path
from statistics import mean


def load_session(path: Path) -> list[dict]:
    events = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        events.append(json.loads(line))
    return events


def detect_a1_breakdown(events: list[dict]) -> tuple[bool, bool, bool]:
    """Return (any_a1, cross_agent_a1, self_agent_a1)."""
    cell_writes: dict[str, list[tuple[int, str, str]]] = defaultdict(list)
    for e in events:
        for c in e.get("write_set", []):
            wt = e.get("write_time", 0)
            wv = e.get("write_values", {}).get(c, "")
            ag = e.get("agent_id", "?")
            cell_writes[c].append((wt, wv, ag))

    any_a1 = cross_a1 = self_a1 = False
    for r in events:
        rt = r.get("read_time", 0)
        ragent = r.get("agent_id", "?")
        for c in r.get("read_set", []):
            rv = r.get("read_values", {}).get(c, "")
            for wt, wv, wagent in cell_writes.get(c, []):
                if wt > rt and wv != rv:
                    any_a1 = True
                    if wagent != ragent:
                        cross_a1 = True
                    else:
                        self_a1 = True
    return any_a1, cross_a1, self_a1


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
    lo = means[int((alpha / 2) * n)]
    hi = means[int((1 - alpha / 2) * n)]
    return (lo, hi)


def scenario_of(stem: str) -> str:
    """Robust: scenario is the leading token before the first '-'.
    'chatdev-mast-ChatDev_5' -> 'chatdev'. Never raises here; grouping
    correctness is asserted in main()."""
    return stem.split("-", 1)[0] if "-" in stem else stem


def main() -> None:
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
    unparseable: list[str] = []
    for p in files:
        scn = scenario_of(p.stem)
        if not scn:
            unparseable.append(p.name)
            continue
        by_scn[scn].append(p)

    n_scored = sum(len(v) for v in by_scn.values())
    print(f"files found: {n_found}   files scored: {n_scored}   dropped: {n_found - n_scored}")
    if unparseable:
        raise SystemExit(
            "REFUSING TO RUN: %d files could not be grouped into a scenario:\n  %s\n"
            "Fix the op-record filenames or scenario_of() rather than silently skipping."
            % (len(unparseable), "\n  ".join(unparseable[:20]))
        )
    assert n_scored == n_found, (
        f"scored {n_scored} != found {n_found}; some files were dropped silently"
    )

    hdr = (f"{'scenario':22} {'n':>5} {'any A_1':>10} {'95% CI':>16} "
           f"{'cross':>8} {'self':>8} {'mean ev':>9}")
    print(hdr); print("-" * len(hdr))
    results = []
    grand_n = 0
    grand_a1 = 0
    for scn, paths in sorted(by_scn.items()):
        any_flags, cross_flags, self_flags, evcounts = [], [], [], []
        for path in paths:
            events = load_session(path)
            evcounts.append(len(events))
            a, c, s = detect_a1_breakdown(events)
            any_flags.append(1.0 if a else 0.0)
            cross_flags.append(1.0 if c else 0.0)
            self_flags.append(1.0 if s else 0.0)
        any_r = mean(any_flags) if any_flags else 0.0
        lo, hi = bootstrap_ci(any_flags)
        ev_mean = mean(evcounts) if evcounts else 0.0
        grand_n += len(paths)
        grand_a1 += int(sum(any_flags))
        print(f"{scn:22} {len(paths):>5} {any_r*100:>9.1f}% "
              f"[{lo*100:>4.0f},{hi*100:>4.0f}] "
              f"{mean(cross_flags)*100:>7.1f}% {mean(self_flags)*100:>7.1f}% {ev_mean:>9.1f}")
        results.append({
            "scenario": scn, "provider": args.provider,
            "n_sessions": len(paths), "a1_any_rate": any_r, "a1_any_ci": [lo, hi],
            "a1_cross_agent_rate": mean(cross_flags), "a1_self_agent_rate": mean(self_flags),
            "mean_events_per_session": ev_mean,
        })
    print("-" * len(hdr))
    print(f"{'TOTAL':22} {grand_n:>5}   A1 fired in {grand_a1}/{grand_n} sessions "
          f"({100.0*grand_a1/grand_n if grand_n else 0:.1f}%)")
    if args.out is not None:
        args.out.write_text(json.dumps(
            {"cells": results, "n_total_scored": grand_n, "n_a1_sessions": grand_a1},
            indent=2))
        print(f"wrote {args.out}")


if __name__ == "__main__":
    main()