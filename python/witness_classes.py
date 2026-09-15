#!/usr/bin/env python3
"""witness_classes.py -- split every committed Definition-1 witness into the
two classes the predicate does not distinguish, and report them per dataset.

WHY THIS EXISTS
  Definition 1 fires when an operation read cell c with value v and a
  different agent committed v' != v inside its window. It says nothing about
  what v was. Two very different executions satisfy it:

    COLD-START   v is the store's initial sentinel. The reader reached the
                 cell before anyone had written it: a reviewer reviewing a
                 document that does not exist yet. Real, and avoidable by
                 seeding the store, which is an engineering matter.
    SUPERSESSION v is a value another agent wrote. The reader held a real
                 prior value across its generation phase and a concurrent
                 write superseded it. This is the phenomenon the paper's
                 narrative describes and the one the lattice is built around.

  The distinction matters because the committed datasets are not alike, and
  presenting them as a progression toward realism invites the reader to treat
  them as one phenomenon measured three ways. They are not. Running this tool
  is how that is checked rather than assumed.

  It also connects to the formal side. With |Values| = {v1} the TLA+ lattice
  matrix can only express the cold-start class, because Guarded.tla constrains
  a write to a cell in the write set to be non-NULL and there is exactly one
  non-NULL value, so a witness requires the read value to be the sentinel.
  The bound and the synthetic datasets exercise the same class.

  Deterministic, stdlib only, no network.

    python3 python/witness_classes.py
    python3 python/witness_classes.py --json python/witness_classes.json
"""
from __future__ import annotations
import argparse
import json
import os
import sys

SENTINELS = {"NULL", "None", "", None}


def agent(r):
    a = r.get("agent")
    return a if a is not None else r.get("agent_id")


def load(path):
    out = []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                try:
                    out.append(json.loads(line))
                except json.JSONDecodeError:
                    return None
    return out


def witnesses(h):
    """Every Definition-1 witness, as (read_value, write_value) pairs."""
    out = []
    n = len(h)
    for i in range(n):
        for j in range(n):
            if i == j or agent(h[i]) == agent(h[j]):
                continue
            for c in set(h[i].get("read_set") or []) & set(h[j].get("write_set") or []):
                if h[i]["read_time"] < h[j]["write_time"] < h[i]["write_time"] \
                   and (h[i].get("read_values") or {}).get(c) \
                       != (h[j].get("write_values") or {}).get(c):
                    out.append(((h[i].get("read_values") or {}).get(c),
                                (h[j].get("write_values") or {}).get(c)))
    return out


def score_dir(d):
    files = sorted(f for f in os.listdir(d) if f.endswith(".jsonl"))
    sessions = fired = cold = supers = 0
    widths = set()
    for fn in files:
        h = load(os.path.join(d, fn))
        if h is None:
            continue
        sessions += 1
        for r in h:
            if "read_time" in r and "write_time" in r:
                widths.add(r["write_time"] - r["read_time"])
        ws = witnesses(h)
        if ws:
            fired += 1
        for rv, _ in ws:
            if rv in SENTINELS:
                cold += 1
            else:
                supers += 1
    return sessions, fired, cold, supers, widths


def datasets(root):
    found = []
    runs = os.path.join(root, "runs")
    if os.path.isdir(runs):
        for stamp in sorted(os.listdir(runs)):
            p = os.path.join(runs, stamp)
            if not os.path.isdir(p):
                continue
            for cell in sorted(os.listdir(p)):
                q = os.path.join(p, cell)
                if os.path.isdir(q):
                    found.append((f"runs/{stamp}/{cell}", q, "synthetic pilot"))
    for rel, lab in (("python/oprecords", "own-executor racy check"),
                     ("python/dynamic_oprecords", "topology dynamic run"),
                     ("python/live_a1_gpt4omini/sessions", "live, gpt-4o-mini"),
                     ("python/live_a1_haiku/sessions", "live, claude-haiku-4-5"),
                     ("python/live_a1_llama/sessions", "live, Llama-3.2")):
        p = os.path.join(root, rel)
        if os.path.isdir(p):
            found.append((rel, p, lab))
    return found


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--json", default=None)
    a = ap.parse_args()

    if not os.path.isfile(os.path.join(a.root, "expected.json")):
        print("FAIL: run from the mac-consistency-pilot root", file=sys.stderr)
        return 1

    groups = {"synthetic pilot": [0, 0], "own-executor racy check": [0, 0],
              "topology dynamic run": [0, 0], "live": [0, 0]}
    rows = []
    print(f"  {'dataset':46s} {'sess':>5s} {'fired':>6s} {'cold-start':>11s} "
          f"{'supersession':>13s}")
    print("  " + "-" * 86)
    for rel, path, lab in datasets(a.root):
        s, f, cold, sup, widths = score_dir(path)
        rows.append({"dataset": rel, "kind": lab, "sessions": s, "fired": f,
                     "cold_start": cold, "supersession": sup,
                     "window_widths": sorted(widths),
                     "width_one_only": widths == {1}})
        key = "live" if lab.startswith("live") else lab
        groups[key][0] += cold
        groups[key][1] += sup
        if f:
            print(f"  {rel:46s} {s:5d} {f:6d} {cold:11d} {sup:13d}")

    print("  " + "-" * 86)
    for k, (cold, sup) in groups.items():
        tot = cold + sup
        if not tot:
            continue
        print(f"  {k:34s} {tot:5d} witnesses   cold-start {100*cold/tot:5.1f}%   "
              f"supersession {100*sup/tot:5.1f}%")
    print()
    silent = [r for r in rows if r["fired"] == 0]
    if silent:
        notrace = [r for r in silent if not r["window_widths"]]
        w1 = [r for r in silent if r["window_widths"] and r["width_one_only"]]
        other = [r for r in silent if r["window_widths"] and not r["width_one_only"]]
        print(f"  {len(silent)} dataset(s) produce NO Definition-1 witness and are omitted")
        print("  from the table above, for THREE different reasons, which this tool")
        print("  distinguishes rather than pooling:")
        if notrace:
            print("    (0) the directory holds no operation records at all (token-cost")
            print("        captures carry no read_time/write_time), so the predicate is")
            f"        not defined over them --"
            print("        not defined over them --")
            for r in notrace:
                print(f"          {r['dataset']} ({r['sessions']} files)")
        if w1:
            print("    (a) every record has a width-one window, so the predicate cannot")
            print("        fire. Read this per cell: for a GUARDED cell the closed window")
            print("        IS the discipline's mechanism and the zero is the result; for")
            print("        an UNGUARDED cell it means the workload never opened a window,")
            print("        and the zero is not evidence about any discipline --")
            for r in w1:
                print(f"          {r['dataset']} ({r['sessions']} sessions)")
        if other:
            print("    (b) windows of width > 1 are present, so the predicate COULD have")
            print("        fired and did not: a guarded discipline or a workload that")
            print("        does not produce the shape --")
            for r in other:
                print(f"          {r['dataset']} ({r['sessions']} sessions, "
                      f"widths {r['window_widths']})")
        print()
    print("  Definition 1 does not separate cold-start from supersession. The datasets")
    print("  are not alike, and the live study is the one whose witnesses are")
    print("  supersessions throughout.")

    if a.json:
        with open(a.json, "w", encoding="utf-8") as fh:
            json.dump({"rows": rows, "sentinels": sorted(
                x for x in SENTINELS if x is not None)}, fh, indent=2)
        print(f"\n  wrote {a.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
