#!/usr/bin/env python3
"""task_utility.py -- what prevention costs in WORK, not in tokens.

WHY THIS EXISTS
  The cost analysis prices prevention in tokens and wall-clock. Neither
  measures the thing a deployer cares about most: whether the task still got
  done. A discipline can drive the anomaly rate to zero by refusing every
  contested commit, and a token metric will report that as cheap. This tool
  scores the committed traces for the outcome instead.

  The metrics are structural and deterministic -- no model calls, no judge:

    roles        the set of agents that commit in the UNGUARDED cell of the
                 same run. Derived, not hard-coded: the baseline defines what
                 a complete session looks like for that workload.
    complete     a session in which every role committed at least one
                 operation.
    clean        a session with no Definition-1 witness.
    both         complete AND clean -- the only outcome a deployer wants.
    dropped      the share of sessions in which a given role committed
                 nothing.

  A prevention claim should be read against `both`, not against `clean`.

  Deterministic, stdlib only, no network.

    python3 python/task_utility.py
    python3 python/task_utility.py --json python/task_utility.json
"""
from __future__ import annotations
import argparse
import json
import os
import sys


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


def fires(h):
    """Definition 1, as check_tables.sh transcribes it."""
    n = len(h)
    for i in range(n):
        for j in range(n):
            if i == j or agent(h[i]) == agent(h[j]):
                continue
            for c in set(h[i].get("read_set") or []) & set(h[j].get("write_set") or []):
                if h[i]["read_time"] < h[j]["write_time"] < h[i]["write_time"] \
                   and (h[i].get("read_values") or {}).get(c) \
                       != (h[j].get("write_values") or {}).get(c):
                    return True
    return False


def sessions(d):
    for fn in sorted(os.listdir(d)):
        if fn.endswith(".jsonl"):
            h = load(os.path.join(d, fn))
            if h is not None:
                yield h


def cells(root):
    """(run, workload, discipline, path) for every op-record cell."""
    out = []
    runs = os.path.join(root, "runs")
    if not os.path.isdir(runs):
        return out
    for stamp in sorted(os.listdir(runs)):
        p = os.path.join(runs, stamp)
        if not os.path.isdir(p):
            continue
        for cell in sorted(os.listdir(p)):
            q = os.path.join(p, cell)
            if not os.path.isdir(q) or cell.startswith("tokens-"):
                continue
            if "-" not in cell:
                continue
            workload, _, discipline = cell.rpartition("-")
            out.append((stamp, workload, discipline, q))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--json", default=None)
    a = ap.parse_args()

    if not os.path.isfile(os.path.join(a.root, "expected.json")):
        print("FAIL: run from the mac-consistency-pilot root", file=sys.stderr)
        return 1

    found = cells(a.root)
    # roles come from the unguarded cell of the SAME run and workload
    roles = {}
    for stamp, workload, disc, path in found:
        if disc == "vanilla":
            r = set()
            for h in sessions(path):
                r |= {agent(x) for x in h}
            roles[(stamp, workload)] = r

    rows = []
    print(f"  {'run/workload (run = HHMMSS)':30s} {'discipline':12s} {'n':>4s} {'clean':>6s} "
          f"{'complete':>9s} {'both':>6s}   roles dropped")
    print("  " + "-" * 96)
    for stamp, workload, disc, path in found:
        R = roles.get((stamp, workload))
        if not R:
            continue
        n = clean = complete = both = 0
        missing = {r: 0 for r in sorted(R)}
        for h in sessions(path):
            n += 1
            present = {agent(x) for x in h}
            c = not fires(h)
            done = R <= present
            clean += c
            complete += done
            both += (c and done)
            for r in R - present:
                missing[r] += 1
        drop = ", ".join(f"{r} {100*v/n:.0f}%" for r, v in missing.items() if v)
        rows.append({"run": stamp, "workload": workload, "discipline": disc,
                     "roles": sorted(R), "n": n, "clean": clean,
                     "complete": complete, "both": both,
                     "dropped": {r: v for r, v in missing.items() if v}})
        print(f"  {stamp[8:14] + '/' + workload:30s} {disc:12s} {n:4d} {clean:6d} "
              f"{complete:9d} {both:6d}   {drop or '-'}")

    print("  " + "-" * 96)
    print("  `clean` is what the anomaly rate reports. `both` is what a deployer gets.")
    print("  Where they diverge, the discipline bought prevention by refusing work.")
    print("  `complete` is a STRUCTURAL proxy -- every role that commits in the")
    print("  unguarded baseline also commits here -- not a judgment that the task")
    print("  succeeded. A session missing one role may still be useful output; it is")
    print("  not the output the baseline produced, which is what this counts.")

    # The correlation worth naming: a refused role whose contribution reaches
    # the log in exactly the sessions that also fired, i.e. it lands if and
    # only if it is stale. `complete` counts sessions where every role
    # committed; `n - clean` counts sessions that fired. Equality of the two,
    # with both non-zero, is the condition.
    for r in rows:
        if r["discipline"] == "vanilla" or not r["dropped"]:
            continue
        dirty = r["n"] - r["clean"]
        if r["complete"] and r["complete"] == dirty:
            print(f"  NOTE {r['run']}/{r['workload']}/{r['discipline']}: the refused "
                  f"role's contribution lands in exactly the {r['complete']} "
                  f"session(s) that also fired -- it reaches the log if and only "
                  f"if it is stale.")

    if a.json:
        with open(a.json, "w", encoding="utf-8") as fh:
            json.dump({"rows": rows}, fh, indent=2)
        print(f"\n  wrote {a.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
