#!/usr/bin/env python3
"""predicate_matrix.py -- score every committed op-record dataset under ALL
THREE relaxations of Definition 1 that this project uses, side by side.

Why this exists.  Three instruments in this repository are all described as
"the A1 predicate" and each drops a different conjunct of Definition 1:

    Definition 1   cross-agent /\\ cell overlap /\\ read_t_i < write_t_j < write_t_i
                   /\\ read_values_i[c] != write_values_j[c]
    structural     cross-agent /\\ cell overlap /\\ window          (value conjunct DROPPED)
                   -- prevalence_static.py, the k-of-N topology bound
    superstep      cross-agent /\\ cell overlap /\\ same superstep
                   /\\ value mismatch                              (window DROPPED)
                   -- prevalence_dynamic_run.py and prevalence_harness.py

They are not interchangeable and their numbers are not comparable.  This tool
prints them together so the difference is a table rather than a footnote.

It also reports the two quantities that decide how to read a superstep
figure: the window widths present in the records (Definition 1 cannot fire on
width-one records at all), and what share of superstep firings are reads of
the executor's initial sentinel rather than of a value another agent
produced.

Deterministic, stdlib only, no network.

    python3 python/predicate_matrix.py
    python3 python/predicate_matrix.py --json python/predicate_matrix.json
"""
from __future__ import annotations
import argparse
import collections
import json
import os
import sys

SENTINEL = "NULL"


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


def def1(h):
    """Full Definition 1 -- Anomalies.tla lines 6-13."""
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


def structural(h):
    """Definition 1 with the VALUE conjunct relaxed away (upper bound)."""
    n = len(h)
    for i in range(n):
        for j in range(n):
            if i == j or agent(h[i]) == agent(h[j]):
                continue
            if not (set(h[i].get("read_set") or []) & set(h[j].get("write_set") or [])):
                continue
            if h[i]["read_time"] < h[j]["write_time"] < h[i]["write_time"]:
                return True
    return False


def superstep(h):
    """Definition 1 with the WINDOW relaxed away, grouped by superstep.

    Returns (fired, sentinel_hits, total_hits) so the caller can report what
    fraction of firings read the executor's initial sentinel.
    """
    if not all("superstep" in r for r in h):
        return None, 0, 0
    by = collections.defaultdict(list)
    for r in h:
        by[r["superstep"]].append(r)
    fired = False
    sent = tot = 0
    for ops in by.values():
        for r in ops:
            for c in r.get("read_set") or []:
                v = (r.get("read_values") or {}).get(c, "")
                for w in ops:
                    if agent(w) == agent(r):
                        continue
                    if c in (w.get("write_set") or []) \
                       and (w.get("write_values") or {}).get(c, "") != v:
                        fired = True
                        tot += 1
                        if v == SENTINEL:
                            sent += 1
                        break
    return fired, sent, tot


def datasets(root):
    """Every committed op-record directory, discovered on disk."""
    cands = [
        ("python/dynamic_oprecords", "S 5.8 topology dynamic run"),
        ("python/oprecords", "S 5.8 own-executor racy check"),
        ("mast_oprecords", "S 5.8 MAST-Data projection"),
        ("python/mast_oprecords", "S 5.8 MAST-Data projection (python/)"),
        ("python/live_a1_gpt4omini/sessions", "Table 6 live, gpt-4o-mini"),
        ("python/live_a1_haiku/sessions", "Table 6 live, claude-haiku-4-5"),
        ("python/live_a1_llama/sessions", "Table 6 live, Llama-3.2"),
    ]
    return [(p, lab) for p, lab in cands if os.path.isdir(os.path.join(root, p))]


def score(root, rel):
    d = os.path.join(root, rel)
    files = sorted(f for f in os.listdir(d) if f.endswith(".jsonl"))
    n = d1 = st = ss = 0
    sent = tot = 0
    widths = collections.Counter()
    ss_applicable = True
    unparsed = 0
    for fn in files:
        h = load(os.path.join(d, fn))
        if h is None:
            unparsed += 1
            continue
        n += 1
        for r in h:
            if "read_time" in r and "write_time" in r:
                widths[r["write_time"] - r["read_time"]] += 1
        if def1(h):
            d1 += 1
        if structural(h):
            st += 1
        f, s, t = superstep(h)
        if f is None:
            ss_applicable = False
        else:
            ss += 1 if f else 0
            sent += s
            tot += t
    return {
        "dir": rel, "sessions": n, "unparsed": unparsed,
        "def1": d1, "structural": st,
        "superstep": (ss if ss_applicable else None),
        "superstep_firing_events": tot,
        "superstep_events_reading_sentinel": sent,
        "window_widths": {str(k): v for k, v in sorted(widths.items())},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--json", default=None)
    a = ap.parse_args()

    if not os.path.isfile(os.path.join(a.root, "expected.json")):
        print("FAIL: run from the mac-consistency-pilot root", file=sys.stderr)
        return 1

    ds = datasets(a.root)
    if not ds:
        print("FAIL: no op-record directory found", file=sys.stderr)
        return 1

    rows = []
    print(f"{'dataset':40s} {'n':>5s} {'Def1':>6s} {'struct':>7s} {'superst':>8s}  widths")
    print("-" * 92)
    for rel, label in ds:
        r = score(a.root, rel)
        r["label"] = label
        rows.append(r)
        ssv = "n/a" if r["superstep"] is None else f"{r['superstep']}"
        print(f"{rel:40s} {r['sessions']:5d} {r['def1']:6d} {r['structural']:7d} "
              f"{ssv:>8s}  {r['window_widths']}")
    print()
    for r in rows:
        if r["superstep_firing_events"]:
            pct = 100.0 * r["superstep_events_reading_sentinel"] / r["superstep_firing_events"]
            print(f"  {r['dir']}: {r['superstep_firing_events']} superstep firing "
                  f"events, {r['superstep_events_reading_sentinel']} "
                  f"({pct:.1f}%) read the initial sentinel {SENTINEL!r} rather "
                  f"than a value another agent produced")
    print()
    print("  Definition 1 cannot fire on a width-one record: the window "
          "read_t < write_t_j < write_t_i is empty when every record's read "
          "and commit land on consecutive ticks.")

    if a.json:
        with open(a.json, "w", encoding="utf-8") as fh:
            json.dump({"rows": rows, "sentinel": SENTINEL}, fh, indent=2)
        print(f"\n  wrote {a.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
