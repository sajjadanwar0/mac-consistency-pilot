#!/usr/bin/env bash
# =====================================================================
# check_tables.sh -- score the committed traces under Definition 1 and
# fail if any published cell disagrees with expected.json.
#
# This does NOT call rust-analyser.  It is a second, independent
# implementation of Definition 1 transcribed from Anomalies.tla:6-13, so
# that agreement between the two is evidence and not a tautology.  It
# also regenerates runs/<stamp>/summary.json from the traces.
#
#   ./check_tables.sh          score everything, exit non-zero on any miss
#   ./check_tables.sh --quiet  cells only, no per-run detail
#
# Requires python3 only.  No network, no API keys, no cargo.
# =====================================================================
set -euo pipefail
[ -f expected.json ] || { echo "FAIL: run from the mac-consistency-pilot root" >&2; exit 1; }
exec python3 - "$@" << 'PY_EOF'
import json, os, sys

QUIET = "--quiet" in sys.argv[1:]

def agent(r):
    a = r.get("agent")
    return a if a is not None else r.get("agent_id")

def load(p):
    with open(p) as f:
        return [json.loads(l) for l in f if l.strip()]

def a1(h):
    """Anomalies.tla:6-13 StaleGeneration, transcribed.

    \\E i,j : i # j /\\ h[i].agent # h[j].agent
              /\\ \\E c \\in h[i].read_set \\cap h[j].write_set :
                   h[i].read_time  < h[j].write_time
                /\\ h[j].write_time < h[i].write_time
                /\\ h[i].read_values[c] # h[j].write_values[c]
    """
    n = len(h)
    for i in range(n):
        for j in range(n):
            if i == j or agent(h[i]) == agent(h[j]):
                continue
            shared = set(h[i].get("read_set") or []) & set(h[j].get("write_set") or [])
            for c in shared:
                if h[i]["read_time"] < h[j]["write_time"] < h[i]["write_time"] \
                   and (h[i].get("read_values") or {}).get(c) != (h[j].get("write_values") or {}).get(c):
                    return True
    return False

def score(d):
    fs = sorted(f for f in os.listdir(d) if f.endswith(".jsonl"))
    return len(fs), sum(1 for f in fs if a1(load(os.path.join(d, f))))

def live_root():
    for c in ("python", "."):
        if os.path.isdir(os.path.join(c, "live_a1_gpt4omini", "sessions")):
            return c
    return None

exp = json.load(open("expected.json"))
bad, checked = [], 0

# ---- runs/<stamp>/<cell>/ ------------------------------------------
pool = {}
for stamp, spec in exp["runs"].items():
    summary = {"cells": {}, "predicate": "Definition 1 (check_tables.sh, independent of rust-analyser)"}
    for cell, want in spec["cells"].items():
        p = os.path.join("runs", stamp, cell)
        if not os.path.isdir(p):
            bad.append(f"{stamp}/{cell}: directory absent"); continue
        n, k = score(p)
        checked += 1
        summary["cells"][cell] = {"n": n, "a1_sessions": k}
        pool.setdefault(cell, [0, 0])
        pool[cell][0] += n; pool[cell][1] += k
        ok = (n == want["n"] and k == want["a1"])
        if not ok:
            bad.append(f"{stamp}/{cell}: scored {k}/{n}, expected {want['a1']}/{want['n']}")
        if not QUIET:
            print(f"  {'ok ' if ok else 'MISS'} runs/{stamp}/{cell:32s} {k:3d}/{n:3d}  expected {want['a1']:3d}")
    # Never overwrite a captured summary.json -- 20260913T0424Z's was written
    # by the run harness and is evidence.  This scorer's output sits beside it.
    with open(os.path.join("runs", stamp, "summary.check.json"), "w") as f:
        json.dump(summary, f, indent=2)

# ---- pooled --------------------------------------------------------
for cell, want in exp["pooled"].items():
    if cell.startswith("_"):
        continue
    n, k = pool.get(cell, [0, 0])
    checked += 1
    ok = (n == want["n"] and k == want["a1"])
    if not ok:
        bad.append(f"pooled/{cell}: scored {k}/{n}, expected {want['a1']}/{want['n']}")
    if not QUIET:
        print(f"  {'ok ' if ok else 'MISS'} pooled {cell:39s} {k:3d}/{n:3d}  expected {want['a1']:3d}")

# ---- live ----------------------------------------------------------
lr = live_root()
if lr is None:
    bad.append("live: live_a1_gpt4omini/sessions not found under python/ or the repo root")
else:
    for model, cells in exp["live"].items():
        if model.startswith("_"):
            continue
        S = os.path.join(lr, model, "sessions")
        if not os.path.isdir(S):
            bad.append(f"live/{model}: sessions/ absent"); continue
        fs = os.listdir(S)
        for kind, want in cells.items():
            sel = sorted(f for f in fs if f.startswith(kind + "_") and f.endswith(".jsonl"))
            k = sum(1 for f in sel if a1(load(os.path.join(S, f))))
            checked += 1
            ok = (len(sel) == want["n"] and k == want["a1"])
            if not ok:
                bad.append(f"live/{model}/{kind}: scored {k}/{len(sel)}, expected {want['a1']}/{want['n']}")
            if not QUIET:
                print(f"  {'ok ' if ok else 'MISS'} {model}/{kind:26s} {k:3d}/{len(sel):3d}  expected {want['a1']:3d}")

print()
if bad:
    print(f"FAIL: {len(bad)} of {checked} cells disagree with expected.json")
    for b in bad:
        print(f"  - {b}")
    sys.exit(1)
print(f"OK: all {checked} published cells reproduce under Definition 1")
PY_EOF
