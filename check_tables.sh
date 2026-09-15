#!/usr/bin/env bash
# =====================================================================
# check_tables.sh -- four gates.
#
#   CELLS    Score the committed traces under Definition 1 and fail if
#            any published cell disagrees with expected.json.  This is a
#            second, independent transcription from Anomalies.tla lines
#            6-13; it does NOT call rust-analyser, so agreement between
#            the two is evidence rather than a tautology.  Writes each
#            run's summary.check.json; never overwrites a captured
#            summary.json.
#
#   MAP      Every repository path named in REPRODUCE.md's table must
#            exist.  A map that points at nothing is worse than no map.
#
#   IGNORES  Only the root .gitignore may carry active rules among the
#            ignore files git honors (./check_ignores.sh).  Evidence was
#            invisible for two rounds because a nested ignore file went
#            unread.
#
#   IMPORTS  Every intra-repo `from M import n` in a file REPRODUCE.md cites
#            must resolve (./python/check_imports.py).  The MAP gate above
#            tests that a path EXISTS; it cannot tell a loadable analyzer
#            from a dead one.  python/prevalence_static.py -- the analyzer
#            that produces the k-of-N topology bound, named by filename in
#            the appendix -- imported compute_layers from the wrong module
#            and raised ImportError on a clean clone with all three gates
#            green.  A file REPRODUCE.md does not cite is reported as a
#            warning and does not gate.
#
#   ./check_tables.sh          all three gates, per-cell detail
#   ./check_tables.sh --quiet  verdict only
#
# Requires python3 only.  No network, no API keys, no cargo.
# =====================================================================
set -euo pipefail
[ -f expected.json ] || { echo "FAIL: run from the mac-consistency-pilot root" >&2; exit 1; }

if [ -x ./check_ignores.sh ]; then
  if [ "${1:-}" = "--quiet" ]; then
    ./check_ignores.sh --quiet >/dev/null || { echo "FAIL: ignore-file gate"; ./check_ignores.sh; exit 1; }
  else
    ./check_ignores.sh || exit 1
  fi
fi

if [ -f ./python/check_imports.py ]; then
  if [ "${1:-}" = "--quiet" ]; then
    python3 ./python/check_imports.py --quiet >/dev/null \
      || { echo "FAIL: import gate"; python3 ./python/check_imports.py; exit 1; }
  else
    python3 ./python/check_imports.py || exit 1
  fi
fi

exec python3 - "$@" << 'PY_EOF'
import json, os, re, sys

QUIET = "--quiet" in sys.argv[1:]

def agent(r):
    a = r.get("agent")
    return a if a is not None else r.get("agent_id")

def load(p):
    with open(p) as f:
        return [json.loads(l) for l in f if l.strip()]

def a1(h):
    """Anomalies.tla lines 6-13, StaleGeneration, transcribed.

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
            for c in set(h[i].get("read_set") or []) & set(h[j].get("write_set") or []):
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

# ---- GATE 1: cells ---------------------------------------------------
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
    with open(os.path.join("runs", stamp, "summary.check.json"), "w") as f:
        json.dump(summary, f, indent=2)

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

# ---- GATE 2: REPRODUCE.md's map resolves -----------------------------
mapped = 0
if not os.path.isfile("REPRODUCE.md"):
    bad.append("REPRODUCE.md absent")
else:
    rows = [l for l in open("REPRODUCE.md").read().splitlines() if l.lstrip().startswith("|")]
    seen = set()
    for line in rows:
        for m in re.finditer(r"`([A-Za-z0-9_][A-Za-z0-9_./-]*)`", line):
            q = m.group(1).rstrip("/")
            if q.startswith("../") or q in seen or "/" not in q:
                continue
            seen.add(q)
            if not os.path.exists(q):
                bad.append(f"REPRODUCE.md names a path that does not exist: {q}")
            else:
                mapped += 1
                checked += 1
if not QUIET:
    print(f"  ok  REPRODUCE.md map: {mapped} paths resolve")

print()
if bad:
    print(f"FAIL: {len(bad)} of {checked} checks failed")
    for b in bad:
        print(f"  - {b}")
    sys.exit(1)
print(f"OK: all {checked} checks pass ({mapped} mapped paths resolve)")
PY_EOF
