#!/usr/bin/env bash
# =====================================================================
# Round 5 v2 (mac-consistency-pilot) — E2b: make Tables 3 and 4 reproducible.
#   v2: scores only the workload cells (v1 also swallowed the tokens-*/ sidecars
#   and crashed in the scorer); a trace the detector cannot score now fails
#   by name instead of with a traceback.  Existing cells are not regenerated,
#   so re-running on STAMP=20260913T0150Z scores the 900 traces already made.
#
# WHY (13 Sep 2026)
#   The committed *-traces/ directories are not the traces that produced
#   the committed *-results.txt: every edit-review results block reports 2
#   operations, every committed edit-review trace has 1 or 3; re-scoring
#   the committed traces with the verified detector gives 43/0/0 against
#   the paper's 100/1/35 (Table 3). autogen_pilot.py's default --output is
#   ../<workload>-traces/, so any later run silently overwrote the traces
#   while the results files stayed. Table 4's 900 sessions left token logs
#   only (pilot_tokens*/), no op-records, so its A_1 rows cannot be
#   re-scored at all.
#
# WHAT THIS DOES
#   One run directory per invocation, never the legacy trace dirs:
#     runs/<stamp>/<workload>-<runtime>/*.jsonl    the traces
#     runs/<stamp>/results.txt                     verified-detector output
#     runs/<stamp>/summary.json                    per-cell A_1 sessions + CI
#     runs/<stamp>/manifest.json                   model, seed, git sha, detector sha256
#   and asserts, for every trace, that the operation count the detector
#   scored equals the operation count in the file it was given.
#
#   Table 3: 3 workloads x vanilla x 100 sessions on gpt-4o        (default)
#   Table 4: add --table4 -> + pessimistic + snapshot_isolation      (900 total)
#
# Requires OPENAI_API_KEY, the AutoGen environment the driver already
# runs in (use PY="uv run python" if that is how you run it), and cargo.
# Cells that already hold 100 traces in this run dir are not regenerated,
# so an interrupted run resumes.  Nothing in the repo is modified; the
# run directory is new content to commit.
# =====================================================================
set -euo pipefail

say()   { printf '  %s\n' "$*"; }
flunk() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

[ -f python/autogen_pilot.py ] || flunk "run from ~/RustroverProjects/mac-consistency-pilot"
[ -n "${OPENAI_API_KEY:-}" ]   || flunk "OPENAI_API_KEY is not set"
command -v cargo >/dev/null    || flunk "cargo not on PATH"

PY="${PY:-python3}"
N="${N:-100}"
SEED="${SEED:-42}"
MODEL="${MODEL:-gpt-4o}"
RUNTIMES="vanilla"
[ "${1:-}" = "--table4" ] && RUNTIMES="vanilla pessimistic snapshot_isolation"
STAMP="${STAMP:-$(date -u +%Y%m%dT%H%MZ)}"
RUN="runs/$STAMP"
mkdir -p "$RUN"

say "building the verified detector"
(cd rust-analyser && cargo build --release -q) || flunk "rust-analyser failed to build"
ANALYSER="$PWD/rust-analyser/target/release/analyser"

for rt in $RUNTIMES; do
  for wl in edit-review plan-execute triage; do
    cell="$RUN/$wl-$rt"
    have=$( ( ls "$cell"/*.jsonl 2>/dev/null | wc -l ) || true )
    if [ "$have" -ge "$N" ]; then say "$wl/$rt: $have traces present, not regenerating"; continue; fi
    say "$wl/$rt: generating $N sessions on $MODEL (seed $SEED)"
    (cd python && $PY autogen_pilot.py --provider openai --model "$MODEL" --workload "$wl" \
        --runtime "$rt" --n "$N" --seed "$SEED" \
        --output "../$cell" --tokens-output "../$RUN/tokens-$wl-$rt") \
      || flunk "driver failed on $wl/$rt"
  done
done

say "scoring every trace with the verified detector -> $RUN/results.txt"
# Score ONLY the workload cells.  The token sidecars (tokens-*/ *.tokens.jsonl)
# are JSONL too and are not op-records; the first version of this script
# globbed them and the scorer died on the detector's parse error.
: > "$RUN/results.txt"
for rt in $RUNTIMES; do for wl in edit-review plan-execute triage; do
  for f in "$RUN/$wl-$rt"/*.jsonl; do
    { echo "=== FILE $f"; "$ANALYSER" "$f"; echo; } >> "$RUN/results.txt" 2>&1 \
      || flunk "detector failed on $f (see $RUN/results.txt)"
  done
done; done

$PY - "$RUN" "$ANALYSER" "$MODEL" "$SEED" <<'PYSCORE'
import sys, json, re, hashlib, subprocess, math
from pathlib import Path
from collections import defaultdict
run, analyser, model, seed = Path(sys.argv[1]), sys.argv[2], sys.argv[3], int(sys.argv[4])

def cp(k, n, a=0.05):
    if n == 0: return [0.0, 1.0]
    try:
        from scipy.stats import beta
        lo = 0.0 if k == 0 else float(beta.ppf(a/2, k, n-k+1)); hi = 1.0 if k == n else float(beta.ppf(1-a/2, k+1, n-k))
        return [lo, hi]
    except Exception:
        if k == 0: return [0.0, 3.0/n]
        if k == n: return [1-3.0/n, 1.0]
        p, z = k/n, 1.959964; d = 1+z*z/n; c = (p+z*z/(2*n))/d; r = z*math.sqrt(p*(1-p)/n+z*z/(4*n*n))/d
        return [max(0, c-r), min(1, c+r)]

blocks = open(run/"results.txt", encoding="utf-8").read().split("=== FILE ")[1:]
cells = defaultdict(lambda: {"n": 0, "a1_sessions": 0, "a1_occurrences": 0, "op_mismatch": 0})
mism = []
for b in blocks:
    path = Path(b.splitlines()[0].strip())
    m_ops = re.search(r"operations: (\d+)", b)
    m_a1 = re.search(r"A1 \(Stale-Generation\):\s+(\d+)", b)
    if not m_ops or not m_a1:
        print(f"FAIL: the detector produced no scorable output for {path}:", file=sys.stderr)
        print("\n".join("    " + l for l in b.splitlines()[1:6]), file=sys.stderr)
        sys.exit(1)
    ops_scored = int(m_ops.group(1))
    ops_file = sum(1 for l in path.read_text().splitlines() if l.strip())
    a1 = int(m_a1.group(1))
    key = path.parent.name
    c = cells[key]; c["n"] += 1; c["a1_occurrences"] += a1; c["a1_sessions"] += 1 if a1 > 0 else 0
    if ops_scored != ops_file:
        c["op_mismatch"] += 1; mism.append((str(path), ops_scored, ops_file))
for k, c in cells.items():
    c["a1_rate"] = c["a1_sessions"]/c["n"] if c["n"] else 0.0
    c["ci95"] = cp(c["a1_sessions"], c["n"])
sha = hashlib.sha256(open(analyser, "rb").read()).hexdigest()
git = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip() or "unknown"
(run/"summary.json").write_text(json.dumps({"cells": dict(cells), "predicate": "Definition 1 (rust-analyser detect_a1)"}, indent=2))
(run/"manifest.json").write_text(json.dumps({"model": model, "seed": seed, "provider": "openai",
    "pilot_git_sha": git, "analyser_sha256": sha, "n_traces": len(blocks)}, indent=2))
print(f"  scored {len(blocks)} traces; op-count mismatches: {len(mism)}")
for k in sorted(cells):
    c = cells[k]; print(f"  {k:32s} A1 sessions {c['a1_sessions']}/{c['n']}  CI95 [{c['ci95'][0]:.3f},{c['ci95'][1]:.3f}]  occurrences {c['a1_occurrences']}")
if mism:
    print("MISMATCHES:", mism[:5], file=sys.stderr); sys.exit(1)
PYSCORE

echo "verifying:"
fails=0
for rt in $RUNTIMES; do for wl in edit-review plan-execute triage; do
  c=$( ( ls "$RUN/$wl-$rt"/*.jsonl 2>/dev/null | wc -l ) || true )
  if [ "$c" -ne "$N" ]; then say "WRONG COUNT ($c, expected $N): $wl-$rt"; fails=$((fails+1)); else say "$wl-$rt: $N traces"; fi
done; done
[ -s "$RUN/summary.json" ]  && say "summary.json written"  || { say "MISSING summary.json";  fails=$((fails+1)); }
[ -s "$RUN/manifest.json" ] && say "manifest.json written" || { say "MISSING manifest.json"; fails=$((fails+1)); }
[ "$fails" -eq 0 ] || flunk "$fails verification check(s) failed"
echo "round 5 (pilot) complete: commit $RUN and send summary.json back for the Table 3/4 update."
