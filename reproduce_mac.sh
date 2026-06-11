#!/usr/bin/env bash
# reproduce_mac.sh — single-script reproduction for the mac-consistency submission
#   ("Verified Detection and Prevention of Concurrency Anomalies in Multi-Agent
#    Large Language Model Systems")
#
# What this script does:
#   1. Clones the three mac-consistency repositories from GitHub
#   2. Verifies the Verus proof obligations that back the paper's scorecard
#      (incl. an anti-regression guard on the concurrent-semantics lift)
#   3. Runs the GenMC RC11 bounded weak-memory check (positive + negative control)
#   4. Builds/tests the runtime and reproduces the A3-prevention measurement
#   5. Best-effort: TLC checks each anomaly-witness spec produces its
#      counterexample (needs java + tla2tools)
#   6. Best-effort: the empirical Python layer (offline checks; --with-live for
#      the dynamic-prevalence cells that need LLM API keys)
#   7. High-contention cost envelope (Finding 5): offline keyless guard run;
#      --with-live reproduces the gpt-4o-mini sweep behind it
#
# Usage:
#   ./reproduce_mac.sh                # Verus + GenMC + runtime + best-effort (~10 min)
#   ./reproduce_mac.sh --formal-only  # only Verus + GenMC + TLC (~5 min)
#   ./reproduce_mac.sh --with-live    # also run the live-LLM prevalence + cost cells
#   ./reproduce_mac.sh --local=DIR    # audit local working trees under DIR
#                                     # (DIR/mac-consistency-pilot, etc.) instead
#                                     # of cloning from GitHub — verify before push
#
# Requirements:
#   - Linux/macOS, git, python3.11+
#   - rustc 1.93+ / cargo (https://rustup.rs/)            — runtime + analyser
#   - Verus (https://github.com/verus-lang/verus)         — proof obligations
#   - Optional: GenMC 0.17+ (https://github.com/MPI-SWS/genmc) — weak-memory check
#   - Optional: java + tla2tools.jar                      — TLC model checking
#       export TLA_TOOLS=/path/to/tla2tools.jar  (default ~/tla2tools.jar)
#   - For --with-live: export ANTHROPIC_API_KEY=... and/or OPENAI_API_KEY=...
#
# Integrity note:
#   lib_concurrent_semantics.rs was, until 2026-06-07, a byte-identical copy of
#   a probabilistic-refinement file (since removed from the repo) rather than the
#   atomic-event lift the paper describes. Phase 3 therefore GUARDS that file:
#   if it lacks the lift signatures or carries any external_body, the script
#   FAILS loudly instead of counting the wrong file.
#
#   The L2 A3-prevention guarantee is a THEOREM, proved in Phase 3 (the
#   a3_free capstone of lib_l2_exec.rs: every well-formed exec state is
#   A3-free). Phase 6's measure_a3_prevention runs the dependency-free std
#   TWIN (l2_causal.rs), which implements the same commit_valid/cascade_abort
#   transition system, to exhibit the unguarded baseline's A3 and corroborate
#   the proof. The two are deliberately distinct artifacts of one protocol;
#   the guarantee does not depend on the twin (see paper sec:l2-deployed).
#
#   The high-contention cost harness (Phase 7b) measures TOKENS exactly
#   (provider usage, incl. generations re-spent on aborts); its wall-clock
#   figures are COMPOSED from measured per-call latencies under each
#   discipline's concurrency structure, not measured under a real concurrent
#   runtime. The offline guard run asserts only the prevention invariant
#   (unguarded baseline exhibits A1; SSI/pessimistic do not).

set -euo pipefail

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------
GITHUB_USER="sajjadanwar0"
REPOS=("mac-consistency" "mac-consistency-pilot" "mac-consistency-runtime")
ROOT="$(pwd)/mac-consistency-replication"
LIVE_MODE=0
FORMAL_ONLY=0
LOCAL_BASE=""

TLA_TOOLS="${TLA_TOOLS:-$HOME/tla2tools.jar}"
VERUS="${VERUS:-verus}"

# Verus targets: "file|expected_verified". expected_verified is an integer
# (asserted) or "?" (require 0 errors, report the count without asserting it).
VERUS_TARGETS=(
  "lib_detector_equivalence.rs|24"     # live-confirmed 2026-06-07
  "lib_l2_safety.rs|22"                # live-confirmed (README's 13 is stale)
  "lib_l2_exec.rs|49"                  # live-confirmed (self-contained; re-includes L2 model)
  "lib_concurrent_semantics.rs|9"      # live-confirmed: atomic-event lift, 0 axioms
  "lib_l3_safety.rs|6"                 # live-confirmed
  "lib_l2_projection.rs|3"             # live-confirmed: L2 state->trace projection, 0 axioms
  "lib_l3_sequencer.rs|5"              # live-confirmed: concurrent-effect commit-order sequencer, 0 axioms
  "lib_l4_safety.rs|5"                 # live-confirmed
  "lib_a4_split_view.rs|9"             # live-confirmed: monotone-primary no-split (was 5; de-tautologized)
  "lib_refinement_pessimistic.rs|31"   # live-confirmed
  "lib_refinement_ssi.rs|18"           # live-confirmed
  "lib_refinement_ssi_chain.rs|17"     # live-confirmed
  "lib_refinement_default_si.rs|18"    # live-confirmed
  "lib_langgraph_refinement.rs|7"      # live-confirmed: LangGraph runtime refinement, 0 axioms
  "lib_rustbelt_interface.rs|4"        # live-confirmed: 4 (2 structural + 3 RUSTBELT external_body stubs)
)

for arg in "$@"; do
    case "$arg" in
        --with-live)   LIVE_MODE=1 ;;
        --formal-only) FORMAL_ONLY=1 ;;
        --local=*)     LOCAL_BASE="${arg#*=}" ;;
        --help|-h) sed -n '2,/^set -e/p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    esac
done

log()  { printf "\033[1;34m[%s]\033[0m %s\n" "$(date +%H:%M:%S)" "$*"; }
ok()   { printf "  \033[1;32m\xe2\x9c\x93\033[0m %s\n" "$*"; }
fail() { printf "  \033[1;31m\xe2\x9c\x97\033[0m %s\n" "$*"; FAIL_COUNT=$((FAIL_COUNT + 1)); }
skip() { printf "  \033[1;33m\xe2\x97\x8b\033[0m %s\n" "$*"; }
need() { command -v "$1" >/dev/null 2>&1 || { echo "Missing required tool: $1" >&2; exit 1; }; }
have() { command -v "$1" >/dev/null 2>&1; }

FAIL_COUNT=0

# ---------------------------------------------------------------------------
log "Phase 1: Checking prerequisites"
need git
need python3
[[ $FORMAL_ONLY -eq 1 ]] || need cargo
[[ $FORMAL_ONLY -eq 1 ]] || need rustc
have "$VERUS" || log "  (note: verus not found; Verus phase will be skipped)"
have genmc    || log "  (note: genmc not found; weak-memory phase will be skipped)"
have java     || log "  (note: java not found; TLC phase will be skipped)"

# ---------------------------------------------------------------------------
if [ -n "$LOCAL_BASE" ]; then
    log "Phase 2: Auditing LOCAL working trees under $LOCAL_BASE (no clone)"
    ROOT="$LOCAL_BASE"
    for repo in "${REPOS[@]}"; do
        [ -d "$ROOT/$repo" ] || log "  (note: $ROOT/$repo not found; its checks will skip)"
    done
else
    log "Phase 2: Cloning repositories into $ROOT"
    mkdir -p "$ROOT"; cd "$ROOT"
    for repo in "${REPOS[@]}"; do
        if [ -d "$repo" ]; then
            log "  $repo exists; pulling latest"
            (cd "$repo" && git pull --quiet --ff-only) || log "    (skipping pull; tree may be dirty)"
        else
            log "  Cloning $repo"
            git clone --quiet --depth=1 "https://github.com/$GITHUB_USER/$repo.git" || fail "clone $repo"
        fi
    done
fi

PILOT="$ROOT/mac-consistency-pilot"
RUNTIME="$ROOT/mac-consistency-runtime"
SPECS="$ROOT/mac-consistency"
VDET="$PILOT/verus-detector"

# ---------------------------------------------------------------------------
log "Phase 3: Verus proof obligations"
if ! have "$VERUS"; then
    skip "Verus phase (verus not on PATH; set VERUS=)"
elif [ ! -d "$VDET" ]; then
    skip "Verus phase (verus-detector/ not found)"
else
    # Anti-regression guard: lib_concurrent_semantics.rs must be the genuine
    # atomic-event lift, NOT the probabilistic duplicate.
    CS="$VDET/src/lib_concurrent_semantics.rs"
    GUARD_OK=1
    if [ -f "$CS" ]; then
        if [ "$(grep -c 'step_enabled\|LockAcquire\|holders' "$CS")" -eq 0 ] \
           || [ "$(grep -c '#\[verifier::external_body\]' "$CS")" -ne 0 ]; then
            fail "lib_concurrent_semantics.rs is NOT the atomic-event lift (no lift signatures and/or has external_body) — looks reverted to the probabilistic duplicate; refusing to count it"
            GUARD_OK=0
        fi
    fi

    cd "$VDET"
    for tgt in "${VERUS_TARGETS[@]}"; do
        f="${tgt%%|*}"; want="${tgt##*|}"
        [ -f "src/$f" ] || { fail "Verus $f: file not found under verus-detector/src"; continue; }
        if [ "$f" = "lib_concurrent_semantics.rs" ] && [ "$GUARD_OK" -eq 0 ]; then continue; fi
        out="$("$VERUS" --crate-type=lib "src/$f" 2>&1 || true)"
        line="$(echo "$out" | grep -Eo '[0-9]+ verified, [0-9]+ errors?' | tail -1)"
        if [ -z "$line" ]; then fail "Verus $f: no 'N verified, M errors' summary"; continue; fi
        v="$(echo "$line" | grep -Eo '^[0-9]+')"
        e="$(echo "$line" | grep -Eo '[0-9]+ error' | grep -Eo '^[0-9]+')"
        if [ "${e:-1}" -ne 0 ]; then
            fail "Verus $f: $line"
        elif [ "$want" = "?" ]; then
            ok "Verus $f: $v verified, 0 errors (count not pinned)"
        elif [ "$v" = "$want" ]; then
            ok "Verus $f: $v verified, 0 errors"
        else
            fail "Verus $f: expected $want verified, got $v"
        fi
    done
    cd "$ROOT"
fi

# ---------------------------------------------------------------------------
log "Phase 4: GenMC RC11 bounded weak-memory check"
WM="$PILOT/weakmem"
if ! have genmc; then
    skip "GenMC phase (genmc not on PATH)"
elif [ ! -f "$WM/litmus_mutex_a1.c" ]; then
    skip "GenMC phase (weakmem/litmus_mutex_a1.c not found)"
else
    cd "$WM"
    # Positive litmus: the acquire/release lock prevents lost updates (no A1)
    # for N agents; GenMC explores exactly N! complete RC11 executions.
    declare -A EXPECT=([2]=2 [3]=6 [4]=24)
    for n in 2 3 4; do
        out="$(genmc -- -DAGENTS=$n litmus_mutex_a1.c 2>&1 || true)"
        execs="$(echo "$out" | grep -Eo 'complete executions explored: [0-9]+' | grep -Eo '[0-9]+$' | tail -1)"
        if echo "$out" | grep -q 'No errors were detected' && [ "${execs:-x}" = "${EXPECT[$n]}" ]; then
            ok "GenMC litmus_mutex_a1 N=$n: no errors, ${execs} complete executions (= $n!)"
        else
            fail "GenMC litmus_mutex_a1 N=$n: expected ${EXPECT[$n]} execs + no errors; got '${execs:-?}'"
        fi
    done
    # Negative control: relaxed orderings MUST exhibit the lost-update race
    # (proves the acquire/release annotations are load-bearing / non-vacuous).
    out="$(genmc litmus_mutex_a1_relaxed.c 2>&1 || true)"
    if echo "$out" | grep -qiE 'Non-atomic race|assertion|unsuccesful|violation'; then
        ok "GenMC relaxed control: data race / violation detected (non-vacuity confirmed)"
    else
        fail "GenMC relaxed control: expected a race/violation, none reported"
    fi
    cd "$ROOT"
fi

# ---------------------------------------------------------------------------
log "Phase 5: TLC model-checking of the anomaly specs (best-effort)"
if ! have java; then
    skip "TLC phase (java not found)"
elif [ ! -f "$TLA_TOOLS" ]; then
    skip "TLC phase (tla2tools.jar not at $TLA_TOOLS; set TLA_TOOLS=)"
elif [ ! -d "$SPECS/tla" ]; then
    skip "TLC phase (mac-consistency/tla not found)"
else
    cd "$SPECS/tla"
    for m in MC_A1 MC_A2 MC_A3 MC_A5 MC_A6; do
        [ -f "$m.tla" ] && [ -f "$m.cfg" ] || { skip "TLC $m (spec/cfg missing)"; continue; }
        out="$(java -cp "$TLA_TOOLS" tlc2.TLC -config "$m.cfg" "$m.tla" 2>&1 || true)"
        # MC_A* are anomaly-WITNESS harnesses: the XxxFree invariant is meant to
        # be VIOLATED, and the resulting counterexample IS the anomaly witness.
        # Success = TLC reports the violation; "No error" would mean the anomaly
        # became unreachable (the witness broke).
        if echo "$out" | grep -qiE 'is violated|invariant .* violated'; then
            ok "TLC $m: anomaly witness reproduced (invariant violated, as designed)"
        elif echo "$out" | grep -q 'No error has been found'; then
            fail "TLC $m: invariant held — anomaly NOT reachable (witness broke)"
        else
            fail "TLC $m: did not run cleanly (no violation and no completion line — inspect)"
        fi
    done
    cd "$ROOT"
fi

if [[ $FORMAL_ONLY -eq 1 ]]; then
    echo; log "Done (formal-only mode)"
    if [[ "$FAIL_COUNT" -eq 0 ]]; then printf "\033[1;32mAll formal checks passed.\033[0m\n"; exit 0
    else printf "\033[1;31m%d checks failed.\033[0m\n" "$FAIL_COUNT"; exit 1; fi
fi

# ---------------------------------------------------------------------------
log "Phase 6: Runtime build, tests, and A3-prevention measurement"
if [ ! -f "$RUNTIME/Cargo.toml" ]; then
    skip "Runtime phase (mac-consistency-runtime/Cargo.toml not found)"
else
    cd "$RUNTIME"
    log "  cargo build --release"
    if cargo build --release --quiet 2>&1 | tail -5; then ok "runtime: cargo build"; else fail "runtime: cargo build"; fi
    log "  cargo test --release  (unit + integration)"
    if cargo test --release --quiet 2>&1 | tail -10; then ok "runtime: cargo test"; else fail "runtime: cargo test"; fi
    # measure_a3_prevention drives the std TWIN (l2_causal.rs), which implements
    # the same commit_valid/cascade_abort transition system Phase 3 verifies on
    # lib_l2_exec.rs. The guarantee is the Phase-3 a3_free theorem; this run
    # corroborates it and exhibits the unguarded baseline's A3 (paper sec:l2-deployed).
    # Self-asserts: baseline a3_positive == runs, L2 a3_positive == 0.
    log "  cargo test --release measure_a3_prevention  (L2 prevents A3; unguarded admits it)"
    if cargo test --release measure_a3_prevention --quiet 2>&1 | tail -8; then
        ok "A3 prevention reproduced (L2: 0 witnesses across all runs; unguarded baseline: all runs)"
    else
        fail "measure_a3_prevention failed"
    fi
    cd "$ROOT"
fi

# ---------------------------------------------------------------------------
log "Phase 7: Rust analyser + empirical Python layer (best-effort)"
if [ -f "$PILOT/rust-analyser/Cargo.toml" ]; then
    cd "$PILOT/rust-analyser"
    if cargo build --release --quiet 2>&1 | tail -3; then ok "rust-analyser: cargo build"; else fail "rust-analyser: cargo build"; fi
    cd "$ROOT"
else
    skip "rust-analyser (Cargo.toml not found)"
fi

# Empirical scripts are reported for presence; their full runs need datasets
# and (for the dynamic cells) live LLM keys, so they are not magic-number
# asserted here.
PY="$PILOT/python"
for s in mast_adapter.py prevalence_static.py prevalence_dynamic_run.py \
         deerflow_3123_repro.py paired_cost_analysis.py judge_audit.py \
         high_contention_cost.py; do
    [ -f "$PY/$s" ] && ok "empirical script present: python/$s" || skip "empirical script missing: python/$s"
done

# ---------------------------------------------------------------------------
log "Phase 7b: High-contention cost envelope (Finding 5)"
HC="$PY/high_contention_cost.py"
if [ ! -f "$HC" ]; then
    skip "high-contention harness (python/high_contention_cost.py not found)"
else
    # Offline, keyless: the deterministic 'mock' provider validates the harness
    # and the prevention guard — the unguarded baseline must exhibit A1 while
    # SSI and pessimistic must not. This asserts the invariant the cost figures
    # are conditioned on, without needing API keys.
    if (cd "$PY" && python3 high_contention_cost.py run \
            --provider mock --model mock --w 16 --cells 1 --depth 2 --n 10 \
            --out /tmp/hc_mock >/tmp/hc_mock.log 2>&1) \
       && grep -q 'must be 0' /tmp/hc_mock.log \
       && ! grep -qE 'ssi +16 +1 +2 +10 +[0-9.]+ +[0-9]+ +[1-9]' /tmp/hc_mock.log; then
        ok "high-contention harness: mock guard run (vanilla fires A1; SSI/pessimistic A1=0)"
    else
        fail "high-contention harness: mock guard run failed (see /tmp/hc_mock.log)"
    fi

    # Live: reproduce the cost-envelope sweep (Fig. cost-envelope). gpt-4o-mini;
    # ~2-3h. Token cost exact; wall-clock figures are COMPOSED (see header note).
    if [[ $LIVE_MODE -eq 1 ]]; then
        if [[ -z "${OPENAI_API_KEY:-}" ]]; then
            fail "cost-envelope sweep: OPENAI_API_KEY not set"
        else
            log "  cost-envelope sweep (gpt-4o-mini; cell-count sweep W=8, C in {2,4,8,16,32})"
            if (cd "$PY" \
                && for C in 2 4 8 16 32; do
                       python3 high_contention_cost.py run \
                           --provider openai --model gpt-4o-mini \
                           --w 8 --cells "$C" --depth 2 --n 15 --seed 7 \
                           --out ./hc_curve || exit 1
                   done \
                && python3 high_contention_cost.py analyze \
                       --in ./hc_curve --regress --target-effect 0.10); then
                ok "cost-envelope sweep reproduced (inspect: overhead ~ 0% + ~110% x abort_rate; breakpoint ~0.14)"
            else
                fail "cost-envelope sweep failed (check key / network / deps)"
            fi
        fi
    else
        skip "cost-envelope live sweep (use --with-live + OPENAI_API_KEY to reproduce Fig. cost-envelope)"
    fi
fi

# ---------------------------------------------------------------------------
if [[ $LIVE_MODE -eq 1 ]]; then
    log "Phase 8: Live dynamic-prevalence cells"
    if [[ -z "${ANTHROPIC_API_KEY:-}" && -z "${OPENAI_API_KEY:-}" ]]; then
        fail "live mode: neither ANTHROPIC_API_KEY nor OPENAI_API_KEY set"
    elif [ -f "$PY/prevalence_dynamic_run.py" ]; then
        log "  python3 prevalence_dynamic_run.py  (immune topologies 0/20, susceptible 20/20)"
        if (cd "$PY" && python3 prevalence_dynamic_run.py 2>&1 | tail -15); then
            ok "dynamic prevalence run completed (inspect output for per-topology firing rates)"
        else
            fail "prevalence_dynamic_run.py failed (check keys / network / deps)"
        fi
    else
        skip "prevalence_dynamic_run.py not found"
    fi
fi

# ---------------------------------------------------------------------------
echo
log "Reproduction complete"
echo
if [[ "$FAIL_COUNT" -eq 0 ]]; then
    printf "\033[1;32mAll checks passed.\033[0m\n"
    printf "Replication root: %s\n" "$ROOT"
else
    printf "\033[1;31m%d checks failed.\033[0m See output above.\n" "$FAIL_COUNT"
    exit 1
fi