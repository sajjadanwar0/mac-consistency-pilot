#!/usr/bin/env bash
# verus_count.sh — compute the DISTINCT Verus obligation total for the
# mac-consistency verus-detector crate, transparently and reproducibly.
#
# Why this exists:
#   `verus` reports "N verified" per file. Summing per-file counts DOUBLE-COUNTS
#   any obligation that one file re-verifies from another:
#     - `mod`-based re-inclusion: lib_consistency_lattice.rs declares
#         `pub mod lib_l2_safety; lib_l3_safety; lib_l4_safety;`
#       so its standalone count already contains L2+L3+L4.
#     - textual re-inclusion: lib_l2_exec.rs copies the L2 model inline
#       (49 = 27 net + the 22-obligation L2 model), so it re-counts L2 safety.
#   The paper's headline "distinct obligations" figure removes those overlaps.
#   This script measures every file, subtracts each re-included child's count
#   ONCE per re-inclusion edge, and prints the arithmetic so the total is
#   auditable rather than asserted.
#
# 2026-06-11 note: lib_occ_l2_refinement.rs (OCC/ETag L1->L2 channel
#   refinement, paper sec 6.5; live-confirmed 8 verified, 0 errors) is restored
#   to the crate and is a COUNTED file — it is cited with a verified count in
#   the paper, so it must appear in the totals, not in EXCLUDE. Its inclusion
#   shifts the printed totals relative to pre-restoration runs (expected:
#   curated 250 -> 258, full 271 -> 279). As always, the figures below are
#   whatever the live run prints, and the paper headline MUST be reconciled
#   to that printed DISTINCT total (not the other way around).
#
# 2026-06-12 note: lib_l3_exec.rs (exec-mode L3 sequencer; live-confirmed
#   7 verified) and lib_l4_exec.rs (exec-mode L4 snapshot discipline;
#   live-confirmed 9 verified) are new COUNTED files. Both are deliberately
#   self-contained (no `mod`, no textual re-inclusion of any model file), so
#   they add to both totals with no re-inclusion edge (expected shift:
#   curated 258 -> 274, full 279 -> 295 -- but the live printed totals are
#   the authority, as always). They are cited contributions (the exec
#   realizations of lattice points L3 and L4) and must NOT be added to
#   EXCLUDE, unlike the non-headline exec *helpers* listed there.
#
# Usage:
#   ./verus_count.sh                 # clone the pilot repo, count (curated total)
#   ./verus_count.sh --full          # empty EXCLUDE: full distinct total
#   ./verus_count.sh --local=DIR     # count DIR/mac-consistency-pilot/verus-detector
#   VERUS=/path/to/verus ./verus_count.sh
#
# Output: a per-file table, the raw sum, every re-inclusion subtraction, and
#   the distinct total. Files with verification errors are flagged and the
#   total is marked INCOMPLETE.

set -uo pipefail   # deliberately NOT -e: we continue past per-file errors

GITHUB_USER="sajjadanwar0"
VERUS="${VERUS:-verus}"
LOCAL_BASE=""
FULL=0
for arg in "$@"; do
    case "$arg" in
        --local=*) LOCAL_BASE="${arg#*=}" ;;
        --full|--include-all) FULL=1 ;;   # clear EXCLUDE: compute the full distinct total
        --help|-h) sed -n '2,/^set -u/p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    esac
done

# Declared TEXTUAL re-inclusions: "parent.rs:child.rs" — parent copies child's
# obligations inline (not via `mod`). `mod` re-inclusions are auto-detected.
# Add a line here only if you confirm a file inlines another file's model.
# (lib_occ_l2_refinement.rs is self-contained: no mod or textual re-inclusion.)
TEXTUAL_REINCLUSION=(
  "lib_l2_exec.rs:lib_l2_safety.rs"   # l2_exec inlines the 22-obligation L2 model
)

# Files with NO countable obligations (exec/test scaffolding). ALWAYS skipped,
# in both curated and --full modes, because `verus` prints no "N verified"
# summary for them and counting them would mark the run INCOMPLETE.
NEVER_COUNT=(
  "verified_a1.rs"                 # exec/test file, no proof obligations
)

# Files to EXCLUDE from the CURATED total only (they DO verify, but are not
# headline lattice points). --full empties this list; NEVER_COUNT files stay
# skipped regardless. NOTE: entries for files no longer in the repo (e.g. the
# removed probabilistic development) are harmless no-ops. Do NOT add
# lib_occ_l2_refinement.rs, lib_l3_exec.rs, or lib_l4_exec.rs here: they are
# cited contributions (paper sec 6.5; exec realizations of L3 and L4) and
# must be counted in both modes.
EXCLUDE=(
  "lib_probabilistic_a1.rs"        # superseded probabilistic v1 (if present)
  "lib_probabilistic_a1_v2.rs"     # demoted probabilistic v2 screen (if present)
  "lib_detect_a1_exec.rs"          # exec helper, not a headline lattice contribution
  "lib_pessimistic_exec.rs"        # exec helper
  "lib_pessimistic_invariant.rs"   # invariant helper
  "lib_si_commit_invariant.rs"     # invariant helper
)
# The curated total subtracts the EXCLUDE files' obligations from the full
# total; --full reports the full total. The exact figures are whatever the
# live run prints below, and the paper's headline MUST be reconciled to that
# printed DISTINCT total (not the other way around).

# --full / --include-all empties EXCLUDE to compute the full distinct total.
[ "${FULL:-0}" -eq 1 ] && EXCLUDE=()

log()  { printf "\033[1;34m%s\033[0m\n" "$*"; }
ok()   { printf "  \033[1;32m\xe2\x9c\x93\033[0m %s\n" "$*"; }
warn() { printf "  \033[1;33m\xe2\x97\x8b\033[0m %s\n" "$*"; }
err()  { printf "  \033[1;31m\xe2\x9c\x97\033[0m %s\n" "$*"; }
have() { command -v "$1" >/dev/null 2>&1; }

if [ -n "$LOCAL_BASE" ]; then
    VDET="$LOCAL_BASE/mac-consistency-pilot/verus-detector"
else
    WORK="$(pwd)/verus-count-clone"; mkdir -p "$WORK"; cd "$WORK"
    # Always refresh: a cached clone from a previous run would mask pushed
    # changes (a stale cache is why a re-run could keep showing an old total).
    rm -rf mac-consistency-pilot
    git clone --quiet --depth=1 \
        "https://github.com/$GITHUB_USER/mac-consistency-pilot.git"
    VDET="$WORK/mac-consistency-pilot/verus-detector"
fi

[ -d "$VDET/src" ] || { echo "verus-detector/src not found at $VDET" >&2; exit 1; }
have "$VERUS" || { echo "verus not on PATH (set VERUS=)" >&2; exit 1; }

cd "$VDET"
declare -A COUNT       # basename -> verified count (only when 0 errors)
declare -A STATUS      # basename -> ok|ERR
INCOMPLETE=0

log "Verifying every src/*.rs standalone (verus --crate-type=lib)"
shopt -s nullglob
FILES=()
for path in src/*.rs; do FILES+=("$(basename "$path")"); done
IFS=$'\n' FILES=($(printf '%s\n' "${FILES[@]}" | sort)); unset IFS

is_excluded()    { local x; for x in "${EXCLUDE[@]:-}";    do [ "$x" = "$1" ] && return 0; done; return 1; }
is_never_count() { local x; for x in "${NEVER_COUNT[@]:-}"; do [ "$x" = "$1" ] && return 0; done; return 1; }

for f in "${FILES[@]}"; do
    if is_never_count "$f"; then
        printf "  \033[2m(no obligations) %-24s\033[0m\n" "$f"
        continue
    fi
    if is_excluded "$f"; then
        printf "  \033[2m(excluded) %-30s\033[0m\n" "$f"
        continue
    fi
    out="$("$VERUS" --crate-type=lib "src/$f" 2>&1 || true)"
    line="$(echo "$out" | grep -Eo '[0-9]+ verified, [0-9]+ errors?' | tail -1)"
    if [ -z "$line" ]; then
        STATUS[$f]="ERR"; INCOMPLETE=1; err "$f: no verification summary"
        continue
    fi
    v="$(echo "$line" | grep -Eo '^[0-9]+')"
    e="$(echo "$line" | grep -Eo '[0-9]+ error' | grep -Eo '^[0-9]+')"
    if [ "${e:-1}" -ne 0 ]; then
        STATUS[$f]="ERR"; INCOMPLETE=1; err "$f: $line"
    else
        COUNT[$f]="$v"; STATUS[$f]="ok"
        printf "  %-34s %s verified\n" "$f" "$v"
    fi
done

echo
log "Re-inclusion edges (subtracted once each from the raw sum)"
# Auto-detect `mod` re-inclusions: parent declares `pub mod child;`
EDGES=()
for f in "${FILES[@]}"; do
    [ "${STATUS[$f]:-}" = "ok" ] || continue
    while read -r m; do
        [ -n "$m" ] || continue
        child="$m.rs"
        if [ -n "${COUNT[$child]:-}" ]; then EDGES+=("$f:$child:mod"); fi
    done < <(grep -oE '(pub +)?mod +[a-z0-9_]+ *;' "src/$f" | grep -oE '[a-z0-9_]+ *;' | tr -d ' ;')
done
# Declared textual re-inclusions
for rel in "${TEXTUAL_REINCLUSION[@]}"; do
    p="${rel%%:*}"; c="${rel##*:}"
    [ "${STATUS[$p]:-}" = "ok" ] && [ -n "${COUNT[$c]:-}" ] && EDGES+=("$p:$c:textual")
done

REINCLUDED=0
if [ "${#EDGES[@]}" -eq 0 ]; then
    warn "none detected"
else
    for edge in "${EDGES[@]}"; do
        p="${edge%%:*}"; rest="${edge#*:}"; c="${rest%%:*}"; kind="${rest##*:}"
        n="${COUNT[$c]}"
        REINCLUDED=$((REINCLUDED + n))
        printf "  %-34s re-includes %-26s -%s  (%s)\n" "$p" "$c" "$n" "$kind"
    done
fi

# Raw sum of counted (non-excluded) files
RAW=0
for f in "${FILES[@]}"; do
    [ "${STATUS[$f]:-}" = "ok" ] || continue
    RAW=$((RAW + COUNT[$f]))
done

DISTINCT=$((RAW - REINCLUDED))

echo
log "Totals"
printf "  raw per-file sum (counted files)      %s\n" "$RAW"
[ "${#EXCLUDE[@]}" -gt 0 ] && printf "  (%s file(s) excluded as superseded/helper — run --full for the full total)\n" "${#EXCLUDE[@]}"
printf "  re-included (double-counted) removed  -%s\n" "$REINCLUDED"
printf "  ------------------------------------------\n"
printf "  DISTINCT obligation total             %s\n" "$DISTINCT"
echo
if [ "$INCOMPLETE" -eq 1 ]; then
    err "One or more files failed to verify — DISTINCT total is INCOMPLETE."
    exit 1
fi
ok "All counted files verified at 0 errors."
echo "  This DISTINCT total = every counted obligation in the crate, with"
echo "  re-included (mod / textual) obligations removed once. The default run"
echo "  is the curated headline (EXCLUDE applied); --full is the full distinct"
echo "  total. This printed figure is authoritative: the paper headline must"
echo "  match it."