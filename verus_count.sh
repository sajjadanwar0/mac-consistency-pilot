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
#   Re-inclusion detection (two kinds, see EDGES below):
#     - `mod` edges are detected STRUCTURALLY (a `pub mod child;` declaration).
#     - textual (inline-copy) edges CANNOT be detected structurally, so each is
#       declared either by a `//@ reinclude-textual: <child>.rs` marker comment
#       in the parent source (preferred; auto-detected) or by a manual entry in
#       TEXTUAL_REINCLUSION (fallback). All edges are de-duplicated by
#       parent:child, so an edge declared both ways is still subtracted once.
#   CAVEAT: the DISTINCT total is sound only if every textual re-inclusion is
#   declared one of those two ways. An UNdeclared inline copy of another file's
#   model would silently OVER-count. Treat a new file that pastes a model in
#   as requiring a marker.
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
# 2026-09-13 note: lib_si_concurrent.rs (the deployed snapshot-isolation store
#   over vstd's verified reader-writer lock) and lib_pess_concurrent.rs (the
#   deployed pessimistic store over the same lock) are new COUNTED files. Both
#   are self-contained (no `mod`, no textual re-inclusion), so they add to both
#   totals with no re-inclusion edge. They are cited contributions -- the
#   deployed critical sections of the two guarded runtimes -- and must NOT be
#   added to EXCLUDE. The live printed totals remain the authority.
#
# 2026-09-13 note (round 20): this script used to COUNT A FRESH GITHUB CLONE by
#   default while printing "This printed figure is authoritative". A file that
#   verifies in the working tree but has not been pushed was therefore invisible
#   to it, with no warning: on 13 Sep it reported 274/295 while
#   lib_si_concurrent.rs (18 verified) and lib_pess_concurrent.rs (31 verified)
#   sat in the checkout, unpushed and uncounted. The default is now the LOCAL
#   working tree; the clone is opt-in via --from-github. Whichever tree is
#   measured, the script prints its path and git revision, and when it counts a
#   clone it DIFFS the clone's file list against the local tree and fails if the
#   local tree has a src/*.rs the clone does not.
#
# 2026-09-15 note (round 22): the pin moved to 0.2026.09.13.671956e in round 21.
#   In a shell whose `verus` was still the old build, a plain `./verus_count.sh
#   --full` then printed the mismatch banner and an INCOMPLETE 169, because the
#   ten migrated files cannot compile under the old vstd. When VERUS is not set
#   and `verus` on PATH is not the pinned version, the script now looks for the
#   pinned build under ~/.local/opt (*/verus, */*/verus), checks each
#   candidate's --version, and uses the first that matches, saying so.
#   VERUS=... is honoured exactly as given, and with no matching build the
#   banner is unchanged. Under the pin, round 21 measured curated 331 -> 338 and
#   full 352 -> 359 (lib_l2_exec.rs 54 -> 59, lib_refinement_ssi_chain.rs
#   17 -> 19; lib_ssi.rs migrated, still 8).
#
# Usage:
#   ./verus_count.sh                 # count the LOCAL verus-detector (curated total)
#   ./verus_count.sh --full          # empty EXCLUDE: full distinct total
#   ./verus_count.sh --from-github   # count a fresh clone instead (opt-in)
#   ./verus_count.sh --local=DIR     # count DIR/mac-consistency-pilot/verus-detector
#   VERUS=/path/to/verus ./verus_count.sh
#
# Output: a per-file table, the raw sum, every re-inclusion subtraction, and
#   the distinct total. Files with verification errors are flagged and the
#   total is marked INCOMPLETE.

set -uo pipefail   # deliberately NOT -e: we continue past per-file errors

GITHUB_USER="sajjadanwar0"
VERUS_EXPLICIT="${VERUS:+1}"   # VERUS=... is honoured exactly as given
VERUS="${VERUS:-verus}"
LOCAL_BASE=""
FULL=0
FROM_GITHUB=0
HERE="$(cd "$(dirname "$0")" && pwd)"
for arg in "$@"; do
    case "$arg" in
        --local=*) LOCAL_BASE="${arg#*=}" ;;
        --from-github) FROM_GITHUB=1 ;;   # opt in to counting a fresh clone
        --full|--include-all) FULL=1 ;;   # clear EXCLUDE: compute the full distinct total
        --help|-h) sed -n '2,/^set -u/p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    esac
done

# Declared TEXTUAL re-inclusions (manual fallback list): "parent.rs:child.rs" --
# parent copies child's obligations inline (not via `mod`), which cannot be
# detected structurally. PREFER declaring the edge with a marker comment in the
# parent source instead:
#     //@ reinclude-textual: <child>.rs
# Markers are auto-detected below and merged with this list; the two are
# de-duplicated by parent:child, so declaring an edge both ways subtracts it
# once. Add an entry/marker only if you confirm the file inlines another file's
# model. (lib_l3_exec.rs, lib_l4_exec.rs, lib_occ_l2_refinement.rs are
# self-contained: no mod, no textual re-inclusion.)
TEXTUAL_REINCLUSION=(
  "lib_l2_exec.rs:lib_l2_safety.rs"   # l2_exec inlines the 22-obligation L2 model
                                      # (recommended: also add the //@ marker to that file)
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

LOCAL_VDET="$HERE/verus-detector"
if [ -n "$LOCAL_BASE" ]; then
    VDET="$LOCAL_BASE/mac-consistency-pilot/verus-detector"
    SOURCE="explicit --local: $VDET"
elif [ "$FROM_GITHUB" -eq 1 ]; then
    WORK="$HERE/verus-count-clone"; mkdir -p "$WORK"
    rm -rf "$WORK/mac-consistency-pilot"
    ( cd "$WORK" && git clone --quiet --depth=1 \
        "https://github.com/$GITHUB_USER/mac-consistency-pilot.git" )
    VDET="$WORK/mac-consistency-pilot/verus-detector"
    SOURCE="fresh clone of github.com/$GITHUB_USER/mac-consistency-pilot"
    # A clone can only show what was pushed.  Refuse to report a total from a
    # tree that is missing a file the local checkout has.
    if [ -d "$LOCAL_VDET/src" ]; then
        missing=""
        for p in "$LOCAL_VDET"/src/*.rs; do
            b="$(basename "$p")"
            [ -f "$VDET/src/$b" ] || missing="$missing $b"
        done
        if [ -n "$missing" ]; then
            printf "\033[1;31m  ✗\033[0m the clone is missing src file(s) present locally:%s\n" "$missing" >&2
            echo "    Push them, or run without --from-github to count the local tree." >&2
            exit 1
        fi
    fi
else
    VDET="$LOCAL_VDET"
    SOURCE="local working tree: $VDET"
fi

[ -d "$VDET/src" ] || { echo "verus-detector/src not found at $VDET" >&2; exit 1; }

# ---- which verus (round 22) ------------------------------------------
# The pin names a version; PATH names whatever was installed last. Unless
# VERUS is given, a PATH verus that is not the pinned version is replaced by the
# first build under ~/.local/opt whose --version is the pinned one.
ver_of() { "$1" --version 2>/dev/null | grep -oE 'Version:[[:space:]]*\S+' | head -1 | sed -E 's/.*:[[:space:]]*//'; }
PINFILE="$VDET/verus-version.txt"
PIN_WANT=""
[ -f "$PINFILE" ] && PIN_WANT="$(grep -oE '^verus[[:space:]]*=[[:space:]]*\S+' "$PINFILE" | head -1 | sed -E 's/.*=[[:space:]]*//')"
if [ -z "$VERUS_EXPLICIT" ] && [ -n "$PIN_WANT" ] && [ "$(ver_of "$VERUS")" != "$PIN_WANT" ]; then
    shopt -s nullglob
    for cand in "$HOME"/.local/opt/*/verus "$HOME"/.local/opt/*/*/verus; do
        [ -f "$cand" ] && [ -x "$cand" ] || continue
        if [ "$(ver_of "$cand")" = "$PIN_WANT" ]; then
            printf "  verus on PATH is not the pinned %s; using %s\n" "$PIN_WANT" "$cand"
            VERUS="$cand"
            break
        fi
    done
    shopt -u nullglob
fi
have "$VERUS" || { echo "verus not on PATH (set VERUS=)" >&2; exit 1; }

# ---- toolchain pin -------------------------------------------------
# These proofs are checked against a SPECIFIC Verus build. vstd's API moves,
# and a newer verifier makes files stop COMPILING (E0308 and friends) rather
# than makes a proof fail -- which surfaces as "no verification summary" on
# ten files and an INCOMPLETE total, with nothing to say the cause is the
# toolchain. Observed 2026-09-14: 0.2026.09.13 turns the 331 into 148.
# verus-version.txt records the build the headline was measured with; a
# mismatch is a loud warning, never a silent wrong number.
if [ -f "$PINFILE" ]; then
    PIN_VER="$(grep -oE '^verus[[:space:]]*=[[:space:]]*\S+' "$PINFILE" | head -1 | sed -E 's/.*=[[:space:]]*//')"
    PIN_TC="$(grep -oE '^toolchain[[:space:]]*=[[:space:]]*\S+' "$PINFILE" | head -1 | sed -E 's/.*=[[:space:]]*//')"
    GOT_VER="$("$VERUS" --version 2>/dev/null | grep -oE 'Version:[[:space:]]*\S+' | sed -E 's/.*:[[:space:]]*//')"
    GOT_TC="$("$VERUS" --version 2>/dev/null | grep -oE 'Toolchain:[[:space:]]*\S+' | sed -E 's/.*:[[:space:]]*//')"
    printf "  verus: %s (pinned %s)\n" "${GOT_VER:-unknown}" "${PIN_VER:-unset}"
    if [ -n "$PIN_VER" ] && [ -n "$GOT_VER" ] && [ "$PIN_VER" != "$GOT_VER" ]; then
        printf '\033[1;33m  !! VERUS VERSION MISMATCH\033[0m\n' >&2
        printf "     pinned   %s  (toolchain %s)\n" "$PIN_VER" "${PIN_TC:-?}" >&2
        printf "     running  %s  (toolchain %s)\n" "$GOT_VER" "${GOT_TC:-?}" >&2
        printf "     Files that fail to COMPILE under a different vstd are reported\n" >&2
        printf "     below as 'no verification summary'. That is a toolchain result,\n" >&2
        printf "     not a proof result. Install the pinned build before treating any\n" >&2
        printf "     total here as the paper's figure. See %s.\n" "$PINFILE" >&2
        VERSION_MISMATCH=1
    fi
else
    printf "  verus: %s (no pin recorded)\n" "$("$VERUS" --version 2>/dev/null | grep -oE 'Version:[[:space:]]*\S+' | sed -E 's/.*:[[:space:]]*//')"
fi
VERSION_MISMATCH="${VERSION_MISMATCH:-0}"

cd "$VDET"
declare -A COUNT       # basename -> verified count (only when 0 errors)
declare -A STATUS      # basename -> ok|ERR
INCOMPLETE=0

REV="$( (cd "$VDET" && git rev-parse --short HEAD 2>/dev/null) || echo 'not a git checkout')"
DIRTY="$( (cd "$VDET" && git status --porcelain -- src 2>/dev/null | head -c1) || true )"
[ -n "$DIRTY" ] && REV="$REV (uncommitted changes in src/)"
log "Counting: $SOURCE"
printf "  revision: %s\n" "$REV"
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
# Declared textual re-inclusions (manual fallback list)
for rel in "${TEXTUAL_REINCLUSION[@]}"; do
    p="${rel%%:*}"; c="${rel##*:}"
    [ "${STATUS[$p]:-}" = "ok" ] && [ -n "${COUNT[$c]:-}" ] && EDGES+=("$p:$c:textual")
done
# Source-marker textual re-inclusions. Any counted file may self-declare a
# textual re-inclusion with a marker comment on its own line:
#     //@ reinclude-textual: <child>.rs
# `mod` re-inclusions are structurally detectable; textual (inline-copy)
# re-inclusions are NOT, so without a marker an undeclared inline copy of
# another file's model would silently OVER-count. This scan makes textual
# edges self-documenting and auto-detected; the manual list above remains a
# fallback. (Markers and the manual list are de-duplicated below, so an edge
# declared both ways is still subtracted exactly once.)
for f in "${FILES[@]}"; do
    [ "${STATUS[$f]:-}" = "ok" ] || continue
    while read -r child; do
        [ -n "$child" ] || continue
        [ -n "${COUNT[$child]:-}" ] && EDGES+=("$f:$child:textual-marker")
    done < <(grep -oE '//@[[:space:]]*reinclude-textual:[[:space:]]*[A-Za-z0-9_]+\.rs' "src/$f" 2>/dev/null \
              | grep -oE '[A-Za-z0-9_]+\.rs')
done
# De-duplicate edges by parent:child. A child re-included by the SAME parent
# through more than one detector (e.g. the manual list AND a source marker)
# must be subtracted ONCE. Distinct parents re-including the same child are
# KEPT -- those are genuinely distinct re-inclusions (e.g. both
# lib_consistency_lattice.rs and lib_l2_exec.rs re-include lib_l2_safety.rs,
# and BOTH of those copies must be removed; that is why l2_safety is subtracted
# twice in the live run).
declare -A SEEN_EDGE
_DEDUP_EDGES=()
for edge in "${EDGES[@]:-}"; do
    [ -n "$edge" ] || continue
    p="${edge%%:*}"; rest="${edge#*:}"; c="${rest%%:*}"
    key="$p|$c"
    if [ -z "${SEEN_EDGE[$key]:-}" ]; then
        SEEN_EDGE[$key]=1
        _DEDUP_EDGES+=("$edge")
    fi
done
if [ "${#_DEDUP_EDGES[@]}" -gt 0 ]; then EDGES=("${_DEDUP_EDGES[@]}"); else EDGES=(); fi

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
    if [ "$VERSION_MISMATCH" -eq 1 ]; then
        err "and the Verus version does not match the pin — check that FIRST."
    fi
    exit 1
fi
if [ "$VERSION_MISMATCH" -eq 1 ]; then
    err "every file verified, but under a Verus that is not the pinned build;"
    err "this total is not the paper's figure unless the pin is restored."
    exit 1
fi
ok "All counted files verified at 0 errors."
printf "  measured tree: %s\n" "$SOURCE"
printf "  revision:      %s\n" "$REV"
echo "  This DISTINCT total = every counted obligation in the crate, with"
echo "  re-included (mod / textual) obligations removed once. The default run"
echo "  is the curated headline (EXCLUDE applied); --full is the full distinct"
echo "  total. This printed figure is authoritative: the paper headline must"
echo "  match it."
