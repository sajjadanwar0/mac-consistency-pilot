#!/usr/bin/env bash
# verus_count.sh — compute the DISTINCT Verus obligation total for the
# mac-consistency verus-detector crate, transparently and reproducibly.
# Usage:
#   ./verus_count.sh                 # clone the pilot repo, count (curated total)
#   ./verus_count.sh --full          # empty EXCLUDE: full distinct total
#   ./verus_count.sh --local=DIR     # count DIR/mac-consistency-pilot/verus-detector
#   VERUS=/path/to/verus ./verus_count.sh
#
# Output: a per-file table, the raw sum, every re-inclusion subtraction, and
#   the distinct total. Files with verification errors are flagged and the
#   total is marked INCOMPLETE.

set -uo pipefail

GITHUB_USER="sajjadanwar0"
VERUS="${VERUS:-verus}"
LOCAL_BASE=""
FULL=0
for arg in "$@"; do
    case "$arg" in
        --local=*) LOCAL_BASE="${arg#*=}" ;;
        --full|--include-all) FULL=1 ;;
        --help|-h) sed -n '2,/^set -u/p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    esac
done

TEXTUAL_REINCLUSION=(
  "lib_l2_exec.rs:lib_l2_safety.rs"
)

NEVER_COUNT=(
  "verified_a1.rs"
)

EXCLUDE=(
  "lib_probabilistic_a1.rs"
  "lib_probabilistic_a1_v2.rs"
  "lib_detect_a1_exec.rs"
  "lib_pessimistic_exec.rs"
  "lib_pessimistic_invariant.rs"
  "lib_si_commit_invariant.rs"
)

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

    rm -rf mac-consistency-pilot

    git clone --quiet --depth=1 \
        "https://github.com/$GITHUB_USER/mac-consistency-pilot.git"
    VDET="$WORK/mac-consistency-pilot/verus-detector"
fi

[ -d "$VDET/src" ] || { echo "verus-detector/src not found at $VDET" >&2; exit 1; }
have "$VERUS" || { echo "verus not on PATH (set VERUS=)" >&2; exit 1; }

cd "$VDET"
declare -A COUNT
declare -A STATUS
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

EDGES=()

for f in "${FILES[@]}"; do
    [ "${STATUS[$f]:-}" = "ok" ] || continue
    while read -r m; do
        [ -n "$m" ] || continue
        child="$m.rs"
        if [ -n "${COUNT[$child]:-}" ]; then EDGES+=("$f:$child:mod"); fi
    done < <(grep -oE '(pub +)?mod +[a-z0-9_]+ *;' "src/$f" | grep -oE '[a-z0-9_]+ *;' | tr -d ' ;')
done

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