#!/usr/bin/env bash
# =====================================================================
# check_ignores.sh -- how many .gitignore files does git actually HONOR?
#
# Evidence in this repository was invisible for two rounds because a
# second ignore file, python/.gitignore, carried rules nobody had looked
# at.  This gate exists so that cannot recur.  It asks the question that
# matters: which .gitignore files can affect a tracked path?
#
# A .gitignore inside a directory that is itself ignored (.idea/,
# .venv/, verus-count-clone/) is never consulted for tracked content, so
# it is not counted.  An ignore file that git honors and that carries an
# active rule outside the allowed set is a finding.
#
#   ./check_ignores.sh          list and gate
#   ./check_ignores.sh --quiet  verdict only
#
# Exits non-zero if git honors an ignore file other than ./.gitignore,
# or if any honored nested ignore file carries an active rule.
# =====================================================================
set -euo pipefail
[ -d .git ] || { echo "FAIL: run from the repository root" >&2; exit 1; }
QUIET=0
[ "${1:-}" = "--quiet" ] && QUIET=1

honored=()
shadowed=()
while IFS= read -r f; do
  rel="${f#./}"
  if git check-ignore -q "$rel" 2>/dev/null; then
    shadowed+=("$rel")
  else
    honored+=("$rel")
  fi
done < <(find . -name '.gitignore' -not -path './.git/*' | sort)

bad=0
for f in "${honored[@]}"; do
  active=$( ( grep -v '^[[:space:]]*#' "$f" | grep -c '[^[:space:]]' ) || true )
  if [ "$f" = ".gitignore" ]; then
    [ "$QUIET" -eq 1 ] || printf '  root   %-56s %s active rule(s)\n' "$f" "${active:-0}"
  elif [ "${active:-0}" -eq 0 ]; then
    [ "$QUIET" -eq 1 ] || printf '  inert  %-56s no active rule\n' "$f"
  else
    printf '  ACTIVE %-56s %s active rule(s) -- this file can hide tracked content\n' "$f" "${active:-0}"
    bad=1
  fi
done
if [ "$QUIET" -eq 0 ]; then
  for f in "${shadowed[@]}"; do
    printf '  shadowed %-54s inside an ignored directory; git never consults it\n' "$f"
  done
fi

echo
if [ "$bad" -ne 0 ]; then
  echo "FAIL: a nested .gitignore that git honors carries active rules."
  echo "      Move the rules into the root .gitignore so there is one place to look."
  exit 1
fi
echo "OK: ${#honored[@]} honored ignore file(s), ${#shadowed[@]} shadowed; only the root carries rules"
