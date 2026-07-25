#!/usr/bin/env bash
#
# check-hygiene.sh -- the l4v-only, self-contained tier of the merge gate.
#
# Checks that can run against the l4v tree ALONE, with no kernel build, no
# Isabelle, and no umbrella repo:
#
#   1. no cheats  (sorry / oops / quick_and_dirty / skip_proofs) in changed .thy
#   2. coding standard: added declarations carry a preceding prose comment
#
# This is the single source of truth for those two checks. It is invoked by:
#   - GitHub Actions (.github/workflows/proof-hygiene.yml) on PRs into polarfire
#   - the local pre-push hook, via the umbrella's check-green.sh
#
# The heavier checks (build config, generated maxIRQ/irqBits, the Isabelle
# build) live in the umbrella's check-green.sh because they need the kernel
# config and the prover; they cannot run in ordinary CI.
#
# Usage: check-hygiene.sh <base-ref>
# Exit:  0 = clean, 1 = a check failed.

set -euo pipefail

BASE="${1:?usage: check-hygiene.sh <base-ref>}"
L4V="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$L4V"

fail=0
bad() { printf '  FAIL: %s\n' "$1"; fail=1; }
ok()  { printf '  OK: %s\n' "$1"; }

echo "[1] No cheats in changed theories (vs $BASE)"
changed=$(git diff --name-only --diff-filter=d "$BASE" -- '*.thy' || true)
if [ -z "$changed" ]; then
  ok "no changed .thy files"
else
  hits=""
  while IFS= read -r f; do
    [ -f "$f" ] || continue
    m=$(grep -nE '(^|[^a-zA-Z_])(sorry|oops)([^a-zA-Z_]|$)|quick_and_dirty|skip_proofs' "$f" || true)
    [ -n "$m" ] && hits="$hits\n  $f:\n$(echo "$m" | sed 's/^/    /')"
  done <<< "$changed"
  if [ -n "$hits" ]; then
    bad "cheat markers found (inspect -- 'sorry' inside a comment is a false positive):"
    printf '%b\n' "$hits"
  else
    ok "$(echo "$changed" | wc -l | tr -d ' ') changed theory file(s), no cheats"
  fi
fi

echo "[2] Coding standard: comments on added declarations"
python3 "$L4V/.github/scripts/check-comments.py" "$BASE" "$L4V" || fail=1

if [ "$fail" -eq 0 ]; then
  echo "hygiene: PASS"
else
  echo "hygiene: FAIL"
fi
exit "$fail"
