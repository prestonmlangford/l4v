#!/usr/bin/env bash
#
# check-hygiene.sh -- the l4v-only, self-contained tier of the merge gate.
#
# Scope is the AMP body of work, l4v/amp/, and nothing else. CLAUDE.md
# forbids touching existing l4v proofs at all, so single-core l4v/seL4
# content is never this project's concern; there is nothing to gain by
# diffing against a base ref and something real to lose, since `polarfire`
# diverges from upstream permanently and a diff-based scan re-flags
# already-reviewed single-core content (e.g. old axiomatizations) on every
# push forever. Scanning the fixed amp/ directory tree directly -- with no
# reference to git history -- is exactly as complete as this project needs.
#
#   1. no cheats  (sorry / oops / quick_and_dirty / skip_proofs) anywhere in l4v/amp
#   2. no raw axioms (axiomatization / axioms) anywhere in l4v/amp, unattributed
#   3. coding standard: every declaration in l4v/amp carries a preceding prose comment
#
# This is the single source of truth for those checks. It is invoked by:
#   - GitHub Actions (.github/workflows/proof-hygiene.yml) on PRs into polarfire
#   - the local pre-push hook, via the umbrella's check-green.sh
#
# The heavier checks (build config, generated maxIRQ/irqBits, the Isabelle
# build) live in the umbrella's check-green.sh because they need the kernel
# config and the prover; they cannot run in ordinary CI.
#
# Usage: check-hygiene.sh
# Exit:  0 = clean, 1 = a check failed.

set -euo pipefail

L4V="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
AMP="$L4V/amp"
cd "$L4V"

fail=0
bad() { printf '  FAIL: %s\n' "$1"; fail=1; }
ok()  { printf '  OK: %s\n' "$1"; }

files=""
if [ -d "$AMP" ]; then
  files=$(find "$AMP" -name '*.thy' | sort)
fi

echo "[1] No cheats in l4v/amp"
if [ -z "$files" ]; then
  ok "no .thy files under l4v/amp"
else
  hits=""
  while IFS= read -r f; do
    m=$(grep -nE '(^|[^a-zA-Z_])(sorry|oops)([^a-zA-Z_]|$)|quick_and_dirty|skip_proofs' "$f" || true)
    [ -n "$m" ] && hits="$hits\n  $f:\n$(echo "$m" | sed 's/^/    /')"
  done <<< "$files"
  if [ -n "$hits" ]; then
    bad "cheat markers found (inspect -- 'sorry' inside a comment is a false positive):"
    printf '%b\n' "$hits"
  else
    ok "$(echo "$files" | wc -l | tr -d ' ') theory file(s) under l4v/amp, no cheats"
  fi
fi

echo "[2] No raw axioms in l4v/amp"
if [ -z "$files" ]; then
  ok "no .thy files under l4v/amp"
else
  hits=""
  while IFS= read -r f; do
    m=$(grep -nE '(^|[^a-zA-Z_])axiomatization([^a-zA-Z_]|$)|(^|[^a-zA-Z_])axioms([^a-zA-Z_]|$)' "$f" || true)
    [ -n "$m" ] && hits="$hits\n  $f:\n$(echo "$m" | sed 's/^/    /')"
  done <<< "$files"
  if [ -n "$hits" ]; then
    bad "raw axiom found -- confirm it is a ledgered, hardware-justified assumption (CLAUDE.md), not an invented one:"
    printf '%b\n' "$hits"
  else
    ok "no raw axioms"
  fi
fi

echo "[3] Coding standard: comments on declarations in l4v/amp"
if [ -d "$AMP" ]; then
  python3 "$L4V/.github/scripts/check-comments.py" "$AMP" || fail=1
else
  ok "no l4v/amp directory yet"
fi

if [ "$fail" -eq 0 ]; then
  echo "hygiene: PASS"
else
  echo "hygiene: FAIL"
fi
exit "$fail"
