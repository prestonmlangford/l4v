#!/usr/bin/env bash
#
# check-hygiene.sh -- the l4v-only, self-contained tier of the merge gate.
#
# Checks that can run against the l4v tree ALONE, with no kernel build, no
# Isabelle, and no umbrella repo:
#
#   1. no cheats  (sorry / oops / quick_and_dirty / skip_proofs) in changed .thy
#   2. no raw axioms (axiomatization / axioms) in changed .thy, unattributed
#   3. coding standard: added declarations carry a preceding prose comment
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
# Untracked new .thy files are invisible to `git diff` (it only sees tracked
# paths), so a brand-new file could otherwise silently skip both checks below
# unless the caller happened to `git add` it first. Union in untracked files
# explicitly so that can't happen.
changed=$( (git diff --name-only --diff-filter=d "$BASE" -- '*.thy'
            git ls-files --others --exclude-standard -- '*.thy') | sort -u || true)
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

echo "[2] No raw axioms in changed theories (vs $BASE)"
# `axiomatization`/`axioms` assert a fact with no proof obligation at all --
# the one mechanism that could introduce an assumption CLAUDE.md's ledger
# never named. Every real AMP assumption (A-BOOT, A-MEM, ...) is stated as an
# explicit theorem hypothesis instead, so this should never fire; a hit is not
# auto-failed the way a cheat is, because a hit needs a human to confirm it
# names an approved, ledgered hardware assumption rather than papering over a
# gap -- see CLAUDE.md's rule against inventing assumptions.
if [ -z "$changed" ]; then
  ok "no changed .thy files"
else
  hits=""
  while IFS= read -r f; do
    [ -f "$f" ] || continue
    m=$(grep -nE '(^|[^a-zA-Z_])axiomatization([^a-zA-Z_]|$)|(^|[^a-zA-Z_])axioms([^a-zA-Z_]|$)' "$f" || true)
    [ -n "$m" ] && hits="$hits\n  $f:\n$(echo "$m" | sed 's/^/    /')"
  done <<< "$changed"
  if [ -n "$hits" ]; then
    bad "raw axiom found -- confirm it is a ledgered, hardware-justified assumption (CLAUDE.md), not an invented one:"
    printf '%b\n' "$hits"
  else
    ok "no raw axioms"
  fi
fi

echo "[3] Coding standard: comments on added declarations"
python3 "$L4V/.github/scripts/check-comments.py" "$BASE" "$L4V" || fail=1

if [ "$fail" -eq 0 ]; then
  echo "hygiene: PASS"
else
  echo "hygiene: FAIL"
fi
exit "$fail"
