#!/bin/sh
# SPDX-License-Identifier: AGPL-3.0-or-later
# Trusted-path check for the fault-model Lean project in lean-fault/
# (the Lean code from PR #4, kept unchanged on its own toolchain).
# Fails if a Lean source there uses a proof escape hatch, or if any theorem
# in lean-fault/Subleq/Theorems.lean depends on an axiom other than Lean's
# three standard ones. The lean-fault sources are not modified: the axiom
# query is run on a temporary copy of Theorems.lean with `#print axioms`
# lines appended.
# Usage: scripts/check-lean-fault-trusted.sh   (run after `lake build` in
# lean-fault/; `make lean-fault-check` does both)
set -eu

cd "$(dirname "$0")/../lean-fault"

files=$(find . -name '*.lean' -not -path './.lake/*' | sort)
echo "Checking: $files"

# 1. Forbidden tokens anywhere in the sources (comments included).
if grep -n -w -E 'sorry|admit|axiom|unsafe|native_decide|implemented_by|extern' $files; then
  echo "FAIL: forbidden token found in lean-fault sources" >&2
  exit 1
fi

theorems=$(sed -n 's/^theorem \([A-Za-z0-9_]*\).*/\1/p' Subleq/Theorems.lean)
n=$(printf '%s\n' "$theorems" | grep -c . || true)
if [ "$n" -eq 0 ]; then
  echo "FAIL: no theorems found in lean-fault/Subleq/Theorems.lean" >&2
  exit 1
fi

# 2. Elaborate the theorems with #print axioms appended (temporary file).
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cp Subleq/Theorems.lean "$tmp/FaultAxiomCheck.lean"
printf '\n' >> "$tmp/FaultAxiomCheck.lean"
for t in $theorems; do printf '#print axioms %s\n' "$t" >> "$tmp/FaultAxiomCheck.lean"; done
out=$(lake env lean "$tmp/FaultAxiomCheck.lean" 2>&1) || { echo "$out"; echo "FAIL: lean-fault theorems did not elaborate (run lake build in lean-fault first)" >&2; exit 1; }
echo "$out"
if printf '%s\n' "$out" | grep -q -E 'error|warning'; then
  echo "FAIL: errors or warnings while elaborating lean-fault theorems" >&2
  exit 1
fi
count=$(printf '%s\n' "$out" | grep -c "depends on axioms\|does not depend on any axioms" || true)
if [ "$count" -ne "$n" ]; then
  echo "FAIL: expected $n #print axioms results, got $count" >&2
  exit 1
fi
bad=$(printf '%s\n' "$out" | sed -n 's/.*depends on axioms: \[\(.*\)\]/\1/p' | tr ',' '\n' | tr -d ' ' \
  | grep -v -x -E 'propext|Classical\.choice|Quot\.sound' || true)
if [ -n "$bad" ]; then
  echo "FAIL: non-standard axioms used: $bad" >&2
  exit 1
fi
echo "OK: $n lean-fault theorems, no escape hatches, only standard axioms"
