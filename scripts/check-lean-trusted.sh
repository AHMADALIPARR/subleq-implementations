#!/bin/sh
# Copyright (C) Ahmad <ahmedparr93@gmail.com>
# SPDX-License-Identifier: AGPL-3.0-only

# Fails if the Lean sources use a proof escape hatch, or if any theorem
# depends on an axiom other than Lean's three standard ones.
# Usage: scripts/check-lean-trusted.sh   (run from the repository root,
# after `lake build` in lean/)
set -eu

cd "$(dirname "$0")/../lean"

files=$(find . -name '*.lean' -not -path './.lake/*' | sort)
echo "Checking: $files"

# 1. Forbidden tokens anywhere in the sources (comments included).
if grep -n -w -E 'sorry|admit|axiom|unsafe|native_decide|implemented_by|extern' $files; then
  echo "FAIL: forbidden token found in Lean sources" >&2
  exit 1
fi

# 2. Every theorem in Theorems.lean must be listed in AxiomCheck.lean.
theorems=$(sed -n 's/^theorem \([A-Za-z0-9_]*\).*/\1/p' Subleq/Theorems.lean | sort)
checked=$(sed -n 's/^#print axioms \([A-Za-z0-9_]*\).*/\1/p' AxiomCheck.lean | sort)
if [ "$theorems" != "$checked" ]; then
  echo "FAIL: AxiomCheck.lean does not list exactly the theorems in Subleq/Theorems.lean" >&2
  exit 1
fi

# 3. Axioms actually used.
out=$(lake env lean AxiomCheck.lean) || { echo "FAIL: AxiomCheck.lean did not elaborate (run lake build first)" >&2; exit 1; }
echo "$out"
count=$(printf '%s\n' "$out" | grep -c "depends on axioms\|does not depend on any axioms" || true)
if [ "$count" -ne "$(printf '%s\n' "$theorems" | wc -l)" ]; then
  echo "FAIL: unexpected #print axioms output" >&2
  exit 1
fi
bad=$(printf '%s\n' "$out" | sed -n 's/.*depends on axioms: \[\(.*\)\]/\1/p' | tr ',' '\n' | tr -d ' ' \
  | grep -v -x -E 'propext|Classical\.choice|Quot\.sound' || true)
if [ -n "$bad" ]; then
  echo "FAIL: non-standard axioms used: $bad" >&2
  exit 1
fi
echo "OK: $(printf '%s\n' "$theorems" | wc -l) theorems, no escape hatches, only standard axioms"
