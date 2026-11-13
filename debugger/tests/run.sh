#!/bin/bash
# Bash tests for subleq_dbg. No Python.
# Copyright (C) Ahmad <ahmedparr93@gmail.com>
# SPDX-License-Identifier: AGPL-3.0-only
set -eu
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
DBG="$ROOT/debugger/subleq_dbg"
LSHIFT="$ROOT/examples/lshift_checked.dec"
REC="$ROOT/debugger/tests/recorded"
mkdir -p "$REC"
fail=0

note() { echo "$*"; }

# 1. lshift_checked: 6<<3 = 48, ascii '0'
out=$("$DBG" --run --quiet "$LSHIFT" | od -An -tu1 | tr -s ' ' | sed 's/^ //;s/ $//')
echo "$out" > "$REC/lshift-run.od"
if [ "$out" = "48" ]; then
  note "PASS lshift_checked.dec output 48"
else
  note "FAIL lshift_checked.dec output='$out' expected 48"
  fail=$((fail+1))
fi

# 2. step / state / dump recorded
"$DBG" -c 'p; s; s; s; p; d 0 16; q' "$LSHIFT" > "$REC/lshift-step.txt"
if grep -q 'loaded' "$REC/lshift-step.txt" && grep -q 'PC=' "$REC/lshift-step.txt"; then
  note "PASS step/state/dump produced PC trace"
else
  note "FAIL step/state/dump"
  fail=$((fail+1))
fi

# 3. breakpoint: break at 0 should fire after first leave and return? We set
#    break at pc=3 (after first insn) and continue.
"$DBG" --break 13 -c 'c; p; q' "$LSHIFT" > "$REC/lshift-break.txt"
if grep -q 'break hit' "$REC/lshift-break.txt"; then
  note "PASS PC breakpoint"
else
  note "FAIL PC breakpoint"
  fail=$((fail+1))
fi

# 4. watchpoint + trace + profile on a short run
"$DBG" --watch 0 --trace -c 'r 5; stats; q' "$LSHIFT" > "$REC/lshift-watch-trace.txt"
if grep -q 'profile total_steps' "$REC/lshift-watch-trace.txt"; then
  note "PASS trace/profile"
else
  note "FAIL trace/profile"
  fail=$((fail+1))
fi

# 5. --run --profile-out
"$DBG" --run --profile-out "$REC/lshift.prof" "$LSHIFT" > "$REC/lshift-run-profile.txt"
if [ -s "$REC/lshift.prof" ]; then
  note "PASS profile-out file"
else
  note "FAIL profile-out"
  fail=$((fail+1))
fi

# 6. memory set + dump
"$DBG" -c 'set 10 99; d 10 1; q' "$LSHIFT" > "$REC/lshift-set.txt"
if grep -q '99' "$REC/lshift-set.txt"; then
  note "PASS set/dump"
else
  note "FAIL set/dump"
  fail=$((fail+1))
fi

echo "debugger tests: fails=$fail"
exit "$fail"
