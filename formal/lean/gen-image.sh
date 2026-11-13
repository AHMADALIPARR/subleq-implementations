#!/usr/bin/env bash
# Deterministic generator: microcode/tinyprintf/intfmt.dec -> IntFmt/Image.lean
# bash + awk only. Re-running must be byte-identical to the committed Image.lean.
set -euo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd)"
dec="${1:-$root/microcode/tinyprintf/intfmt.dec}"
out="${2:-$root/formal/lean/IntFmt/Image.lean}"
if [[ ! -f "$dec" ]]; then
  echo "missing $dec" >&2
  exit 1
fi
awk -v out="$out" '
BEGIN {
  print "/-" > out
  print "Copyright (C) Ahmad <ahmedparr93@gmail.com>" > out
  print "SPDX-License-Identifier: AGPL-3.0-only" > out
  print "Generated from microcode/tinyprintf/intfmt.s — do not edit." > out
  print "-/" > out
  print "" > out
  print "import IntFmt.Subleq" > out
  print "" > out
  print "namespace IntFmt" > out
  print "" > out
  print "/-- Assembled 16-bit image for u16toa/i16toa (cell words). -/" > out
  print "def intfmtImage : Array UInt16 := #[" > out
  n = 0
}
{
  for (i = 1; i <= NF; i++) {
    v = $i + 0
    if (v < 0) v += 65536
    cell[++n] = v
  }
}
END {
  for (i = 1; i <= n; i++) {
    if (i < n) printf("  %d,\n", cell[i]) > out
    else       printf("  %d\n", cell[i]) > out
  }
  print "]" > out
  print "" > out
  print "end IntFmt" > out
}
' "$dec"
