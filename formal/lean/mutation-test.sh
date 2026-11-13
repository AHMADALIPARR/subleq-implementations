#!/usr/bin/env bash
# Flip meaningful cells of the assembled Lean image and confirm lake build
# rejects the broken identity / boot theorems. Always restores Image.lean.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
image="$here/IntFmt/Image.lean"
log="${1:-$here/../results/mutation-test.log}"
mkdir -p "$(dirname "$log")"
backup="$(mktemp)"
cp "$image" "$backup"
restore() { cp "$backup" "$image"; rm -f "$backup" "$here/.mutation-build.log"; }
trap restore EXIT

# Replace the 0-based cell `idx` of intfmtImage (the `  N,` / last `  N` line
# after `:= #[`) with `new`.
flip_cell() {
  local idx="$1" new="$2"
  awk -v idx="$idx" -v new="$new" '
    BEGIN { n = -1; seen = 0 }
    /def intfmtImage : Array UInt16 := #\[/ { print; inarr = 1; next }
    inarr && seen == 0 {
      # array entries are "  NUM," or the last "  NUM"
      if ($0 ~ /^  -?[0-9]+,?$/) {
        n++
        if (n == idx) {
          if ($0 ~ /,$/) print "  " new ","
          else print "  " new
          seen = 1
          next
        }
      }
    }
    { print }
    END { if (seen == 0) { print "flip_cell: cell " idx " not found" > "/dev/stderr"; exit 1 } }
  ' "$backup" > "$image"
}

fail_build() {
  local name="$1"
  if (cd "$here" && lake build IntFmt.DecLoad IntFmt.RefinementDec) >"$here/.mutation-build.log" 2>&1; then
    echo "MUTATION $name: FAIL (lake build unexpectedly succeeded)" | tee -a "$log"
    return 1
  else
    echo "MUTATION $name: PASS (lake build failed as required)" | tee -a "$log"
    grep "error:" "$here/.mutation-build.log" | head -5 | tee -a "$log" || true
    return 0
  fi
}

: > "$log"
echo "mutation-test: start" | tee -a "$log"

flip_cell 2 49
fail_build "boot-jmp-target-48-to-49"
restore
cp "$image" "$backup"

flip_cell 9 44
fail_build "K45-minus-45-to-44"
restore
cp "$image" "$backup"

flip_cell 2318 32767
fail_build "halt-target-32768-to-32767"

echo "mutation-test: all cases broke the kernel build as required" | tee -a "$log"
