#!/usr/bin/env bash
# Mutation tests for the concrete intfmt.dec refinement.
#
# (A) Identity / artifact binding: flip a meaningful cell of Image.lean
#     only (hash / regen check out of date, or a cell theorem breaks).
#     Cases: boot target 48→49, ASCII '0' (K48=48)→47, ASCII '-' (K45=45)→44,
#     HALT target 32768→32767.
# (B) Semantic: alter the program AND update the hash, Image.lean,
#     embedded .dec, DecChunks, and DecBindData so artifact binding
#     would pass, but leave the hand-written semantic lemmas
#     (`image_cell_K45`, `k45_is_ascii_minus`) stating the value 45.
#     The build must still fail on those semantic theorems.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
log="${1:-$here/../results/mutation-test.log}"
mkdir -p "$(dirname "$log")"

image="$here/IntFmt/Image.lean"
embedded="$here/IntFmt/intfmt.dec"
decload="$here/IntFmt/DecLoad.lean"
check="$here/check-image.sh"
chunksA="$here/IntFmt/DecChunksA.lean"
chunksB="$here/IntFmt/DecChunksB.lean"
chunksC="$here/IntFmt/DecChunksC.lean"
bindA="$here/IntFmt/DecBindDataA.lean"
bindB="$here/IntFmt/DecBindDataB.lean"
bindC="$here/IntFmt/DecBindDataC.lean"

backup_dir="$(mktemp -d)"
cp "$image" "$embedded" "$decload" "$check" "$chunksA" "$chunksB" "$chunksC" "$bindA" "$bindB" "$bindC" "$backup_dir/"
restore_all() {
  cp "$backup_dir/Image.lean" "$image"
  cp "$backup_dir/intfmt.dec" "$embedded"
  cp "$backup_dir/DecLoad.lean" "$decload"
  cp "$backup_dir/check-image.sh" "$check"
  cp "$backup_dir/DecChunksA.lean" "$chunksA"
  cp "$backup_dir/DecChunksB.lean" "$chunksB"
  cp "$backup_dir/DecChunksC.lean" "$chunksC"
  cp "$backup_dir/DecBindDataA.lean" "$bindA"
  cp "$backup_dir/DecBindDataB.lean" "$bindB"
  cp "$backup_dir/DecBindDataC.lean" "$bindC"
  rm -rf "$backup_dir" "$here/.mutation-build.log"
}
trap restore_all EXIT

# Replace the 0-based cell `idx` of intfmtImage (the `  N,` / last `  N` line
# after `:= #[`) with `new`.
flip_cell() {
  local src="$1" dest="$2" idx="$3" new="$4"
  awk -v idx="$idx" -v new="$new" '
    BEGIN { n = -1; seen = 0 }
    /def intfmtImage : Array UInt16 := #\[/ { print; inarr = 1; next }
    inarr && seen == 0 {
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
  ' "$src" > "$dest"
}

# Flip 0-based whitespace-separated cell `idx` of a .dec file to `new`.
flip_dec_cell() {
  local src="$1" dest="$2" idx="$3" new="$4"
  awk -v idx="$idx" -v new="$new" '
    BEGIN { n = -1; seen = 0 }
    {
      for (i = 1; i <= NF; i++) {
        n++
        if (n == idx && seen == 0) {
          $i = new
          seen = 1
        }
      }
      print
    }
    END { if (seen == 0) { print "flip_dec_cell: cell " idx " not found" > "/dev/stderr"; exit 1 } }
  ' "$src" > "$dest"
}

fail_build() {
  local name="$1"
  shift
  local targets=("$@")
  if [[ ${#targets[@]} -eq 0 ]]; then
    targets=(IntFmt.DecLoad IntFmt.RefinementDec IntFmt.Blocks)
  fi
  if (cd "$here" && lake build "${targets[@]}") >"$here/.mutation-build.log" 2>&1; then
    echo "MUTATION $name: FAIL (lake build unexpectedly succeeded)" | tee -a "$log"
    return 1
  else
    echo "MUTATION $name: PASS (lake build failed as required)" | tee -a "$log"
    grep "error:" "$here/.mutation-build.log" | head -8 | tee -a "$log" || true
    return 0
  fi
}

: > "$log"
echo "mutation-test: start" | tee -a "$log"

# --- (A) Identity / binding mutations (Image.lean only) ---

flip_cell "$backup_dir/Image.lean" "$image" 2 49
fail_build "boot-jmp-target-48-to-49"
# Do not call restore_all mid-script: it deletes backup_dir (used by later cases).
cp "$backup_dir/Image.lean" "$image"

flip_cell "$backup_dir/Image.lean" "$image" 8 47
fail_build "K48-ascii-0-48-to-47"
cp "$backup_dir/Image.lean" "$image"

flip_cell "$backup_dir/Image.lean" "$image" 9 44
fail_build "K45-minus-45-to-44"
cp "$backup_dir/Image.lean" "$image"

flip_cell "$backup_dir/Image.lean" "$image" 2318 32767
fail_build "halt-target-32768-to-32767"
cp "$backup_dir/Image.lean" "$image"

# --- (B) Semantic mutation with matching updated hash ---
echo "mutation-test: semantic case (K45 45→44 with matching hash)" | tee -a "$log"
mutdec="$(mktemp)"
flip_dec_cell "$root/microcode/tinyprintf/intfmt.dec" "$mutdec" 9 44
# The official file is not modified; we only point the formal copies at mutdec.
newsha="$(sha256sum "$mutdec" | awk '{print $1}')"
oldsha="bc8679df169f382114b779b54e97bdf21bccc94bf6341ca55374f357610f94c6"
cp "$mutdec" "$embedded"
# Image / chunks / bind regenerated from the mutated artifact
"$here/gen-image.sh" "$mutdec" "$image"
"$here/gen-chunks.sh" "$mutdec" "$here/IntFmt"
"$here/gen-bind.sh" "$mutdec" "$here/IntFmt"
# Update expected hash in the check script and the Lean constant only.
# Do NOT change image_cell_K45 / k45_is_ascii_minus (they still say 45).
sed -i "s/$oldsha/$newsha/g" "$check" "$decload"
# Sanity: binding check should PASS on the mutated, consistent artifact.
if ! (cd "$here" && bash check-image.sh) >"$here/.mutation-bind-check.log" 2>&1; then
  # check-image.sh compares against the official microcode artifact, which
  # we deliberately did not modify. For the semantic test we only need the
  # formal copies to be internally consistent; document that official vs
  # mutated differs (expected) and continue with lake build of Lean files
  # after temporarily pointing the official-path check away...
  # Instead: skip the official-file comparison by not running check-image,
  # and build Lean modules that do not re-run a failing official cmp.
  # The lakefile extraDep target WOULD fail on official mismatch, so we
  # build the Lean files with `lean` via lake but the extraDep will fire.
  #
  # To let the semantic-theorem failure be the one we observe, temporarily
  # copy the mutated .dec over a side path... we cannot touch official
  # microcode. Work around: run `lake` will run checkArtifact against
  # official. That fails the *hash* (official still 45), which is not the
  # semantic test we want.
  #
  # So we compile the affected modules with `lean` directly, bypassing
  # the extraDep official-hash check, after the formal tree is consistent
  # with the mutated program + new hash.
  echo "check-image vs official .dec failed as expected (official unchanged)" | tee -a "$log"
fi
# `lake env lean --make` is not accepted by Lean 4.35, and a direct
# `lean` invocation would reuse stale oleans for the unmutated Image.
# Temporarily stub check-image.sh so the lake extraDep does not fail on
# the expected official-vs-mutated .dec mismatch (official microcode is
# never modified). Formal Image/chunks/bind/hash are already consistent.
# The stub is restored from backup_dir below (and by the EXIT trap).
cat > "$check" << 'STUB'
#!/bin/bash
# Semantic mutation stub: official .dec is intentionally unchanged.
exit 0
STUB
chmod +x "$check"
if (cd "$here" && lake build IntFmt.DecLoad IntFmt.Blocks) \
    >"$here/.mutation-build.log" 2>&1; then
  echo "MUTATION semantic-K45-with-matching-hash: FAIL (build unexpectedly succeeded)" | tee -a "$log"
  rm -f "$mutdec"
  exit 1
else
  # Lean reports the failing `rfl` by file:line (image_cell_K45 is
  # DecLoad.lean:152; intfmtImage_prefix16 also hard-codes cell 9 = 45).
  if ! grep -E "image_cell_K45|k45_is_ascii_minus|DecLoad.lean:152|DecLoad.lean:13[37]" "$here/.mutation-build.log" >/dev/null; then
    echo "MUTATION semantic-K45-with-matching-hash: FAIL (build failed, but not on the semantic K45 lemmas)" | tee -a "$log"
    grep "error:" "$here/.mutation-build.log" | head -20 | tee -a "$log" || true
    rm -f "$mutdec"
    exit 1
  fi
  echo "MUTATION semantic-K45-with-matching-hash: PASS (semantic theorem failed as required)" | tee -a "$log"
  grep "error:" "$here/.mutation-build.log" | head -12 | tee -a "$log" || true
fi
rm -f "$mutdec"
# Restore formal tree (not official microcode, which was never changed)
cp "$backup_dir/Image.lean" "$image"
cp "$backup_dir/intfmt.dec" "$embedded"
cp "$backup_dir/DecLoad.lean" "$decload"
cp "$backup_dir/check-image.sh" "$check"
cp "$backup_dir/DecChunksA.lean" "$chunksA"
cp "$backup_dir/DecChunksB.lean" "$chunksB"
cp "$backup_dir/DecChunksC.lean" "$chunksC"
cp "$backup_dir/DecBindDataA.lean" "$bindA"
cp "$backup_dir/DecBindDataB.lean" "$bindB"
cp "$backup_dir/DecBindDataC.lean" "$bindC"

echo "mutation-test: all cases broke the kernel build as required" | tee -a "$log"
