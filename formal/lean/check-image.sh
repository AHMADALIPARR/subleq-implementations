#!/usr/bin/env bash
# Build-time identity check, hooked into `lake build` via the
# `checkArtifact` extraDep target in lakefile.lean:
#   * official and embedded intfmt.dec match the expected SHA-256
#   * the two .dec files are byte-identical
#   * regenerating Image.lean, DecChunksA/B/C.lean, and DecBindDataA/B/C.lean
#     is byte-identical
#   * IntFmt/DecLoad.lean quotes the same SHA-256
# This is a #eval-free, native_decide-free build check.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
official="$root/microcode/tinyprintf/intfmt.dec"
embedded="$here/IntFmt/intfmt.dec"
image="$here/IntFmt/Image.lean"
decload="$here/IntFmt/DecLoad.lean"
expect_sha="bc8679df169f382114b779b54e97bdf21bccc94bf6341ca55374f357610f94c6"
fail() { echo "check-image: FAIL: $*" >&2; exit 1; }
[[ -f "$official" ]] || fail "missing $official"
[[ -f "$embedded" ]] || fail "missing $embedded"
[[ -f "$image" ]] || fail "missing $image"
[[ -f "$decload" ]] || fail "missing $decload"
sha_off="$(sha256sum "$official" | awk '{print $1}')"
sha_emb="$(sha256sum "$embedded" | awk '{print $1}')"
[[ "$sha_off" == "$expect_sha" ]] || fail "official sha256 $sha_off != $expect_sha"
[[ "$sha_emb" == "$expect_sha" ]] || fail "embedded sha256 $sha_emb != $expect_sha"
cmp -s "$official" "$embedded" || fail "embedded copy differs from official .dec"
grep -q "$expect_sha" "$decload" || fail "DecLoad.lean does not quote expected SHA-256 $expect_sha"
tmp="$(mktemp)"
tmpdir="$(mktemp -d)"
trap 'rm -f "$tmp"; rm -rf "$tmpdir"' EXIT
"$here/gen-image.sh" "$official" "$tmp"
cmp -s "$image" "$tmp" || fail "regenerating Image.lean is not byte-identical"
"$here/gen-chunks.sh" "$official" "$tmpdir"
for f in DecChunksA.lean DecChunksB.lean DecChunksC.lean; do
  [[ -f "$here/IntFmt/$f" ]] || fail "missing IntFmt/$f"
  cmp -s "$here/IntFmt/$f" "$tmpdir/$f" || fail "regenerating $f is not byte-identical"
done
"$here/gen-bind.sh" "$official" "$tmpdir"
for f in DecBindDataA.lean DecBindDataB.lean DecBindDataC.lean; do
  [[ -f "$here/IntFmt/$f" ]] || fail "missing IntFmt/$f"
  cmp -s "$here/IntFmt/$f" "$tmpdir/$f" || fail "regenerating $f is not byte-identical"
done
echo "check-image: PASS"
echo "intfmt.dec SHA-256 $expect_sha"
echo "Image.lean, DecChunksA/B/C.lean, DecBindDataA/B/C.lean match generators"
echo "embedded IntFmt/intfmt.dec is byte-identical to official artifact"
echo "DecLoad.lean quotes the expected SHA-256"
echo "hooked into lake build as extraDep target checkArtifact"
