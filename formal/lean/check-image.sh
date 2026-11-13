#!/usr/bin/env bash
# Build-time identity check: regenerating Image.lean is byte-identical,
# and the embedded IntFmt/intfmt.dec matches the official assembled artifact.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
official="$root/microcode/tinyprintf/intfmt.dec"
embedded="$here/IntFmt/intfmt.dec"
image="$here/IntFmt/Image.lean"
expect_sha="bc8679df169f382114b779b54e97bdf21bccc94bf6341ca55374f357610f94c6"
fail() { echo "check-image: FAIL: $*" >&2; exit 1; }
[[ -f "$official" ]] || fail "missing $official"
[[ -f "$embedded" ]] || fail "missing $embedded"
[[ -f "$image" ]] || fail "missing $image"
sha_off="$(sha256sum "$official" | awk '{print $1}')"
sha_emb="$(sha256sum "$embedded" | awk '{print $1}')"
[[ "$sha_off" == "$expect_sha" ]] || fail "official sha256 $sha_off != $expect_sha"
[[ "$sha_emb" == "$expect_sha" ]] || fail "embedded sha256 $sha_emb != $expect_sha"
cmp -s "$official" "$embedded" || fail "embedded copy differs from official .dec"
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
"$here/gen-image.sh" "$official" "$tmp"
cmp -s "$image" "$tmp" || fail "regenerating Image.lean is not byte-identical"
echo "check-image: PASS"
echo "intfmt.dec SHA-256 $expect_sha"
echo "Image.lean matches gen-image.sh output"
echo "embedded IntFmt/intfmt.dec is byte-identical to official artifact"
