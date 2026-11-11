#!/usr/bin/env bash
# verify-microcode.sh — Time the native directive-machine Rosette harness.
set -euo pipefail
cd "$(dirname "$0")/../.."

echo "=== Native microcode verification (trusted path) ==="
/usr/bin/time -f "Elapsed: %e s  Max RSS: %M KB" \
  racket racket/microcode/verify.rkt
echo
echo "=== Mutation self-test ==="
/usr/bin/time -f "Elapsed: %e s  Max RSS: %M KB" \
  make verify-microcode-mutations
