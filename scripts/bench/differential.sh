#!/usr/bin/env bash
# differential.sh — Run differential suite at different scales.
# Usage: ./scripts/bench/differential.sh [random-count]
set -euo pipefail
cd "$(dirname "$0")/../.."

N="${1:-200}"
echo "=== Differential (fixtures + $N random) ==="
/usr/bin/time -f "Elapsed: %e s" \
  racket verification/differential.rkt --random "$N" --seed 20261110
