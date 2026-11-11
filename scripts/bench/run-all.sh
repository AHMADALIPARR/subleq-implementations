#!/usr/bin/env bash
# run-all.sh — Run the full benchmark suite and collect results.
# Usage: ./scripts/bench/run-all.sh [--repeat N] [--only engines]
set -euo pipefail
cd "$(dirname "$0")/../.."

REPEAT=3
ONLY=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --repeat) REPEAT="$2"; shift 2 ;;
    --only)   ONLY="$2"; shift 2 ;;
    *) echo "Unknown arg: $1"; exit 1 ;;
  esac
done

mkdir -p verification-results
echo "=== SUBLEQ Benchmark Suite ==="
echo "Repeat: $REPEAT"
echo "Only: ${ONLY:-all}"
echo

# Ensure results directory
OUT=verification-results/bench-$(date +%Y%m%d-%H%M%S).md
echo "# Benchmark run $(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$OUT"
echo >> "$OUT"

ARGS=()
[[ -n "$ONLY" ]] && ARGS+=(--only "$ONLY")
ARGS+=(--repeat "$REPEAT")

echo "Running bench/bench.rkt ..."
racket bench/bench.rkt "${ARGS[@]}" >> "$OUT"
echo "Results written to $OUT"
echo
echo "=== Summary ==="
tail -40 "$OUT"
