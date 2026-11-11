#!/usr/bin/env bash
# crypto.sh — SHA-256 vectors and keystream (killer app).
set -euo pipefail
cd "$(dirname "$0")/../.."

echo "=== SHA-256 NIST vectors ==="
racket bench/sha256-vectors.rkt
echo
echo "=== Killer app (keystream) ==="
racket bench/killer-app.rkt
