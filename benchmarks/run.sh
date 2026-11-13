#!/bin/bash
# Benchmark runner (bash only, no Python).
# Records hyperfine (warmup + >=10 runs where practical) and one-shot
# instruction counts from jserv -s. Never invents numbers.
#
# Copyright (C) Ahmad <ahmedparr93@gmail.com>
# SPDX-License-Identifier: AGPL-3.0-only
set -eu

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/benchmarks"
WORK="$OUT/work"
HF="$OUT/hyperfine"
mkdir -p "$WORK" "$HF" "$OUT/outputs"

JSERV="${JSERV:-/workspace/jserv-subleq/subleq}"
HOWERJ="${HOWERJ:-/workspace/howerj-subleq/subleq}"
JS_IMG="${JS_IMG:-/workspace/jserv-subleq/stage0.dec}"
HW_IMG="${HW_IMG:-/workspace/howerj-subleq/subleq.dec}"

# Prepare Forth stdin: example + bye (eForth otherwise waits for more input).
prep_forth() {
  local name="$1"
  cat "$ROOT/examples/${name}.fth" > "$WORK/${name}.in"
  printf '\nbye\n' >> "$WORK/${name}.in"
}

prep_10000() {
  local name="$1"
  cat "$ROOT/examples/${name}.fth" \
      "$ROOT/benchmarks/harness/${name}_10000.tail.fth" \
      > "$WORK/${name}_10000.in"
}

EXAMPLES="bitcount clz crc fibonacci log loops sqrt scheduler rainbow"
# mandelbrot is timed separately (fewer runs — it is slow)
HEAVY="bitcount clz crc fibonacci log sqrt"

for e in $EXAMPLES; do
  prep_forth "$e"
done
if [ "${SKIP_MANDELBROT:-0}" != 1 ]; then
  prep_forth mandelbrot
fi
for e in $HEAVY; do
  prep_10000 "$e"
done

# Also copy lshift (raw image) path
LSHIFT="$ROOT/examples/lshift_checked.dec"

run_js() { # $1=opt|plain  $2=input or --image  $3=file
  local mode="$1" kind="$2" file="$3"
  if [ "$kind" = "forth" ]; then
    if [ "$mode" = "opt" ]; then
      "$JSERV" "$JS_IMG" < "$file"
    else
      "$JSERV" "$JS_IMG" -O < "$file"
    fi
  else
    if [ "$mode" = "opt" ]; then
      "$JSERV" "$file"
    else
      "$JSERV" "$file" -O
    fi
  fi
}

# ---- one-shot instruction counts (jserv -s only) ----
# -s prints stats to... check previous: `echo 5000 ms bye | ./subleq stage0.dec -s`
# We'll capture stderr+stdout of a stats run into files.
stats_one() {
  local label="$1" cmd="$2"
  # shellcheck disable=SC2086
  set +e
  eval "$cmd" > "$OUT/outputs/${label}.out" 2> "$OUT/outputs/${label}.stats"
  echo $? > "$OUT/outputs/${label}.exit"
  set -e
}

echo "=== one-shot functional + jserv -s (if any) ==="
CAPTURE="$EXAMPLES"
if [ "${SKIP_MANDELBROT:-0}" != 1 ]; then
  CAPTURE="$CAPTURE mandelbrot"
fi
for e in $CAPTURE; do
  # jserv_opt stats: put -s after the image
  set +e
  "$JSERV" "$JS_IMG" -s < "$WORK/${e}.in" \
    > "$OUT/outputs/jserv_opt_${e}.out" \
    2> "$OUT/outputs/jserv_opt_${e}.stats"
  echo $? > "$OUT/outputs/jserv_opt_${e}.exit"
  "$JSERV" "$JS_IMG" -O -s < "$WORK/${e}.in" \
    > "$OUT/outputs/jserv_plain_${e}.out" \
    2> "$OUT/outputs/jserv_plain_${e}.stats"
  echo $? > "$OUT/outputs/jserv_plain_${e}.exit"
  "$HOWERJ" "$HW_IMG" < "$WORK/${e}.in" \
    > "$OUT/outputs/howerj_${e}.out" \
    2> "$OUT/outputs/howerj_${e}.stats"
  echo $? > "$OUT/outputs/howerj_${e}.exit"
  set -e
  echo "  captured $e"
done
set +e
"$JSERV" "$LSHIFT" -s > "$OUT/outputs/jserv_opt_lshift.out" 2> "$OUT/outputs/jserv_opt_lshift.stats"
echo $? > "$OUT/outputs/jserv_opt_lshift.exit"
"$JSERV" "$LSHIFT" -O -s > "$OUT/outputs/jserv_plain_lshift.out" 2> "$OUT/outputs/jserv_plain_lshift.stats"
echo $? > "$OUT/outputs/jserv_plain_lshift.exit"
"$HOWERJ" "$LSHIFT" > "$OUT/outputs/howerj_lshift.out" 2> "$OUT/outputs/howerj_lshift.stats"
echo $? > "$OUT/outputs/howerj_lshift.exit"
set -e
echo "  captured lshift"

# ---- hyperfine: short examples, 3 warmup, 10 runs ----
# Build command list.
HF_ARGS=( --warmup 3 --runs 10 --export-csv "$HF/examples.csv" --export-markdown "$HF/examples.md" )
for e in $EXAMPLES; do
  HF_ARGS+=( -n "jserv_opt_${e}" "bash -c \"$JSERV $JS_IMG < $WORK/${e}.in > /dev/null\"" )
  HF_ARGS+=( -n "jserv_plain_${e}" "bash -c \"$JSERV $JS_IMG -O < $WORK/${e}.in > /dev/null\"" )
  HF_ARGS+=( -n "howerj_${e}" "bash -c \"$HOWERJ $HW_IMG < $WORK/${e}.in > /dev/null\"" )
done
HF_ARGS+=( -n "jserv_opt_lshift" "bash -c \"$JSERV $LSHIFT > /dev/null\"" )
HF_ARGS+=( -n "jserv_plain_lshift" "bash -c \"$JSERV $LSHIFT -O > /dev/null\"" )
HF_ARGS+=( -n "howerj_lshift" "bash -c \"$HOWERJ $LSHIFT > /dev/null\"" )

echo "=== hyperfine examples (warmup 3, runs 10) ==="
/home/box/.local/bin/hyperfine "${HF_ARGS[@]}"

echo "=== hyperfine 10000x harness (warmup 3, runs 10) ==="
HF2=( --warmup 3 --runs 10 --export-csv "$HF/x10000.csv" --export-markdown "$HF/x10000.md" )
for e in $HEAVY; do
  HF2+=( -n "jserv_opt_${e}_10000" "bash -c \"$JSERV $JS_IMG < $WORK/${e}_10000.in > /dev/null\"" )
  HF2+=( -n "jserv_plain_${e}_10000" "bash -c \"$JSERV $JS_IMG -O < $WORK/${e}_10000.in > /dev/null\"" )
  HF2+=( -n "howerj_${e}_10000" "bash -c \"$HOWERJ $HW_IMG < $WORK/${e}_10000.in > /dev/null\"" )
done
/home/box/.local/bin/hyperfine "${HF2[@]}"

# mandelbrot is slow (minutes per run). Do 3 runs, 0 warmup, and label it.
# Set SKIP_MANDELBROT=1 to omit this section.
if [ "${SKIP_MANDELBROT:-0}" = 1 ]; then
  echo "=== skip mandelbrot hyperfine (SKIP_MANDELBROT=1) ==="
else
  echo "=== hyperfine mandelbrot (runs 3, no warmup — too slow for 10) ==="
  /home/box/.local/bin/hyperfine --runs 3 --export-csv "$HF/mandelbrot.csv" --export-markdown "$HF/mandelbrot.md" \
    -n jserv_opt_mandelbrot "bash -c \"$JSERV $JS_IMG < $WORK/mandelbrot.in > /dev/null\"" \
    -n jserv_plain_mandelbrot "bash -c \"$JSERV $JS_IMG -O < $WORK/mandelbrot.in > /dev/null\"" \
    -n howerj_mandelbrot "bash -c \"$HOWERJ $HW_IMG < $WORK/mandelbrot.in > /dev/null\""
fi

echo "=== run.sh done ==="
