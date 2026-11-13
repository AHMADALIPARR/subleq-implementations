# SUBLEQ implementation benchmarks

Times and instruction counts below are measured, not estimated.
Hyperfine 1.19.0, warmup 3, 10 runs, unless noted. Wall-clock times for
the eForth examples **include booting `stage0.dec`/`subleq.dec` and
compiling the Forth source**, then running the example and `bye`.

## Host

- OS: Linux (Debian), gcc (Debian 14.2.0-19) 14.2.0
- CPU: 8× Intel Xeon Processor (KVM hypervisor), 1 thread/core
- Full `lscpu`: `benchmarks/lscpu.txt`
- GNU time 1.9 at `/usr/bin/time`

## Compiler flags

See `benchmarks/compiler-flags.txt`.

- jserv (opt): `gcc -O2 -std=c99 -D_DEFAULT_SOURCE -Wall -Wextra`
  (`-D_DEFAULT_SOURCE` needed for `fileno` on gcc 14 / `-std=c99`).
  The same binary with runtime `-O` is **jserv_plain** (optimizer off).
- howerj: `gcc -std=c99 -Wall -Wextra -pedantic -O3` (upstream makefile).
- This repository's Forth directive VM: `gforth` 0.7.3.
- Racket and the Factor *language* were not installed (`/usr/bin/factor` is
  coreutils). Those engines were not benchmarked.

## jserv `make check` / `make bootstrap` / `make bench`

Logs: `benchmarks/jserv-make-check.log`, `jserv-make-bootstrap.log`,
`jserv-make-bench.log`.

- `make check`: all OK (loops, radix, bitcount, clz, fibonacci, log, sqrt,
  crc, lshift.dec opt-vs-plain).
- `make bootstrap`: OK (`stage0.dec` = `stage1.dec`).
- `make bench` (`echo 5000 ms bye | ./subleq stage0.dec -s`), with
  `/usr/bin/time` installed: **OK**.
  - Instruction total: **470,694,828**
  - jserv "Execution time": **1.529 seconds**
  - GNU time `-p`: real **1.53**, user **1.52**, sys **0.00**
  (America/Los_Angeles / PST)

## Hyperfine: examples (warmup 3, 10 runs)

Values are mean ± stddev, with min, in milliseconds. Source:
`benchmarks/hyperfine/examples.md` / `examples.csv`.

| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `jserv_opt_bitcount` | 378.8 ± 1.2 | 377.0 | 380.4 | 225.64 ± 19.81 |
| `jserv_plain_bitcount` | 734.6 ± 42.0 | 708.8 | 848.5 | 437.61 ± 45.84 |
| `howerj_bitcount` | 405.9 ± 0.4 | 405.5 | 406.8 | 241.79 ± 21.22 |
| `jserv_opt_clz` | 173.3 ± 0.9 | 171.4 | 174.5 | 103.22 ± 9.07 |
| `jserv_plain_clz` | 324.7 ± 3.9 | 322.6 | 335.8 | 193.45 ± 17.14 |
| `howerj_clz` | 186.0 ± 0.3 | 185.5 | 186.4 | 110.81 ± 9.73 |
| `jserv_opt_crc` | 429.7 ± 1.8 | 427.3 | 431.8 | 255.99 ± 22.49 |
| `jserv_plain_crc` | 793.5 ± 15.6 | 761.2 | 805.4 | 472.74 ± 42.51 |
| `howerj_crc` | 460.0 ± 1.1 | 459.1 | 462.5 | 274.05 ± 24.06 |
| `jserv_opt_fibonacci` | 262.2 ± 0.8 | 260.7 | 263.3 | 156.19 ± 13.71 |
| `jserv_plain_fibonacci` | 490.1 ± 5.7 | 486.3 | 506.0 | 291.95 ± 25.84 |
| `howerj_fibonacci` | 280.3 ± 0.1 | 280.2 | 280.5 | 167.01 ± 14.65 |
| `jserv_opt_log` | 266.7 ± 0.9 | 265.6 | 268.3 | 158.89 ± 13.95 |
| `jserv_plain_log` | 512.3 ± 37.2 | 498.6 | 618.2 | 305.21 ± 34.77 |
| `howerj_log` | 286.9 ± 2.1 | 285.9 | 292.6 | 170.91 ± 15.05 |
| `jserv_opt_loops` | 250.1 ± 1.0 | 248.9 | 252.3 | 149.01 ± 13.09 |
| `jserv_plain_loops` | 467.3 ± 3.0 | 462.6 | 473.8 | 278.37 ± 24.49 |
| `howerj_loops` | 267.5 ± 0.3 | 267.3 | 268.1 | 159.38 ± 13.99 |
| `jserv_opt_sqrt` | 462.2 ± 2.0 | 459.5 | 465.4 | 275.32 ± 24.19 |
| `jserv_plain_sqrt` | 867.2 ± 5.0 | 859.6 | 876.5 | 516.64 ± 45.43 |
| `howerj_sqrt` | 496.8 ± 0.5 | 496.4 | 498.2 | 295.99 ± 25.97 |
| `jserv_opt_scheduler` | 1348.3 ± 5.6 | 1340.1 | 1356.4 | 803.26 ± 70.56 |
| `jserv_plain_scheduler` | 2513.4 ± 4.9 | 2503.3 | 2519.9 | 1497.33 ± 131.42 |
| `howerj_scheduler` | 1438.2 ± 2.2 | 1436.5 | 1443.4 | 856.81 ± 75.20 |
| `jserv_opt_rainbow` | 880.5 ± 3.8 | 874.5 | 884.8 | 524.52 ± 46.08 |
| `jserv_plain_rainbow` | 1659.2 ± 18.7 | 1631.4 | 1693.7 | 988.43 ± 87.45 |
| `howerj_rainbow` | 944.4 ± 1.1 | 942.8 | 945.6 | 562.61 ± 49.37 |
| `jserv_opt_lshift` | 1.7 ± 0.1 | 1.4 | 1.9 | 1.02 ± 0.13 |
| `jserv_plain_lshift` | 1.8 ± 0.1 | 1.6 | 2.0 | 1.05 ± 0.11 |
| `howerj_lshift` | 1.7 ± 0.1 | 1.4 | 1.9 | 1.00 |

`lshift` is a raw 16-cell program (no eForth boot), which is why it is
~1.7 ms. eForth examples spend most of their time compiling Forth.

## jserv `-s` instruction counts (one-shot, includes eForth compile)

| Example | jserv_opt instr | jserv_opt exec s | jserv_plain instr | jserv_plain exec s |
|---|---:|---:|---:|---:|
| bitcount | 99205368 | 0.403 | 192327212 | 0.709 |
| clz | 45227037 | 0.170 | 87270122 | 0.320 |
| crc | 112920121 | 0.424 | 217799070 | 0.801 |
| fibonacci | 68723684 | 0.258 | 132324727 | 0.487 |
| log | 69586342 | 0.263 | 135036437 | 0.497 |
| loops | 65246631 | 0.249 | 126061654 | 0.464 |
| sqrt | 120500743 | 0.462 | 235039283 | 0.869 |
| rainbow | 231549149 | 0.874 | 448355123 | 1.655 |
| scheduler | 357213003 | 1.408 | 684766471 | 2.510 |
| lshift (raw .dec) | 4 | 0.000 | 12 | 0.000 |

howerj has no `-s` flag. howerj one-shot runs all exited 0. Raw
`lshift_checked.dec` output is the single byte `48` (`'0'`), i.e. `6<<3`.

jserv_opt fuses the lshift image to 4 instructions; the plain interpreter
takes 12 (the same 12-step count the debugger recorded).

## 10000× harness

Appended eForth `for ... next` loops (see `benchmarks/harness/`). Times
still include image boot and compile. Table filled from
`benchmarks/hyperfine/x10000.md` when that run finishes.

Mandelbrot was omitted from the ≥10-run hyperfine set because a single
run is several minutes; an earlier functional capture of `jserv_opt`
mandelbrot was 20208 bytes
(SHA-256 `54c72349e00a8e1b3435817f3768ce03c04223b4a331f1a595ede2d41240b59e`).

## Other VMs in this repository

- **Forth directive machine** (`gforth forth/main.fs`, input format from
  `semantics/subleq-spec.md`): countdown fixture
  `benchmarks/fixtures/countdown.directive` → `STATUS halted`, `PC -1`,
  `STEPS 9`, `OUTPUT 3 2 1`. This is a 32-bit directive image, not
  eForth, and is not comparable to the times above.
- Raw eForth `.dec` / `.fth` is not a valid `forth/main.fs` input
  (`subleq: bad number` / `trailing data after FUEL`).
- **Racket**: not installed.
- **Factor language**: not installed (`/usr/bin/factor` is coreutils).
- Existing `lean/` and `lean-fault/` trees were not used as eForth VMs
  and were not modified.

## Microcode oracle (not a VM comparison)

`microcode/tinyprintf/test-oracle` vs `tfp_*` checked, all 65536 unsigned
and signed values plus cap samples: **131128 runs, 0 failures**.
Instruction counts (debugger/VM step counter, the formatting routine only):

- u16toa: min 396, max 1223, mean 934
- i16toa: min 411, max 1266, mean 945
