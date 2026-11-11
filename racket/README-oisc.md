<!--
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-or-later
-->

# Simple OISC ADD / SUB Experiment

This is a deliberately limited first experiment that defines the SUBLEQ machine semantics *before* implementing anything complex.

## Semantics

```
result = data[b] - data[a]   (modulo 2^32)
data[b] = result

if signed(result) <= 0:
    micro_pc = target
else:
    micro_pc = micro_pc + 1
```

## What it verifies

### ADD
Four SUBLEQ instructions that compute `output = A + B` with no data-dependent control flow.

Symbolic inputs `a` and `b` are used. The check asserts:

- Final PC is 4 (the program completed)
- Output register equals `a + b`
- Source registers A and B are preserved

### SUB
Five SUBLEQ instructions that compute `output = A - B`.

Both temporary and output may start with arbitrary values. The check asserts:

- Final PC equals the program length (completed)
- Output register equals `a - b`
- Source registers A and B are preserved
- Initial scratch and output contents do not affect the result

Run with:

```bash
racket racket/oisc-add.rkt
# or
make oisc
```

Expected output:

```
PASS: ADD result, exit PC, and source preservation
PASS: SUB result, exit PC, and source preservation
```

## Checking that the verifier catches a bug

Change only the last SUB instruction to:

```racket
(insn 0 3 5)   ; BUG: subtract A instead of B
```

The SUB check should then report `FAIL` and supply a counterexample with unequal `a` and `b`,
and `racket racket/oisc-add.rkt` exits with status 1 (it exits 0 only when every check passes).

This verifies two arithmetic routines; it still does not verify a RISC-V decoder, architectural register writeback, `x0`, or the architectural PC.
