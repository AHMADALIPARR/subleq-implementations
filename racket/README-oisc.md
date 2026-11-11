# Simple OISC ADD Experiment

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

Four SUBLEQ instructions that compute `output = A + B` with no data-dependent control flow.

Symbolic inputs `a` and `b` are used. The check asserts:

- Final PC is 4 (the program completed)
- Output register equals `a + b`
- Source registers A and B are preserved

Run with:

```bash
racket racket/oisc-add.rkt
```

This serves as a clean foundation before moving to the full RISC-V microcode model (operand loading → SUBLEQ sequence → writeback, checked against an independent architectural specification).
