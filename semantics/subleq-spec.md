<!-- SPDX-License-Identifier: AGPL-3.0-or-later -->
# SUBLEQ machine specification (directive semantics)

This file is the single source of truth for the "directive" SUBLEQ machine
implemented by `racket/subleq.rkt`, `factor/subleq.factor`,
`forth/subleq.fs` and `lean/Subleq/*.lean`.

Rules chosen by the repository owner: 32-bit signed cells with wrapping
subtraction; branch on the wrapped result `r <= 0`; absolute branch target
`c`; halt when `c = -1`; `a = -1` input, `b < 0` output, `a = -2` trap;
out-of-range reads give 0 and out-of-range writes are discarded.

Details this specification adds to make those rules precise are marked
**(detail)** below: the trap leaves `PC` unchanged and ignores `c`; the
priority order trap > input > output > ordinary; the fetch fault; the
`input-exhausted` fault; wrapping of input words and of the initial image;
how steps are counted; and the step limit.

The original, unbounded-integer SUBLEQ interpreter is kept unchanged in
behaviour as `racket/subleq-original.rkt` (see "Baseline" at the end). It
does **not** follow this specification.

## 1. State

| Component | Meaning |
|---|---|
| `M[0..N-1]` | memory, `N` cells, each a 32-bit signed two's-complement integer |
| `PC` | program counter, an integer |
| `IN` | finite list of input words still to be read |
| `OUT` | list of words written so far (initially empty) |
| `STATUS` | `running`, `halted`, `trap`, or `fault` (with a reason) |
| `CODE` | trap code (the `b` operand of the trap instruction); 0 otherwise |
| `STEPS` | number of instructions executed |

**(detail)** The initial memory image is reduced with `wrap` cell by cell when it is
loaded (images in the fixtures are already in range, except one fixture
that checks this rule).

Initial state: `PC = 0`, `STATUS = running`, `OUT = []`, `CODE = 0`, `STEPS = 0`.

## 2. Helper functions

* `wrap(x)` = the unique `y` with `-2^31 <= y < 2^31` and `y ≡ x (mod 2^32)`.
* `in(a)` is true iff `0 <= a < N`.
* `read(a)` = `M[a]` if `in(a)`, otherwise `0`.
* `write(a, v)`: sets `M[a] := v` if `in(a)`, otherwise does nothing (the write is discarded).

## 3. One step

A step is only taken when `STATUS = running`. Any other status is final:
the state no longer changes.

1. **Fetch (detail).** If `PC < 0` or `PC + 2 >= N`, the instruction cannot be
   fetched: `STATUS := fault pc-out-of-range`. Nothing else changes and
   `STEPS` is not incremented.
2. Otherwise `a = M[PC]`, `b = M[PC+1]`, `c = M[PC+2]`. All three are
   read before any write, so an instruction that overwrites its own `c`
   still branches to, and applies the halt rule to, the fetched `c`.
3. The instruction is classified by the first matching rule, in this
   priority order (highest first; the order is a **(detail)**):

| Priority | Condition | Effect |
|---|---|---|
| 1 | `a = -2` | **Trap.** `STATUS := trap`, `CODE := b`, `STEPS += 1`. Memory, `PC`, `IN`, `OUT` are unchanged. The `c` operand is ignored. |
| 2 | `a = -1` | **Input.** If `IN` is empty: `STATUS := fault input-exhausted`, nothing else changes, `STEPS` not incremented. Otherwise let `v = wrap(head IN)`; `IN := tail IN`; `write(b, v)`; `PC := PC + 3`; `STEPS += 1`. |
| 3 | `b < 0` | **Output.** `OUT := OUT ++ [read(a)]`; `PC := PC + 3`; `STEPS += 1`. Memory is unchanged. |
| 4 | otherwise | **Ordinary SUBLEQ.** `r = wrap(read(b) - read(a))`; `write(b, r)`; `PC := c` if `r <= 0`, else `PC := PC + 3`; `STEPS += 1`. |

4. **Halt rule.** After an Input, Output or Ordinary step has completed
   its effect, if `c = -1` then `STATUS := halted`. This applies whether
   or not the branch was taken: an ordinary instruction with `c = -1`
   always halts after one execution, which matches the halt rule in
   `racket/model.rkt` (it stops on `jump == -1` regardless of the
   branch). The reported `PC` is the value computed in step 3 (so it is
   `-1` if an ordinary branch was taken, else the old `PC + 3`).

Notes that follow directly from the table:

* Rules are exclusive and the order is fixed: a trap is never an input
  or output, and `a = -1` with `b < 0` is an input (the value is
  discarded by `write`), not an output.
* The branch test uses the **wrapped** result `r`. For example
  `read(b) = -2^31`, `read(a) = 1` gives `r = 2^31 - 1 > 0`, so no branch.
* The branch target `c` is **absolute**.
* In an ordinary instruction `a` may be any negative number other than
  `-1`/`-2`; it simply reads 0. `b >= 0` there, but `b` may still be
  `>= N`, in which case the write is discarded (the branch still uses `r`).

## 4. Running (detail)

`run(fuel)` repeats steps while `STATUS = running` and fewer than `fuel`
steps have been executed. If the fuel is used up while the status is
still `running`, the reported status is `step-limit`. This is a property
of the runner, not of the machine.

## 5. Canonical serialized result

All implementations print exactly these six lines (single spaces, no
trailing spaces, numbers in decimal with a leading `-` when negative):

```
STATUS <halted|trap|fault:pc-out-of-range|fault:input-exhausted|step-limit>
PC <pc>
STEPS <steps>
CODE <code>
OUTPUT <o1> <o2> ...
MEM <m0> <m1> ... <mN-1>
```

`OUTPUT` and `MEM` are followed by nothing when the list is empty.

## 6. Input file format (for the command-line runners)

Whitespace-separated decimal integers:

```
N  m0 ... mN-1  K  i0 ... iK-1  FUEL
```

The differential runner generates these files from
`verification/fixtures/*.json`. `forth/main.fs` has a capacity of 1000
memory cells and 1000 input words (the defaults of the capacity hook in
`forth/subleq.fs`); larger files are rejected by its loader with an error
(non-zero exit status). `forth/main-large.fs` is the same driver with
4,000,000 memory cells and 1,000,000 input words (run it with
`gforth -m 64M`); it is used for the SHA-256 image (about 434,000 cells).

## 7. Baseline (original semantics)

`racket/subleq-original.rkt` keeps the repository's original interpreter:
unbounded integers, no I/O, halting when `PC < 0`, when `PC + 2 >= N`,
or when both `a < 0` and `b < 0`. It is provided only as a benchmark
baseline and is not compared against this specification.
