<!-- SPDX-License-Identifier: AGPL-3.0-or-later -->
# The directive SUBLEQ machine: parameters, macros and measured cost

This paper describes the SUBLEQ machine defined in
[`semantics/subleq-spec.md`](../semantics/subleq-spec.md) (the *directive
machine*). It compares that machine with the original SUBLEQ interpreter in
this repository, [`racket/subleq-original.rkt`](../racket/subleq-original.rkt)
(the *original machine*). Every number below comes from a command in
section 10, run on the toolchain listed there. `make bench` writes its
tables to `verification-results/bench.md` (git-ignored); the tables here
are copied from that run and from the output of `make test`.

## 1. Summary

* **SHA-256** (FIPS 180-4) runs as a SUBLEQ program on both machines. On the
  directive machine one 433,968-cell image hashes any message (input is the
  length and then the bytes; output is 8 words). It gives the NIST digests
  for `""`, `"abc"` and the 448-bit two-block message on the Racket, Forth,
  Factor and Lean implementations, each with the same instruction count. The
  original-machine version gives the same digests.
* **SHA-256 gains little.** The original machine needs 105,672 instructions
  per 64-byte block and the directive machine 104,159: **1.45 % more** on
  the original. The bit-sliced design spends almost all its instructions on
  work both machines do the same way, so 32-bit wrap and I/O have little to
  remove.
* **The keystream program (the "killer app") gains more.** It is a toy
  LCG stream cipher, not a secure one. The original needs 178.9 instructions
  per word and the directive machine 102: **1.754 times as many** on the
  original. Its image also grows by 2 cells per word, while the directive
  image stays at 704 cells for any stream length.
* **The keystream program fails on the original machine without wrap
  emulation.** The unchanged directive image does not work there either.
  Without wrap emulation, 0 of N output words are correct for every N
  tested, and the LCG state cell grows by about 20.7 bits per word. Run time
  grows roughly quadratically: 30.2 ms for 1,000 words, 1,935.0 ms for
  8,000. The unchanged directive image ran on the original until the
  10,000,000-step limit and produced no result.
* **No claim of novelty against the literature is made** (section 8). The
  comparison is only between the two machines in this repository.

## 2. The two machines

| | Directive machine | Original machine |
|---|---|---|
| Definition | `semantics/subleq-spec.md` | `racket/subleq-original.rkt` |
| Implementations | Racket (`racket/subleq.rkt`), Forth (`forth/`), Factor (`factor/`), Lean (`lean/`) | Racket only |
| Cell values | 32-bit two's complement; every result wraps | unbounded integers |
| Branch | if the wrapped result `r <= 0` | if the exact result `<= 0` |
| Jump target | absolute `c` | absolute `c` |
| Halt | `c = -1` (after the instruction's effect) | `PC < 0`, `PC + 2 >= N`, or `a < 0` and `b < 0` |
| Input | `a = -1`: next input word into `M[b]` | none |
| Output | `b < 0`: append `M[a]` to the output | none |
| Trap | `a = -2`: stop with status `trap`, `CODE = b` | none |
| Out-of-range access | reads give 0, writes are discarded; a PC outside memory is a fault | Racket error (`vector-ref: index is out of range`) |
| Result | STATUS, PC, STEPS, CODE, OUTPUT, MEM | the final memory vector |

To count instructions on the original machine, `racket/subleq-original.rkt`
gained `execute-subleq/steps`, which returns the memory and the number of
instructions executed. `execute-subleq` now calls it and returns only the
memory, so it behaves as before. Its test module checks the count on three
programs.

## 3. The parameter space

Each row is one design choice, with the alternatives and what was observed
in this repository.

| Parameter | Directive choice | Alternatives | Observed consequence |
|---|---|---|---|
| Word size | 32-bit signed, wrap on every result | unbounded (original); other widths (8, 16, 64); saturating | The original must reduce values itself with `MOD32` (section 4). SHA-256 on the original costs +1.45 % per block; the keystream costs ×1.754 per word. Without the reduction the keystream output is wrong (section 7). |
| Branch test | wrapped `r <= 0` | exact `r <= 0`; `r < 0` (SUBLEZ vs SUBLZ variants) | Same instruction, different results near the edges. `4 3 6 -2147483648 1 0 0 0 -1`: the directive machine stores 2147483647 in cell 3 and does not branch (3 steps, halts). The original stores -2147483649, branches, and halts after 2 steps. |
| Sign of a word | signed words: bit 31 set means x < 0 | canonical unsigned words, where bit 31 set means x > 2^31 - 1 (original) | `JSIGN`: 2-3 executed instructions on both machines (static 5 directive, 4 original). |
| Jump target | absolute `c` | relative `c` (PC + c) | Not varied; both machines use absolute targets. |
| Halt | `c = -1` | any negative PC (original, and common in the literature); a halt opcode; running off the end of memory | `HALT` is `sq Z Z -1` and is 1 instruction on both. The original also halts when `a < 0` and `b < 0` and at the end of memory; the directive machine faults if the PC leaves memory. |
| Input | `a = -1` reads one word into `M[b]` | no input (original), with data preloaded in the image; memory-mapped input | `IN` is 1 instruction. Its replacement `LOAD-NEXT` is 9, and the image must hold the data. |
| Output | `b < 0` appends `M[a]` | no output (original), with results left in memory; memory-mapped output | `OUT` is 1 instruction. Its replacement `STORE-NEXT` is 13, and the image needs room for the results. |
| Trap | `a = -2`, `CODE = b`, PC and memory unchanged | none (original), writing a status cell and halting; a fault | `TRAP` is 1 instruction. The keystream program stops bad headers in 7 or 15 steps with CODE 1 or 2 (section 7). |
| Out-of-range access | reads 0, writes discarded | Racket error (original); wrap the address; fault | On the original, `(execute-subleq '(100 0 -1))` raises `vector-ref: index is out of range`. The directive machine returns a result for every program. |
| Priority | trap > input > output > ordinary | other orders | Fixed by the spec, so `-1 -1 c` is an input and `-2 -1 c` is a trap. Not varied. |

Points in the space that were not explored: other word widths, relative
jumps, and the `r < 0` branch. The table records them as alternatives only.

## 4. The macro library

[`asm/sasm.rkt`](../asm/sasm.rkt) is a small assembler written in Racket. It
has two targets, `'directive` and `'original`, and both SUBLEQ programs are
written with it. A macro expands to a fixed list of `sq a b c` instructions
(`M[b] -= M[a]; if M[b] <= 0 goto c`). `K v` is a constant cell holding v,
and `Z` (`K0`) is a cell that holds 0 before and after every macro.

The full expansions of every macro on both targets are in
[`docs/macro-expansions.md`](macro-expansions.md), generated by
`racket asm/macro-table.rkt --expansions`.

### 4.1 Cost table

`make macros` (`racket asm/macro-table.rkt`) runs each macro on both
interpreters. It compares the result with an independently computed value
and measures how many instructions run. The harness overhead is subtracted.
"Cases" is the number of operand values tried; all were correct.

| Macro | What it does | Directive: static / executed | Original: static / executed | Cases |
|---|---|---|---|---|
| `ZERO x` | x := 0 | 1 / 1 | 1 / 1 | 12 |
| `SUB a b` | b := b - a | 1 / 1 | 1 / 1 | 144 |
| `ADD a b` | b := b + a | 3 / 3 | 3 / 3 | 144 |
| `MOV a b` | b := a | 4 / 4 | 4 / 4 | 144 |
| `NEG-INTO a b` | b := -a | 2 / 2 | 2 / 2 | 144 |
| `INC x`, `DEC x` | x := x ± 1 | 1 / 1 | 1 / 1 | 12 each |
| `DOUBLE x` | x := 2x | 3 / 3 | 3 / 3 | 12 |
| `JLEZ x l` | jump if x <= 0 (signed on the directive machine; canonical words on the original, so only x = 0) | 1 / 1 | 1 / 1 | 12 |
| `JSIGN x l` | jump if bit 31 of x is set | 5 / 2-3 | 4 / 2-3 | 12 |
| `MOD32 x 3` | x := x mod 2^32, for 0 <= x < 2^35 (original only) | - | 12 / 6-9 | 8 |
| `ADD32 a b` | b := b + a mod 2^32 | 3 / 3 | 7 / 5-6 | 144 |
| `SHL1 x` | x := 2x mod 2^32 | 3 / 3 | 7 / 5-6 | 12 |
| `ROTL1 x` | rotate left by 1 | 13 / 6-7 | 6 / 5 | 12 |
| `ROTR x 7` | rotate right by 7 (as 25 `ROTL1`) | 325 / 150-175 | 150 / 125 | 12 |
| `MULK x 1664525` | x := 1664525·x mod 2^32 (shift and add) | 91 / 91 | 175 / 133-145 | 12 |
| `UNPACK32 w bits v` | 32 cells of 0/1 from word w | 134 / 97-101 | 130 / 98 | 12 |
| `ACC+PARITY acc s (x y z)` | acc := acc + (x xor y xor z) | 10 / 5-7 | 10 / 5-7 | 8 |
| `ACC+PARITY acc s (x y)` | acc := acc + (x xor y) | 7 / 4-6 | 7 / 4-6 | 4 |
| `ACC+CH acc e f g` | acc := acc + Ch(e, f, g) on bits | 6 / 2-4 | 6 / 2-4 | 8 |
| `ACC+MAJ acc s a b c` | acc := acc + Maj(a, b, c) on bits | 7 / 6 | 7 / 6 | 8 |
| `IN x` | read one word into x | 1 / 1 | - | 1 |
| `OUT x` | write x | 1 / 1 | - | 1 |
| `TRAP code` | stop with status trap | 1 / 1 | - | 1 |
| `HALT` | stop | 1 / 1 | 1 / 1 | 1 |
| `LOAD-NEXT ptr dst` | dst := M[ptr]; ptr := ptr + 1 (self-modifying) | 9 / 9 | 9 / 9 | 1 |
| `STORE-NEXT src ptr` | M[ptr] := src; ptr := ptr + 1 (self-modifying) | 13 / 13 | 13 / 13 | 1 |

The table shows where wrap-around helps and where it does not:

* Additions and shifts that must stay 32-bit (`ADD32`, `SHL1`, `MULK`)
  are cheaper on the directive machine, because the original adds `MOD32`
  after them.
* `ROTL1` and `ROTR` are cheaper on the **original**. On canonical unsigned
  words, the top bit is a single compare against 2^31 - 1. On signed words
  the directive version needs a 3-way branch.
* `UNPACK32` costs about the same on both: 97-101 against 98.
* The bit-level macros that SHA-256 uses most (`ACC+PARITY`, `ACC+CH`,
  `ACC+MAJ`) have exactly the same expansion on both machines.

### 4.2 Selected expansions

`ADD a b` (both targets):

```
  sq a K0 next
  sq K0 b next
  sq K0 K0 next
```

`IN x` on the directive machine, and its replacement `LOAD-NEXT p d` on
either machine (the expansion is the same on both; instructions 1-4 write
the address in `p` into the `a` field of `LD1`):

```
  sq -1 x next            | sq LD1 LD1 next
                          | sq p K0 next
                          | sq K0 LD1 next
                          | sq K0 K0 next
                          | sq d d next
                          | LD1:
                          | sq 0 K0 next
                          | sq K0 d next
                          | sq K0 K0 next
                          | sq K-1 p next
```

`ADD32 a b` on the original machine: `ADD` followed by one compare-subtract
step that removes 2^32 if the sum is too large. On the directive machine
`ADD32` is plain `ADD`.

```
  sq a K0 next
  sq K0 b next
  sq K0 K0 next
  sq K4294967295 b M1
  sq K1 b M2
  sq K0 K0 M2
M1:
  sq K-4294967295 b M2
M2:
```

`MOD32 x k` (original only) repeats that step k times. It subtracts
2^(31+k), then 2^(30+k), ..., then 2^32, each only if the value is large
enough, so it reduces any 0 <= x < 2^(32+k). `MOD32 x 2`:

```
  sq K8589934591 x M1
  sq K1 x M2
  sq K0 K0 M2
M1:
  sq K-8589934591 x M2
M2:
  sq K4294967295 x M3
  sq K1 x M4
  sq K0 K0 M4
M3:
  sq K-4294967295 x M4
M4:
```

`JSIGN x l` on the directive machine (x is signed; the sign bit set means
x <= -1) and on the original machine (x is canonical; the bit is set when
x > 2^31 - 1):

```
  sq K0 x J1              | sq K2147483647 x J1
  sq K0 K0 J3             | sq K-2147483647 x l
J1:                       | sq K0 K0 l
  sq K-1 x J2             | J1:
  sq K1 x J3              | sq K-2147483647 x J2
J2:                       | J2:
  sq K1 x l               |
J3:                       |
```

## 5. SHA-256 in SUBLEQ

Source: [`programs/sha256.rkt`](../programs/sha256.rkt). It generates the
image for either target.

* The constants H and K are computed from the first 8 and 64 primes with
  exact integer roots. They are checked against the first and last values
  from FIPS 180-4.
* Each word is unpacked into 32 bit cells with `UNPACK32`. ROTR and SHR then
  cost nothing: they only change which cells are read. Σ0, Σ1, σ0, σ1, Ch
  and Maj are computed bit by bit and summed straight into a word with
  Horner's rule (acc := 2·acc + bit).
* The 48 schedule steps and the 64 rounds are fully unrolled. The loop over
  64-byte blocks is the only loop. The program pads the message itself.
* **Directive machine:** the input is `L, b0, ..., b(L-1)`. The output is
  H0..H7 as 8 words (signed 32-bit, printed as hex by the test harness), and
  the program halts with `c = -1`. The same image is used for every message.
* **Original machine:** `LEN` and the message bytes are part of the image
  and are read with `LOAD-NEXT`. Sums are reduced with `MOD32`, with k set
  from the largest possible sum at each place (T1: 3, new a: 2, new e: 1,
  schedule: 2, H update: 1). The digest is left in the `H` cells.
* Limit: messages shorter than 2^28 bytes. Both image builders check this.

### 5.1 NIST results

The vectors are `"abc"` and the 448-bit message from FIPS 180-2 Appendix
B.1/B.2, and `""` from NIST CAVP `SHA256ShortMsg.rsp` (Len = 0). The checker
is `bench/sha256-vectors.rkt` (`make sha256`). Each command-line run must
exit 0, halt, and print the expected digest. Its whole canonical result
(including memory) must also equal the in-process Racket reference. The run
in `make test` gave `checks=18 failures=0`:

| Vector | Digest printed (all 6 runs) | Directive STEPS (Racket in-process, Racket CLI, Forth, Factor, Lean) | Original STEPS |
|---|---|---|---|
| `""` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 101,967 on all five | 102,977 |
| `"abc"` | `ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad` | 102,856 on all five | 103,842 |
| 448-bit | `248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1` | 206,160 on all five | 208,678 |

`raco test programs/sha256.rkt` also checks messages of 1, 54, 55, 56, 57,
63, 64, 65, 119, 120, 128 and 200 seeded random bytes on both machines
against a plain-Racket SHA-256 (`sha256-bytes`). These lengths cover the
padding boundaries.

## 6. Benchmarks

### 6.1 SHA-256 instruction counts (`make bench`, table A)

| Message | Bytes | Blocks | Directive STEPS | Original STEPS | Original - directive | Difference | I/O part (exact) | Image cells: directive / original |
|---|---|---|---|---|---|---|---|---|
| NIST `""` | 0 | 1 | 101,967 | 102,977 | 1,010 | +0.99 % | -9 | 433,968 / 439,014 |
| NIST `"abc"` | 3 | 1 | 102,856 | 103,842 | 986 | +0.96 % | 15 | 433,968 / 439,016 |
| NIST 448-bit | 56 | 2 | 206,160 | 208,678 | 2,518 | +1.22 % | 439 | 433,968 / 439,069 |
| random 55 | 55 | 1 | 103,684 | 105,153 | 1,469 | +1.42 % | 431 | 433,968 / 439,068 |
| random 119 | 119 | 2 | 207,561 | 210,603 | 3,042 | +1.47 % | 943 | 433,968 / 439,132 |
| random 183 | 183 | 3 | 311,966 | 316,490 | 4,524 | +1.45 % | 1,455 | 433,968 / 439,196 |
| random 247 | 247 | 4 | 416,161 | 422,169 | 6,008 | +1.44 % | 1,967 | 433,968 / 439,260 |

* **I/O part.** This is 8 per message byte (`LOAD-NEXT` is 9 instructions,
  `IN` is 1), minus the 9 I/O instructions that only the directive program
  runs (one `IN` for the length, 8 `OUT` for the digest).
* **The rest of the difference** comes from two places: `MOD32`, which only
  the original runs, and the different bit-31 handling inside `UNPACK32`.
* **Marginal cost per block.** (STEPS(247 B) - STEPS(55 B)) / 3 is 104,159.0
  on the directive machine and 105,672.0 on the original. The original
  needs **1.015 times as many (+1.45 %)**.
* **Data dependence.** Costs vary slightly with the data, because
  `UNPACK32`, `ACC+PARITY` and `ACC+CH` take data-dependent paths.

Why the gain is small: per block, SHA-256 here spends nearly all of its
instructions on unpacking and bit-level logic. Those cost the same on both
machines (section 4.1). Only the 32-bit additions benefit from wrap-around.
A different SHA-256 design, for example one that works on whole words with
rotations, would give a different ratio. Such a design was not written or
measured.

### 6.2 Keystream instruction counts (`make bench`, table B)

| N words | Directive STEPS | Original STEPS | Original / directive | Image cells: directive / original |
|---|---|---|---|---|
| 0 | 15 | 11 | 0.733 | 704 / 1,430 |
| 1,000 | 102,014 | 178,798 | 1.753 | 704 / 3,428 |
| 10,000 | 1,020,014 | 1,788,833 | 1.754 | 704 / 21,428 |

Marginal cost per word, (STEPS(10000) - STEPS(1000)) / 9000: the directive
machine 102.000, the original 178.893, ratio 1.754. With an empty stream the
original is cheaper, because the directive program reads the 3-word header
with `IN`.

This table (key 12345) and section 7.3 (key 987654321) use different keys
and random words, so their original STEPS differ slightly (178,798 here, 178,979 there for N = 1,000). The cost
of `MOD32` depends on the data. The directive counts do not depend on the
data.

### 6.3 Wall-clock time (`make bench`, table C; secondary data)

Medians of 3 runs, in milliseconds.

* **Command-line rows.** "Total" is the whole process. "Load only" is the
  same input file with FUEL = 0: parse, load and print, with no instructions
  executed. "Execution" is total minus load.
* **In-process rows** time only the interpreter call, after the image has
  been built.
* **SHA-256 message.** A 4,087-byte (64-block) seeded random message is
  used, so that execution is not lost in the time to load the 434,000-cell
  image.

| Program | Machine / implementation | STEPS | Total | Load only | Execution | Instructions/s (execution) |
|---|---|---|---|---|---|---|
| SHA-256, 4,087 B (64 blocks) | directive / Racket in process | 6,661,851 | 115.8 | - | 115.8 | 57,504,787 |
| SHA-256, 4,087 B | directive / Racket CLI | 6,661,851 | 605.0 | 543.9 | 61.0 | 109,132,052 |
| SHA-256, 4,087 B | directive / Forth | 6,661,851 | 1,096.7 | 296.5 | 800.3 | 8,324,677 |
| SHA-256, 4,087 B | directive / Factor | 6,661,851 | 2,302.5 | 982.7 | 1,319.8 | 5,047,778 |
| SHA-256, 4,087 B | directive / Lean | 6,661,851 | 1,517.2 | 249.2 | 1,268.0 | 5,253,917 |
| SHA-256, 4,087 B | original / Racket in process | 6,758,843 | 60.6 | - | 60.6 | 111,555,253 |
| Keystream, 10,000 words | directive / Racket in process | 1,020,014 | 15.1 | - | 15.1 | 67,329,176 |
| Keystream, 10,000 words | directive / Racket CLI | 1,020,014 | 164.0 | 149.8 | 14.3 | 71,466,060 |
| Keystream, 10,000 words | directive / Forth | 1,020,014 | 139.9 | 14.0 | 125.9 | 8,100,482 |
| Keystream, 10,000 words | directive / Factor | 1,020,014 | 1,022.4 | 412.1 | 610.4 | 1,671,195 |
| Keystream, 10,000 words | directive / Lean | 1,020,014 | 449.7 | 14.5 | 435.2 | 2,343,671 |
| Keystream, 10,000 words | original / Racket in process | 1,788,833 | 13.7 | - | 13.7 | 130,593,162 |

Every timed run was checked: each digest or output equals the plain-Racket
reference, each command-line run printed the same STEPS, and each FUEL = 0
run executed 0 instructions.

What the wall-clock numbers measure:

* **They measure interpreters, not machines.** The original Racket
  interpreter runs about twice as many instructions per second as
  `racket/subleq.rkt`, which by its specification wraps every result and
  checks for traps, I/O and the halt rule on every step. As a
  result, the original finished SHA-256 in less wall-clock time
  (60.6 ms against 115.8 ms) even though it ran 1.45 % more instructions.
  For the keystream the two are close: 13.7 ms against 15.1 ms. Instruction
  counts are the primary comparison.
* **Factor's per-instruction rate is low on the keystream.** In the Factor
  runner each input read uses `unclip`, which, from reading the code, copies
  the remaining input sequence. That would make input cost grow with the
  stream length. This explanation was not profiled.
* **Execution times are a difference of two medians.** They carry the noise
  of both. When loading dominates, the noise is large. For the Racket
  command line on SHA-256, an earlier run of the same `make bench` gave
  131.2 ms of execution (587.8 total, 456.6 load only), against 61.0 ms
  here. The in-process rows avoid this problem.

## 7. The killer app: a streaming keystream filter

Source: [`programs/keystream.rkt`](../programs/keystream.rkt).

* x(0) = seed and x(i+1) = 1664525·x(i) + 1013904223 mod 2^32.
* Encrypt: c(i) = p(i) + x(i+1) mod 2^32. Decrypt: p(i) = c(i) - x(i+1).
* It is a toy cipher and not secure.
* It uses every directive parameter:
  * The LCG and the addition rely on 32-bit wrap. There is no reduction
    code.
  * Words stream in with `IN` and out with `OUT`, so the image is 704 cells
    for any stream length.
  * A negative count (CODE 1) or a mode other than 1 or -1 (CODE 2) stops
    the machine with a trap.
  * The program halts on `c = -1`.

The input is `MODE SEED N w1 ... wN`. The program is checked against a
plain-Racket reference (`keystream-reference`). Evidence comes from
`bench/killer-app.rkt` (`make killer-app`, part of `make test`), which gave
`checks=24 failures=0`. It uses random words from seed 20261110 and key
987654321.

### 7.1 Correct on all four directive implementations

| N words | Racket in-process | Racket CLI | Forth | Factor | Lean |
|---|---|---|---|---|---|
| 1,000 | halted, 102,014 steps, output = reference | same | same | same | same |
| 10,000 | halted, 1,020,014 steps, output = reference | same | same | same | same |

Each command-line result is identical to the in-process canonical result.
Decrypting each ciphertext with the same image (MODE -1) gave back the
plaintext (checked in process).

### 7.2 Bad headers trap

| Header (MODE SEED N) | Result on all five runs |
|---|---|
| `1 0 -1` | STATUS trap, CODE 1, 7 steps |
| `7 0 0` | STATUS trap, CODE 2, 15 steps |

### 7.3 On the original machine

**(a) The directive image, unchanged.** The original has no I/O, so the
stream cannot be given to it. Run on `racket/subleq-original.rkt`, the image
was still running at the 10,000,000-step limit and had printed nothing. At
that point MODE, X and N held 0, 0, 0, and 2 of the 704 cells differed from
the loaded image.

**(b) The same algorithm ported to the original, with wrap emulated and the
data preloaded:**

| N words | Machine | Image cells | STEPS | Output = reference |
|---|---|---|---|---|
| 1,000 | directive image | 704 | 102,014 | yes |
| 1,000 | original (port) | 3,428 | 178,979 | yes |
| 10,000 | directive image | 704 | 1,020,014 | yes |
| 10,000 | original (port) | 21,428 | 1,789,082 | yes |

Marginal instructions per word: 102.000 on the directive machine and
178.900 on the original, ratio 1.754.

**(c) The port without wrap emulation (`MOD32` removed):**

| N words | STEPS | Run time (ms, in process, median of 3) | Output words equal to the reference | Bits in the LCG state cell at the end |
|---|---|---|---|---|
| 250 | 30,511 | 2.7 | 0 of 250 | 5,197 |
| 500 | 61,011 | 8.9 | 0 of 500 | 10,364 |
| 1,000 | 122,011 | 30.2 | 0 of 1,000 | 20,697 |
| 2,000 | 244,011 | 117.6 | 0 of 2,000 | 41,364 |
| 4,000 | 488,011 | 470.9 | 0 of 4,000 | 82,697 |
| 8,000 | 976,011 | 1,935.0 | 0 of 8,000 | 165,364 |

What these runs show:

* **Without the reduction the output is wrong.** The LCG state grows by
  about 20.7 bits per word, which matches log2(1664525) ≈ 20.67, so every
  output word is wrong.
* **Time grows roughly quadratically.** Each step works on a larger
  integer: 8 times the words took 64 times as long (1,000 → 8,000).
* **The per-word cost splits as follows.** Without `MOD32` the port runs
  122 instructions per word against the directive machine's 102. Those 20
  are exactly the I/O replacement cost: `LOAD-NEXT` + `STORE-NEXT` = 22,
  against `IN` + `OUT` = 2. Wrap emulation accounts for the remaining
  178.9 - 122 = 56.9 per word.

## 8. Prior art and what is claimed

The SUBLEQ literature already has:

* memory-mapped I/O at address -1;
* halting by jumping to a negative address;
* sign-bit tests that depend on fixed-width cells.

See the [esolangs.org Subleq page](https://esolangs.org/wiki/Subleq) and the
implementations it links. This paper does **not** claim that the directive
parameter set is new in the literature. It claims only what was measured:
the differences between the directive machine and
`racket/subleq-original.rkt` on the programs above.

## 9. Limitations

* **One design per program.** Each program has one design, used on both
  machines. A program written specially for the original, or a word-level
  SHA-256, could change the ratios. Neither was written.
* **Wall-clock times depend on the interpreters** (section 6.3), not only on
  the machines.
* **The Lean implementation is used here as a runner.** No proofs about
  these programs were written.
* **SHA-256 input.** Messages must be shorter than 2^28 bytes. The
  directive program does not check that the input words are bytes
  (0..255).
* **The keystream is a toy cipher.** An LCG keystream is not secure.
* **Forth capacity.** `forth/main.fs` keeps its capacity of 1,000 cells and
  1,000 input words. The SHA-256 image needs `forth/main-large.fs`
  (4,000,000 cells and 1,000,000 input words, `gforth -m 64M`), which sets
  the capacity hook in `forth/subleq.fs` and then loads `main.fs`.
* **Thin macro tests.** `LOAD-NEXT` and `STORE-NEXT` are tested with one
  case each in the macro table. They are also exercised by every
  original-machine run of both programs.

## 10. Reproduce

Toolchain used for the numbers above (as recorded by `make bench`, run
2026-11-10 21:24 PST):

| Tool | Version |
|---|---|
| Racket | 9.3 (CS) |
| gforth | 0.7.3 |
| Factor | 0.102 |
| Lean | 4.35.0 (x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release) |
| OS | Linux 6.12.113+ x86_64 |
| CPU | Intel(R) Xeon(R) Processor (8 logical CPUs) |

The seed for all random data is 20261110 (`random-seed` in Racket). Commands
are run from the repository root:

```
make test FACTOR=/path/to/factor      # everything below, plus the existing tests
make sha256 FACTOR=/path/to/factor    # NIST vectors on all machines (section 5.1)
make killer-app FACTOR=/path/to/factor  # section 7
make bench FACTOR=/path/to/factor     # section 6; writes verification-results/bench.md
make macros                           # section 4.1
racket asm/macro-table.rkt --expansions > docs/macro-expansions.md
racket programs/sha256.rkt OUT.txt "abc"   # write a directive input file for one message
```

Instruction counts are deterministic and should be identical on any machine.
Wall-clock times will differ.
