# tinyprintf integer formatting as 16-bit SUBLEQ microcode

This note specifies the 16-bit eForth SUBLEQ machine, the canonical
`u16toa` / `i16toa` algorithms (the checked tinyprintf integer core),
the assembler macros, the assembled image, and how it was tested.

The original `debugger/tinyprintf.c` is kept verbatim. The C oracle is
`debugger/tinyprintf_checked.c` (`tfp_u16toa`, `tfp_i16toa`).

## 16-bit SUBLEQ semantics (Howe / eForth)

- Memory is 65536 cells of 16-bit words. Addresses name cells, not bytes.
- Each instruction occupies three cells at `PC`: `A`, `B`, `C`.
- If `A = 0xFFFF`, read a byte (EOF → `0xFFFF`) into `mem[B]` and set `PC := PC+3`.
- Else if `B = 0xFFFF`, write `mem[A] & 0xFF` to the output and set `PC := PC+3`.
- Else `mem[B] := mem[B] - mem[A]` (unsigned 16-bit wrap). If the result is `0`
  or has bit 15 set (i.e. the difference interpreted as `int16` is `≤ 0`),
  `PC := C`; otherwise `PC := PC+3`.
- Halt when `PC ≥ 32768` (a negative branch target, as unsigned, is `≥ 32768`).

This is the same convention as `howerj/subleq` and the unfused path of
`jserv/subleq`. It is **not** the repository's 32-bit directive machine
(`a = -1` word input, `b < 0` word output, `c = -1` halt). The debugger
supports both via `--mode=eforth` (default) and `--mode=directive`.

## Canonical `u16toa` (unsigned 16-bit decimal)

Given `n ∈ [0, 65535]`, produce the exact canonical decimal string
(no leading zeros, except `0` itself):

1. Extract five place digits by *unsigned* comparison against `10000`,
   `1000`, `100`, `10`, then the remainder, counting repeated subtractions.
   Unsigned `N ≥ M` (with `M ∈ 1..32767`) is:
   - if `N = 0`, no;
   - if `N` is signed-`≤ 0` and not zero (`N ≥ 32768`), yes;
   - otherwise a signed compare of `N - M`.
2. Skip leading `'0'` digits, but keep at least one digit.
3. The required length is the number of significant digits.

There is no signed arithmetic in this path.

## Canonical `i16toa` (signed 16-bit decimal)

Given the 16-bit two's-complement pattern of `n ∈ [-32768, 32767]`:

1. If bit 15 is set, emit `-` and replace `n` with the **unsigned 16-bit
   magnitude** `(0 - n) mod 65536`. Never negate a signed `int16`
   (that would overflow on `-32768`).
2. Format the magnitude with `u16toa`.
3. Required length is `u16toa` length plus one if a minus sign was emitted.

This matches `tfp_i16toa` in `tinyprintf_checked.c` and the Lean
`i16toa` / `unsignedMag_eq_natAbs` theorems.

## snprintf-style bounding

Cells `CAP`, `WIDTH`, `BUF`, `LEN`:

- `LEN` is the untruncated length (`max(raw, WIDTH)` if `WIDTH > 0`, else `raw`).
- If `CAP = 0`, write nothing (no NUL).
- If `CAP > 0`, write at most `CAP-1` characters (optional left spaces
  when `WIDTH > raw`, then optional `-`, then digits) and NUL-terminate
  at `min(LEN, CAP-1)`. Never write at an index `≥ CAP`.

## Assembler macros (`microcode/tinyprintf/asm16.c`)

Repo-style names, 16-bit eForth encoding, `Z` is cell 0:

| Macro | Expansion |
|---|---|
| `SUB a b c` | `sq a b c` |
| `ZERO x` | `sq x x next` |
| `MOV src dst` | `ZERO dst`; `sq src Z next`; `sq Z dst next`; `ZERO Z` |
| `ADD src dst` | `sq src Z next`; `sq Z dst next`; `ZERO Z` |
| `NEG x` | `sq x Z next`; `ZERO x`; `sq Z x next`; `ZERO Z` |
| `INC x` | `ADD ONE x` (requires `ONE`) |
| `DEC x` | `sq ONE x next` |
| `JMP l` | `sq Z Z l` |
| `JLEZ x l` | `sq Z x l` (non-destructive: `x -= 0`) |
| `OUT x` | `sq x -1 next` |
| `IN x` | `sq -1 x next` |
| `HALT` | `sq Z Z 32768` |

`LABEL+OFF` is accepted (for `BUF+i`). Source: `microcode/tinyprintf/intfmt.s`.
Listing: `intfmt.lst`. Image: `intfmt.dec` (2323 cells). Boot: `JMP START` at
address 0, which also keeps `Z = 0`.

Runtime cells (from the listing): `INPUT=12`, `CAP=13`, `WIDTH=14`,
`MODE=15` (`0` = u16, `1` = i16), `LEN=16`, `BUF=32` (16 cells).

## Test versus the C oracle

`microcode/tinyprintf/test-oracle` loads `intfmt.dec` into `debugger/subleq_vm`
and, for every `v ∈ 0..65535`, runs both modes with `CAP=8`, `WIDTH=0`,
and compares `LEN` plus the buffer against `tfp_u16toa` / `tfp_i16toa`.
It also checks capacities `0..6` on a sample including `0`, `32767`,
`32768` (`-32768`), and `65535`.

Recorded result (`oracle-counts.txt`):

```
runs=131128 fails=0
u16toa_steps_min=396
u16toa_steps_max=1223
u16toa_steps_mean=934
i16toa_steps_min=411
i16toa_steps_max=1266
i16toa_steps_mean=945
```

Instruction counts come from the VM step counter (the same counter the
debugger profiler uses). They are not estimates.

## Formal layer

Lean 4 proofs live in `formal/lean/` (isolated). Kernel theorems cover
decimal correctness, min-int safety, buffer safety including a general
`snprintf_nul` lemma, and a structured PUT refinement. The assembled
image is imported as `IntFmt.intfmtImage`. `runImage` is defined on the
Lean `Subleq` machine with fuel `intfmtFuel = 2000` (strictly above the
measured max of 1266). The statement that every Int16 run of the *image*
matches the spec is **C-oracle evidence**, not a kernel proof of the
2323-cell program. See `formal/README.md`.
