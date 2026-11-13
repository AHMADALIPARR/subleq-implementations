# tinyprintf.c audit

Audit of the user-supplied `debugger/tinyprintf.c` (Kustaa Nyholm, MIT/BSD/LGPL;
chat prefix stripped; asset line numbers stripped). The original file is kept
**verbatim**. Fixes belong only in `debugger/tinyprintf_checked.c` (and
`tinyprintf_checked.h` if needed).

Tests: `debugger/tests/audit-tinyprintf.c`, compiled with

```
gcc -std=c11 -Wall -Wextra -O0 -g -DTINYPRINTF_OVERRIDE_LIBC=0
    -fsanitize=undefined,address -fno-sanitize-recover=undefined,address
    -I debugger debugger/tests/audit-tinyprintf.c debugger/tinyprintf.c
```

Raw sanitizer logs: `debugger/tests/audit-logs/`. Refined putchw sweep:
`debugger/tests/audit-logs/audit-i4.log`.

Box compiler: gcc (Debian 14.2.0-19) 14.2.0.

## Table

| # | Issue | Location in `tinyprintf.c` | Confirmed? | Evidence | Fix (checked copy only) |
|---|---|---|---|---|---|
| 1 | `i2a` / `li2a` / `lli2a` negate the minimum signed integer (UB) | `i2a` lines 182–188: `if (num < 0) { num = -num; … }`. Same pattern in `li2a` (154–160) and `lli2a` (125–131). | **Yes** | UBSAN: `tinyprintf.c:185:13: runtime error: negation of -2147483648 cannot be represented in type 'int'` with stack `i2a` ← `tfp_format` ← `tfp_vsnprintf` ← `tfp_snprintf("%d", INT_MIN)`. Log: `audit-issue1.err`. | Compute the magnitude in unsigned arithmetic: `ui2a(0u - (unsigned)num, p)` (and the `long` / `long long` analogues). Never negate a signed min. |
| 2 | `a2u`: `digit > base` should be `digit >= base` | `a2u` lines 113–127, condition at line 119: `if (digit > base) break;` | **Yes** | `tfp_snprintf(buf, n, "%10ad", 5)` produced a **110**-character field (`'a'` accepted as decimal width digit 10: `10*10+10=110`) then formatted `5`. glibc treats `%10a` as a hex-float conversion (and warns). The width-110 result is direct evidence that `digit == base` was not rejected. Log: `audit-issue2.err`. | Change the test to `if (digit >= base) break;` so valid digits are `0 .. base-1`. |
| 3 | `tfp_vsnprintf` returns 0 for `size==0` instead of the formatted length | `tfp_vsnprintf` lines 522–540: `if (size < 1) return 0;` | **Yes** | `tfp_snprintf(buf, 0, "hello-%d", 42)` returned **0** and left `buf[0]=='Z'`. glibc `snprintf(NULL, 0, "hello-%d", 42)` returned **8**. Log: `audit-issue3.err`. | Do not early-return. When `size==0`, still run `tfp_format` with a counting (non-writing) putcf, and return the would-be length. Write nothing, including no NUL. Matches C `vsnprintf`. |
| 4 | `putchw`: some precision / zero-pad / alignment combinations format incorrectly vs glibc | `putchw` lines 129–183; flags parsed at 212–259 | **Yes**, on a *supported-flag* sweep, and also a larger incompatibility | Refined sweep (`-`, `0`, `#`, width, precision only; no `+` / space; no `INT_MIN`): **10 diffs** vs glibc (`audit-i4.log`). Confirmed mismatches: (a) `#` on **zero** hex/octal (`%#x` of 0 → tfp `0x0`, glibc `0`; `%#o` of 0 → tfp `00`, glibc `0`; similarly `%#08x`, `%-#8x`, `%#8.3x` of 0); (b) `0` flag on **strings** (`%08s` zero-pads in tfp; glibc space-pads — the `0` flag is for numeric conversions). Additional finding (not in the original putchw claim, but seen in the first sweep): `+` and space flags are **not parsed**, so `%+d` / `% d` are mis-parsed (the flag character is treated as the conversion, the letter `d` is printed literally). | In the checked copy: suppress `#` prefix for a zero hex value; do not emit an extra leading `0` for `#` octal when the value is already zero; ignore the `0` flag for `%s`; optionally accept `+` and space as integer flags so the oracle matches C. |
| 5 | Numeric width/precision parsing can overflow `int` fields | `a2u` line 121: `num = num * base + digit` (`unsigned int`); assignment `p.width = width` / `p.prec = prec` (lines 241–243, 256–258). Also `p.width = -p.width` for negative `*` width (237–238) is UB at `INT_MIN`. | **Yes** | `%9999999999d` (width > `UINT_MAX`): tfp returned `1410065407` (wrapped `unsigned` math), length in a 256-byte buffer was 255. `%2147483648d` (`INT_MAX+1` assigned to `int` width): tfp returned **`-2147483648`**. Control `%200d` matched glibc (len 200). gcc also warned that the converted width exceeds `INT_MAX`. Log: `audit-issue5.err`. | In `a2u`, detect overflow before `num * base + digit` and saturate at `INT_MAX`. Store width/prec as saturated `int`. For `*` width, if the value is `INT_MIN`, do not negate; saturate and set left-align. |
| 6 | `tfp_vsprintf` has no capacity parameter (buffer overrun) | `tfp_vsprintf` / `_vsprintf_putcf` lines 553–573: `data->dest[data->num_chars++] = c` with no bound | **Yes** | ASAN: `stack-buffer-overflow` **WRITE of size 1** at `tinyprintf.c:562` in `_vsprintf_putcf`, called from `tfp_format` ← `tfp_vsprintf` ← `tfp_sprintf` into an 8-byte stack buffer with a ~40-character message. Log: `audit-issue6.err`. | Keep `tfp_vsprintf` as the historical unbounded API (cannot add a capacity parameter without breaking the signature). Add `tfp_vsprintf_checked` / `tfp_sprintf_checked` that take a `size` and delegate to the fixed `tfp_vsnprintf`. The SUBLEQ oracle and formal spec use the bounded entry point. |

## Notes for the SUBLEQ microcode and formal spec

The checked semantics, which the formal development in `formal/lean/` and
the SUBLEQ microcode must follow:

* 16-bit signed min `−32768` is converted via **unsigned magnitude**
  (`0 - bits` in 16-bit wrap), never by signed negation.
* `a2u` rejects `digit >= base`.
* A `vsnprintf`-style writer with `capacity == 0` returns the full
  formatted length and writes nothing; `capacity > 0` NUL-terminates and
  never writes at an index `≥ capacity`.
* Width/precision parsing saturates; it does not wrap.
* Bounded writes only (`tfp_vsprintf_checked`).

Kernel proofs of those properties (decimal correctness, min-int safety,
buffer safety, length, structured SUBLEQ refinement) live in
`formal/lean/` and are summarized in `formal/README.md`.
