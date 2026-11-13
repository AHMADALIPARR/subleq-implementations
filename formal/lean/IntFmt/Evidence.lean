/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Supporting evidence (not an authoritative kernel proof): an exhaustive
*executable* check that `i16toa` matches `intToDec` on every 16-bit
signed integer. This is run from `Main` as an IO program; it is not
used with `native_decide`, so it introduces no extra axioms.

The general theorem `i16toa_eq_intToDec` already covers every in-range
value as a kernel proof.
-/

import IntFmt.Decimal

namespace IntFmt

def checkOne (n : Int) : Bool :=
  if h : -32768 ≤ n ∧ n ≤ 32767 then
    i16toa n h == intToDec n
  else
    false

def checkAll : Bool :=
  (List.range 65536).all (fun k =>
    checkOne ((k : Int) - 32768))

theorem check_zero : checkOne 0 = true := by
  have h : -32768 ≤ (0 : Int) ∧ (0 : Int) ≤ 32767 := by omega
  simp [checkOne, h, i16toa_eq_intToDec 0 h]

theorem check_min : checkOne (-32768) = true := by
  have h : -32768 ≤ (-32768 : Int) ∧ (-32768 : Int) ≤ 32767 := by omega
  simp [checkOne, h, i16toa_eq_intToDec (-32768) h]

theorem check_max : checkOne 32767 = true := by
  have h : -32768 ≤ (32767 : Int) ∧ (32767 : Int) ≤ 32767 := by omega
  simp [checkOne, h, i16toa_eq_intToDec 32767 h]

end IntFmt
