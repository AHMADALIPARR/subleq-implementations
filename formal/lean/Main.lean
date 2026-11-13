/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Driver: print axioms of the authoritative theorems, and run the
exhaustive executable sweep as supporting evidence.
-/

import IntFmt

open IntFmt

#print axioms divmodSub_eq
#print axioms value_uToDigits
#print axioms unsignedMag_eq_natAbs
#print axioms i16toa_eq_intToDec
#print axioms i16toa_minInt
#print axioms snprintf_length
#print axioms snprintf_buf_length
#print axioms snprintf_cap0
#print axioms snprintf_cap1
#print axioms snprintf_index_lt_cap
#print axioms subleqI16toa_refines_spec
#print axioms putAll_i16toa
#print axioms run_fuel0_halted
#print axioms check_min
#print axioms Subleq.sub_defined

def main : IO Unit := do
  IO.println "IntFmt formal driver"
  IO.println "Authoritative theorems live in IntFmt.Decimal, Buffer, Refinement."
  IO.println "Running exhaustive executable check over 65536 Int16 values..."
  if checkAll then
    IO.println "checkAll: PASS (i16toa = intToDec on every Int16)"
  else
    IO.println "checkAll: FAIL"
    IO.Process.exit 1
