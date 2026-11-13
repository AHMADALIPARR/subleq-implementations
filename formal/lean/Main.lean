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
#print axioms snprintf_nul
#print axioms subleqI16toa_refines_spec
#print axioms putAll_i16toa
#print axioms run_fuel0_halted
#print axioms check_min
#print axioms Subleq.sub_defined
#print axioms intfmtFuel_gt_maxMeasured
#print axioms image_sub_defined
#print axioms runImage_terminates
#print axioms image_mem_in_range


#print axioms intfmtImage_size
#print axioms intfmtImage_prefix16_eq_parse
#print axioms parseDec_line0
#print axioms parse_min_cell
#print axioms image_cell_startTarget
#print axioms image_cell_K45
#print axioms image_cell_haltTarget
#print axioms loadImage_eq_aux
#print axioms boot_jmp
#print axioms program_identity
#print axioms safety_applies
#print axioms run_intfmtFuel_of_done
#print axioms Subleq.step_JMP
#print axioms Subleq.step_ZERO
#print axioms Subleq.step_JLEZ
#print axioms Subleq.step_SUB
#print axioms Subleq.step_HALT
#print axioms Subleq.runN_MOV
#print axioms Subleq.runN_ADD
#print axioms Subleq.runN_INC
#print axioms Subleq.sub_sub_zero
#print axioms Subleq.add_sub_neg

#print axioms extract_split
#print axioms parseDecText_append
#print axioms parse_atA
#print axioms image_atA
#print axioms parse_line000
#print axioms image_chunk000
#print axioms k48_is_ascii_zero
#print axioms k45_is_ascii_minus
#print axioms formatSpec_neg_uses_minus
#print axioms image_start_ZERO_SIGN
#print axioms imageCell_eq_bang
#print axioms afterBoot_get
#print axioms start_zero_SIGN
#print axioms start_zero_regs
#print axioms prepMachine_get_input
#print axioms start_zero_regs_get
#print axioms start_zero_regs_get_INPUT
#print axioms start_mov_INPUT_N
#print axioms parseDecText_intfmtDecText
#print axioms program_identity_parsed
#print axioms Subleq.runN_add
#print axioms Subleq.runCounted_programHalt_le
#print axioms Subleq.runCounted_zero_go

def main : IO Unit := do
  IO.println "IntFmt formal driver"
  IO.println "Authoritative theorems live in IntFmt.Decimal, Buffer, Refinement."
  IO.println "Running exhaustive executable check over 65536 Int16 values..."
  if checkAll then
    IO.println "checkAll: PASS (i16toa = intToDec on every Int16)"
  else
    IO.println "checkAll: FAIL"
    IO.Process.exit 1
