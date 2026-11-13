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
#print axioms start_mov_get
#print axioms start_mov_get_MODE
#print axioms start_mov_get_ONE
#print axioms mode_mov_MODE_T
#print axioms mode_dispatch_signed
#print axioms mode_dispatch_unsigned
#print axioms afterSignedDispatch_entry
#print axioms i_path_prelude
#print axioms i_path_pos
#print axioms i_path_zero
#print axioms i_path_neg_to_doneg
#print axioms i_path_neg
#print axioms word_sub_ge
#print axioms p0PlaceSteps_le
#print axioms digits_zero_Qs
#print axioms p0_ge_body
#print axioms p0_exit_zero
#print axioms p0_exit_small
#print axioms p0_to_ge_hi
#print axioms p0_to_ge_mid
#print axioms p0_to_ge_eq
#print axioms p0PlaceSteps_ge
#print axioms p0_to_ge
#print axioms p0_one_iter
#print axioms p0_loop
#print axioms placeSteps_ge
#print axioms placeSteps_le
#print axioms p1_image
#print axioms p2_image
#print axioms p3_image
#print axioms place_loop_mov_N_T
#print axioms place_pos_mov_N_T
#print axioms place_loop
#print axioms p1_loop
#print axioms p2_loop
#print axioms p3_loop
#print axioms ascii_convert
#print axioms ascii_mov_N_Q4
#print axioms ndig_five
#print axioms ndig_four
#print axioms ndig_three
#print axioms ndig_two
#print axioms ndig_one
#print axioms have_dig_sign0
#print axioms have_dig_sign_nz
#print axioms pad_len_width0
#print axioms pad_len_le_raw
#print axioms pad_len_gt_raw
#print axioms cap0_halt
#print axioms cap_nz_to_sploop
#print axioms sp_loop_pad0
#print axioms have_dig_to_after_pad_unsigned
#print axioms after_pad_sign0
#print axioms st0_store
#print axioms store_ch_idx0
#print axioms store_ch_idx1
#print axioms store_ch_idx15
#print axioms stored_ret_pad
#print axioms stored_ret_sign
#print axioms stored_ret_dig
#print axioms write_space
#print axioms write_minus
#print axioms write_space_pad_idx0
#print axioms write_minus_sign_idx0
#print axioms sp_loop_to_write_space
#print axioms after_pad_to_write_minus
#print axioms after_sign_to_emit
#print axioms pad_one_iter_idx0
#print axioms after_pad_minus_to_emit_idx0
#print axioms emit_prelude
#print axioms dig_next
#print axioms dig_loop_exit
#print axioms dig_loop_to_body
#print axioms dig_body_skip
#print axioms dig_body_take_eq
#print axioms dig_body_take_gt
#print axioms take_dig_di0
#print axioms take_dig_di4
#print axioms have_ch_to_store
#print axioms take_store_next_di0_idx0
#print axioms skip_next
#print axioms loop_take_eq_di4_idx0
#print axioms emit_ndig1_idx0
#print axioms emit_ndig1_idx1
#print axioms emit_ndig5_idx0
#print axioms emit_ndig5_idx1
#print axioms after_digs_nul_at_len
#print axioms write_nul_idx0
#print axioms write_nul_idx6
#print axioms write_nul_done_idx1
#print axioms after_digs_write_nul_done_len1
#print axioms emit_ndig1_idx0_write_nul_done
#print axioms emit_ndig5_idx0_write_nul_done
#print axioms emit_ndig1_idx1_write_nul_done
#print axioms emit_ndig5_idx1_write_nul_done
#print axioms after_pad_sign0_ndig1_done
#print axioms after_pad_sign0_ndig4_done
#print axioms have_dig_unsigned_ndig1_done
#print axioms have_dig_unsigned_ndig4_done
#print axioms after_pad_minus_ndig1_done
#print axioms after_pad_minus_ndig4_done
#print axioms write_space_pad_idx1
#print axioms pad_one_iter_idx1
#print axioms pad_1_spaces_idx0
#print axioms pad_7_spaces_idx0
#print axioms pad_1_to_after_pad
#print axioms pad_7_to_after_pad
#print axioms p3_done_unsigned_ndig1_done
#print axioms p3_done_unsigned_ndig4_done
#print axioms have_dig_to_after_pad_signed
#print axioms have_dig_signed_ndig1_done
#print axioms have_dig_signed_ndig4_done
#print axioms p3_done_signed_ndig1_done
#print axioms p3_done_signed_ndig4_done
#print axioms after_pad_sign0_ndig5_done
#print axioms after_pad_minus_ndig5_done
#print axioms have_dig_unsigned_ndig5_done
#print axioms have_dig_signed_ndig5_done
#print axioms p3_done_unsigned_ndig5_done
#print axioms p3_done_signed_ndig5_done
#print axioms unsigned_at_digits
#print axioms signed_pos_at_digits
#print axioms signed_zero_at_digits
#print axioms signed_neg_at_digits
#print axioms digits_to_p3_done
#print axioms placeAllSteps_le_of_word
#print axioms p0_goto_pos
#print axioms word_sub_lt
#print axioms parseDecText_intfmtDecText
#print axioms program_identity_parsed
#print axioms Subleq.runN_add
#print axioms Subleq.runCounted_programHalt_le
#print axioms Subleq.runCounted_zero_go

#print axioms intfmt_unsigned_e2e
#print axioms intfmt_signed_e2e
#print axioms intfmt_signed_e2e_load

def main : IO Unit := do
  IO.println "IntFmt formal driver"
  IO.println "Authoritative theorems live in IntFmt.Decimal, Buffer, Refinement."
  IO.println "Running exhaustive executable check over 65536 Int16 values..."
  if checkAll then
    IO.println "checkAll: PASS (i16toa = intToDec on every Int16)"
  else
    IO.println "checkAll: FAIL"
    IO.Process.exit 1
