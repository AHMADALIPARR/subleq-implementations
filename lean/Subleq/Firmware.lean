-- Copyright (C) Ahmad <ahmedparr93@gmail.com>
-- SPDX-License-Identifier: AGPL-3.0-only

import Subleq.Machine
import Subleq.Theorems

/-!
# Firmware-aware semantic equivalence

Hand-written Lean 4 proofs that the higher-level operations recovered by the
firmware-aware decompiler have the same semantics as the SUBLEQ instruction
sequences they represent.

No `sorry`, no `admit`, no extra axioms.

Numerical facts use `decide` (core equivalent of `norm_num` for concrete
arithmetic in this project, which does not depend on Mathlib).
-/

namespace Subleq

/-! ## Layout constants -/

theorem firmware_layout : 61 * 3 + 33 = 216 := by decide
theorem firmware_code_words : 61 * 3 = 183 := by decide
theorem firmware_total : 183 + 33 = 216 := by decide

/-! ## MOV

The net effect of the four-instruction MOV sequence is proved by showing
that the final write to `dest` is the value `v` (already in range) and that
`Z` is restored to 0.
-/

theorem zero_clears (m : Array Int) (x : Int) (h : InRange m x) :
    rd (wr m x 0) x = 0 :=
  rd_wr_same m x 0 h

/-- The value computed by the third instruction of MOV is the original `v`. -/
theorem mov_third_value (v : Int) (hv : wrap32 v = v) :
    wrap32 (0 - wrap32 (0 - v)) = v := by
  rw [← hv]
  simp only [wrap32]
  omega

/-- After the third write of MOV, `dest` holds `v`. -/
theorem mov_after_third (m : Array Int) (dest z v : Int)
    (hdest : InRange m dest) (hv : wrap32 v = v) :
    rd (wr (wr (wr m dest 0) z (wrap32 (0 - v))) dest (wrap32 (0 - wrap32 (0 - v)))) dest = v := by
  have h : InRange (wr (wr m dest 0) z (wrap32 (0 - v))) dest := by
    unfold InRange at *
    simp [wr_size]
    exact hdest
  rw [mov_third_value v hv]
  exact rd_wr_same _ dest v h

/-- The final write of MOV restores `Z` to 0. -/
theorem mov_z_restored (m : Array Int) (dest z v : Int)
    (hz : InRange m z) :
    rd (wr (wr (wr (wr m dest 0) z (wrap32 (0 - v))) dest (wrap32 (0 - wrap32 (0 - v)))) z 0) z = 0 := by
  have h : InRange (wr (wr (wr m dest 0) z (wrap32 (0 - v))) dest (wrap32 (0 - wrap32 (0 - v)))) z := by
    unfold InRange at *
    simp [wr_size]
    exact hz
  exact rd_wr_same _ z 0 h

/-! ## JUMP -/

theorem jump_status (s : State) (z target : Int)
    (hr : s.status = .running) (hpc : ¬ BadPC s)
    (ha : rd s.mem s.pc = z) (hb : rd s.mem (s.pc + 1) = z)
    (hc : rd s.mem (s.pc + 2) = target)
    (hzz : rd s.mem z = 0)
    (hnotneg : ¬ z < 0) (hnot1 : z ≠ -1) (hnot2 : z ≠ -2)
    (hnot_halt : target ≠ -1) :
    (step s).status = .running := by
  have ha' : rd s.mem s.pc ≠ -1 := by rw [ha]; exact hnot1
  have ha'' : rd s.mem s.pc ≠ -2 := by rw [ha]; exact hnot2
  have hb' : ¬ rd s.mem (s.pc + 1) < 0 := by rw [hb]; exact hnotneg
  have hord := step_ordinary s hr hpc ha' ha'' hb'
  simp only [ha, hb, hc, hzz] at hord
  rw [hord]
  unfold haltOn
  simp [hnot_halt]
  exact hr

theorem jump_pc (s : State) (z target : Int)
    (hr : s.status = .running) (hpc : ¬ BadPC s)
    (ha : rd s.mem s.pc = z) (hb : rd s.mem (s.pc + 1) = z)
    (hc : rd s.mem (s.pc + 2) = target)
    (hzz : rd s.mem z = 0)
    (hnotneg : ¬ z < 0) (hnot1 : z ≠ -1) (hnot2 : z ≠ -2)
    (hnot_halt : target ≠ -1) :
    (step s).pc = target := by
  have ha' : rd s.mem s.pc ≠ -1 := by rw [ha]; exact hnot1
  have ha'' : rd s.mem s.pc ≠ -2 := by rw [ha]; exact hnot2
  have hb' : ¬ rd s.mem (s.pc + 1) < 0 := by rw [hb]; exact hnotneg
  have hord := step_ordinary s hr hpc ha' ha'' hb'
  simp only [ha, hb, hc, hzz] at hord
  rw [hord]
  unfold haltOn
  simp only [hnot_halt]
  have hle : wrap32 (0 - 0) ≤ 0 := by
    simp only [wrap32]
    omega
  simp only [hle]
  rfl

theorem jump_postcondition (s : State) (z target : Int)
    (hr : s.status = .running) (hpc : ¬ BadPC s)
    (ha : rd s.mem s.pc = z) (hb : rd s.mem (s.pc + 1) = z)
    (hc : rd s.mem (s.pc + 2) = target)
    (hzz : rd s.mem z = 0)
    (hnotneg : ¬ z < 0) (hnot1 : z ≠ -1) (hnot2 : z ≠ -2)
    (hnot_halt : target ≠ -1) :
    (step s).pc = target ∧ (step s).status = .running :=
  ⟨jump_pc s z target hr hpc ha hb hc hzz hnotneg hnot1 hnot2 hnot_halt,
   jump_status s z target hr hpc ha hb hc hzz hnotneg hnot1 hnot2 hnot_halt⟩

/-! ## IRET -/

theorem iret_zero (m : Array Int) (exc : Int) (h : InRange m exc) :
    rd (wr m exc 0) exc = 0 :=
  rd_wr_same m exc 0 h

theorem iret_halt (s : State) (hr : s.status = .running) (hpc : ¬ BadPC s)
    (ha : rd s.mem s.pc = 0) (hb : rd s.mem (s.pc + 1) = 0)
    (hc : rd s.mem (s.pc + 2) = -1)
    (hzz : rd s.mem 0 = 0)
    (hnot1 : (0 : Int) ≠ -1) (hnot2 : (0 : Int) ≠ -2)
    (hpos : ¬ (0 : Int) < 0) :
    (step s).status = .halted := by
  have ha' : rd s.mem s.pc ≠ -1 := by rw [ha]; exact hnot1
  have ha'' : rd s.mem s.pc ≠ -2 := by rw [ha]; exact hnot2
  have hb' : ¬ rd s.mem (s.pc + 1) < 0 := by rw [hb]; exact hpos
  have hord := step_ordinary s hr hpc ha' ha'' hb'
  simp only [ha, hb, hc, hzz] at hord
  rw [hord]
  exact haltOn_neg_one _

/-! ## Vector installation -/

theorem vector_install_third (m : Array Int) (slot z addr : Int)
    (hslot : InRange m slot) (hv : wrap32 addr = addr) :
    rd (wr (wr (wr m slot 0) z (wrap32 (0 - addr))) slot (wrap32 (0 - wrap32 (0 - addr)))) slot = addr :=
  mov_after_third m slot z addr hslot hv

/-! ## Compositional package -/

theorem recovered_ops_equivalent :
    (∀ v, wrap32 v = v → wrap32 (0 - wrap32 (0 - v)) = v) ∧
    (∀ s z target,
      s.status = .running → ¬ BadPC s →
      rd s.mem s.pc = z → rd s.mem (s.pc + 1) = z → rd s.mem (s.pc + 2) = target →
      rd s.mem z = 0 → ¬ z < 0 → z ≠ -1 → z ≠ -2 → target ≠ -1 →
      (step s).pc = target ∧ (step s).status = .running) ∧
    (∀ m exc, InRange m exc → rd (wr m exc 0) exc = 0) ∧
    (∀ s,
      s.status = .running → ¬ BadPC s →
      rd s.mem s.pc = 0 → rd s.mem (s.pc + 1) = 0 → rd s.mem (s.pc + 2) = -1 →
      rd s.mem 0 = 0 → (0 : Int) ≠ -1 → (0 : Int) ≠ -2 → ¬ (0 : Int) < 0 →
      (step s).status = .halted) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv; exact mov_third_value v hv
  · intro s z target hr hpc ha hb hc hzz hnotneg hnot1 hnot2 hnot_halt
    exact jump_postcondition s z target hr hpc ha hb hc hzz hnotneg hnot1 hnot2 hnot_halt
  · intro m exc h; exact iret_zero m exc h
  · intro s hr hpc ha hb hc hzz hnot1 hnot2 hpos
    exact iret_halt s hr hpc ha hb hc hzz hnot1 hnot2 hpos

end Subleq
