/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

START block lemma for the assembled `intfmt.dec` image: after the boot
`JMP`, four `ZERO` macros at pc 48 clear SIGN/LEN/PAD/NDIG and leave
the machine at pc 60. This is a block lemma, not end-to-end correctness.
-/

import IntFmt.Blocks

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- `imageCell` agrees with `intfmtImage[k]!` without reducing the
2323-cell literal: rewrite size, then `getElem!_pos`. -/
theorem imageCell_eq_bang {k : Nat} (hk : k < 2323) :
    imageCell k = intfmtImage[k]! := by
  have hsz : k < intfmtImage.size := by
    rw [intfmtImage_size]
    exact hk
  have hbang : intfmtImage[k]! = intfmtImage[k] :=
    getElem!_pos intfmtImage k hsz
  exact (imageCell_of_lt hsz).trans hbang.symm

/-- After the boot `JMP`, a non-poked cell still equals the assembled image. -/
theorem afterBoot_get (input mode cap : Word) (k : Nat)
    (hk : k < 2323) (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13) :
    (step (prepMachine input mode cap)).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
  have hmem := (boot_jmp input mode cap).2.2.1
  rw [hmem]
  exact (prep_get_cell input mode cap k hk hIn hMo hCa).trans (imageCell_eq_bang hk)

/-- `ZERO SIGN` at pc 48: one step to pc 51 with SIGN = 0, Z unchanged. -/
theorem start_zero_SIGN (input mode cap : Word) :
    let s0 := step (prepMachine input mode cap)
    let s1 := step s0
    s0.pc = 48 ∧
    s0.halted = false ∧
    s0.mem.get 0 = 0 ∧
    s1 = { s0 with mem := s0.mem.set 19 0, pc := 51 } ∧
    s1.pc = 51 ∧
    s1.halted = false ∧
    s1.mem.get 19 = 0 ∧
    s1.mem.get 0 = 0 := by
  intro s0 s1
  have boot := boot_jmp input mode cap
  have hs0pc : s0.pc = 48 := boot.1
  have hs0h : s0.halted = false := boot.2.1
  have hZ0 : s0.mem.get 0 = 0 := by
    rw [boot.2.2.1]
    exact (prep_ready input mode cap).2.2.2
  have h48 : s0.mem.get 48 = 19 := by
    have h := afterBoot_get input mode cap 48 (by decide) (by decide) (by decide) (by decide)
    have hk : (48 : Word) = UInt16.ofNat 48 := rfl
    rw [hk]
    exact h.trans image_start_ZERO_SIGN.1
  have h49 : s0.mem.get 49 = 19 := by
    have h := afterBoot_get input mode cap 49 (by decide) (by decide) (by decide) (by decide)
    have hk : (49 : Word) = UInt16.ofNat 49 := rfl
    rw [hk]
    exact h.trans image_start_ZERO_SIGN.2.1
  have h50 : s0.mem.get 50 = 51 := by
    have h := afterBoot_get input mode cap 50 (by decide) (by decide) (by decide) (by decide)
    have hk : (50 : Word) = UInt16.ofNat 50 := rfl
    rw [hk]
    exact h.trans image_start_ZERO_SIGN.2.2
  have hpc : s0.pc.toNat < 32768 := by
    simp [hs0pc]
  have ha : s0.mem.get s0.pc = 19 := by
    simpa [hs0pc] using h48
  have hb : s0.mem.get (s0.pc + 1) = 19 := by
    have : s0.pc + 1 = (49 : Word) := by simp [hs0pc]
    simpa [this] using h49
  have hc : s0.mem.get (s0.pc + 2) = s0.pc + 3 := by
    have hpc2 : s0.pc + 2 = (50 : Word) := by simp [hs0pc]
    have hdst : s0.pc + 3 = (51 : Word) := by simp [hs0pc]
    rw [hpc2, hdst]
    exact h50
  have hstep := step_ZERO (s := s0) (x := 19) hs0h hpc ha hb hc (by decide)
  have hs1 : s1 = { s0 with mem := s0.mem.set 19 0, pc := 51 } := by
    have : s0.pc + 3 = (51 : Word) := by simp [hs0pc]
    simpa [this] using hstep
  refine ⟨hs0pc, hs0h, hZ0, hs1, ?pc, ?hh, ?sign, ?Z⟩
  · simpa [hs1]
  · simpa [hs1] using hs0h
  · simpa [hs1] using Mem.get_set_eq s0.mem 19 0
  · have : s1.mem.get 0 = s0.mem.get 0 := by
      simpa [hs1] using Mem.get_set_ne s0.mem 19 0 0 (by decide)
    exact this.trans hZ0

/-- After four `ZERO`s at START, SIGN/LEN/PAD/NDIG are 0 and pc = 60. -/
theorem start_zero_regs (input mode cap : Word) :
    let s0 := step (prepMachine input mode cap)
    let s4 := runN s0 4
    s0.pc = 48 ∧
    s4.pc = 60 ∧
    s4.halted = false ∧
    s4.mem.get 19 = 0 ∧
    s4.mem.get 16 = 0 ∧
    s4.mem.get 27 = 0 ∧
    s4.mem.get 25 = 0 ∧
    s4.mem.get 0 = 0 := by
  intro s0 s4
  have step1 := start_zero_SIGN input mode cap
  have hs0pc : s0.pc = 48 := step1.1
  have hs0h : s0.halted = false := step1.2.1
  have hZ0 : s0.mem.get 0 = 0 := step1.2.2.1
  -- s1
  let s1 : Machine := step s0
  have hs1def : s1 = step s0 := rfl
  have hs1eq : s1 = { s0 with mem := s0.mem.set 19 0, pc := 51 } := by
    -- start_zero_SIGN is about the same s0
    simpa [hs1def] using step1.2.2.2.1
  have hs1pc : s1.pc = 51 := by simpa [hs1eq]
  have hs1h : s1.halted = false := by simpa [hs1eq] using hs0h
  have getk := afterBoot_get input mode cap
  -- instruction cells after ZERO SIGN (dst 19 is not in 51..59)
  have instr (k : Nat) (hk : k < 2323) (hne : UInt16.ofNat k ≠ 19)
      (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13) :
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    have h0 : s0.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
      getk k hk hIn hMo hCa
    have : s1.mem.get (UInt16.ofNat k) = s0.mem.get (UInt16.ofNat k) := by
      simpa [hs1eq] using Mem.get_set_ne s0.mem 19 (UInt16.ofNat k) 0 hne
    exact this.trans h0
  -- ZERO LEN at pc 51
  have h51 : s1.mem.get 51 = 16 := by
    have hk : (51 : Word) = UInt16.ofNat 51 := rfl
    rw [hk]
    exact (instr 51 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      image_start_ZERO_LEN.1
  have h52' : s1.mem.get 52 = 16 := by
    have hk : (52 : Word) = UInt16.ofNat 52 := rfl
    rw [hk]
    exact (instr 52 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      image_start_ZERO_LEN.2.1
  have h53 : s1.mem.get 53 = 54 := by
    have hk : (53 : Word) = UInt16.ofNat 53 := rfl
    rw [hk]
    exact (instr 53 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      image_start_ZERO_LEN.2.2
  have hpc1 : s1.pc.toNat < 32768 := by simp [hs1pc]
  have ha1 : s1.mem.get s1.pc = 16 := by simpa [hs1pc] using h51
  have hb1 : s1.mem.get (s1.pc + 1) = 16 := by
    have : s1.pc + 1 = (52 : Word) := by simp [hs1pc]
    simpa [this] using h52'
  have hc1 : s1.mem.get (s1.pc + 2) = s1.pc + 3 := by
    have hpc2 : s1.pc + 2 = (53 : Word) := by simp [hs1pc]
    have hdst : s1.pc + 3 = (54 : Word) := by simp [hs1pc]
    rw [hpc2, hdst]
    exact h53
  have hstep2 := step_ZERO (s := s1) (x := 16) hs1h hpc1 ha1 hb1 hc1 (by decide)
  let s2 : Machine := step s1
  have hs2def : s2 = step s1 := rfl
  have hs2eq : s2 = { s1 with mem := s1.mem.set 16 0, pc := 54 } := by
    have : s1.pc + 3 = (54 : Word) := by simp [hs1pc]
    simpa [hs2def, this] using hstep2
  have hs2pc : s2.pc = 54 := by simpa [hs2eq]
  have hs2h : s2.halted = false := by simpa [hs2eq] using hs1h
  have instr2 (k : Nat) (hk : k < 2323)
      (hne19 : UInt16.ofNat k ≠ 19) (hne16 : UInt16.ofNat k ≠ 16)
      (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13) :
      s2.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    have h1 : s1.mem.get (UInt16.ofNat k) = intfmtImage[k]! := instr k hk hne19 hIn hMo hCa
    have : s2.mem.get (UInt16.ofNat k) = s1.mem.get (UInt16.ofNat k) := by
      simpa [hs2eq] using Mem.get_set_ne s1.mem 16 (UInt16.ofNat k) 0 hne16
    exact this.trans h1
  -- ZERO PAD at pc 54
  have h54 : s2.mem.get 54 = 27 := by
    have hk : (54 : Word) = UInt16.ofNat 54 := rfl
    rw [hk]
    exact (instr2 54 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      image_start_ZERO_PAD.1
  have h55 : s2.mem.get 55 = 27 := by
    have hk : (55 : Word) = UInt16.ofNat 55 := rfl
    rw [hk]
    exact (instr2 55 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      image_start_ZERO_PAD.2.1
  have h56 : s2.mem.get 56 = 57 := by
    have hk : (56 : Word) = UInt16.ofNat 56 := rfl
    rw [hk]
    exact (instr2 56 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      image_start_ZERO_PAD.2.2
  have hpc2n : s2.pc.toNat < 32768 := by simp [hs2pc]
  have ha2 : s2.mem.get s2.pc = 27 := by simpa [hs2pc] using h54
  have hb2 : s2.mem.get (s2.pc + 1) = 27 := by
    have : s2.pc + 1 = (55 : Word) := by simp [hs2pc]
    simpa [this] using h55
  have hc2 : s2.mem.get (s2.pc + 2) = s2.pc + 3 := by
    have hp2 : s2.pc + 2 = (56 : Word) := by simp [hs2pc]
    have hd : s2.pc + 3 = (57 : Word) := by simp [hs2pc]
    rw [hp2, hd]
    exact h56
  have hstep3 := step_ZERO (s := s2) (x := 27) hs2h hpc2n ha2 hb2 hc2 (by decide)
  let s3 : Machine := step s2
  have hs3def : s3 = step s2 := rfl
  have hs3eq : s3 = { s2 with mem := s2.mem.set 27 0, pc := 57 } := by
    have : s2.pc + 3 = (57 : Word) := by simp [hs2pc]
    simpa [hs3def, this] using hstep3
  have hs3pc : s3.pc = 57 := by simpa [hs3eq]
  have hs3h : s3.halted = false := by simpa [hs3eq] using hs2h
  have instr3 (k : Nat) (hk : k < 2323)
      (hne19 : UInt16.ofNat k ≠ 19) (hne16 : UInt16.ofNat k ≠ 16) (hne27 : UInt16.ofNat k ≠ 27)
      (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13) :
      s3.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    have h2 : s2.mem.get (UInt16.ofNat k) = intfmtImage[k]! := instr2 k hk hne19 hne16 hIn hMo hCa
    have : s3.mem.get (UInt16.ofNat k) = s2.mem.get (UInt16.ofNat k) := by
      simpa [hs3eq] using Mem.get_set_ne s2.mem 27 (UInt16.ofNat k) 0 hne27
    exact this.trans h2
  -- ZERO NDIG at pc 57
  have h57 : s3.mem.get 57 = 25 := by
    have hk : (57 : Word) = UInt16.ofNat 57 := rfl
    rw [hk]
    exact (instr3 57 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans
      image_start_ZERO_NDIG.1
  have h58 : s3.mem.get 58 = 25 := by
    have hk : (58 : Word) = UInt16.ofNat 58 := rfl
    rw [hk]
    exact (instr3 58 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans
      image_start_ZERO_NDIG.2.1
  have h59 : s3.mem.get 59 = 60 := by
    have hk : (59 : Word) = UInt16.ofNat 59 := rfl
    rw [hk]
    exact (instr3 59 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans
      image_start_ZERO_NDIG.2.2
  have hpc3n : s3.pc.toNat < 32768 := by simp [hs3pc]
  have ha3 : s3.mem.get s3.pc = 25 := by simpa [hs3pc] using h57
  have hb3 : s3.mem.get (s3.pc + 1) = 25 := by
    have : s3.pc + 1 = (58 : Word) := by simp [hs3pc]
    simpa [this] using h58
  have hc3 : s3.mem.get (s3.pc + 2) = s3.pc + 3 := by
    have hp2 : s3.pc + 2 = (59 : Word) := by simp [hs3pc]
    have hd : s3.pc + 3 = (60 : Word) := by simp [hs3pc]
    rw [hp2, hd]
    exact h59
  have hstep4 := step_ZERO (s := s3) (x := 25) hs3h hpc3n ha3 hb3 hc3 (by decide)
  let s4' : Machine := step s3
  have hs4def : s4' = step s3 := rfl
  have hs4eq : s4' = { s3 with mem := s3.mem.set 25 0, pc := 60 } := by
    have : s3.pc + 3 = (60 : Word) := by simp [hs3pc]
    simpa [hs4def, this] using hstep4
  -- runN s0 4 = s4'
  have hr0 : runN s0 4 = runN (step s0) 3 :=
    runN_succ_go s0 3 hs0h (by simp [hs0pc])
  have hr1 : runN s1 3 = runN (step s1) 2 :=
    runN_succ_go s1 2 hs1h (by simp [hs1pc])
  have hr2 : runN s2 2 = runN (step s2) 1 :=
    runN_succ_go s2 1 hs2h (by simp [hs2pc])
  have hr3 : runN s3 1 = runN (step s3) 0 :=
    runN_succ_go s3 0 hs3h (by simp [hs3pc])
  have hrun : s4 = s4' := by
    calc
      s4 = runN s0 4 := rfl
      _  = runN (step s0) 3 := hr0
      _  = runN s1 3 := by rw [hs1def]
      _  = runN (step s1) 2 := hr1
      _  = runN s2 2 := by rw [hs2def]
      _  = runN (step s2) 1 := hr2
      _  = runN s3 1 := by rw [hs3def]
      _  = runN (step s3) 0 := hr3
      _  = step s3 := runN_zero _
      _  = s4' := hs4def.symm
  have hs4pc : s4.pc = 60 := by simpa [hrun, hs4eq]
  have hs4h : s4.halted = false := by
    have : s4'.halted = false := by simpa [hs4eq] using hs3h
    simpa [hrun] using this
  have h19 : s4.mem.get 19 = 0 := by
    -- 19 survived later ZEROs of 16, 27, 25
    have a : s1.mem.get 19 = 0 := by
      simpa [hs1eq] using Mem.get_set_eq s0.mem 19 0
    have b : s2.mem.get 19 = s1.mem.get 19 := by
      simpa [hs2eq] using Mem.get_set_ne s1.mem 16 19 0 (by decide)
    have c : s3.mem.get 19 = s2.mem.get 19 := by
      simpa [hs3eq] using Mem.get_set_ne s2.mem 27 19 0 (by decide)
    have d : s4'.mem.get 19 = s3.mem.get 19 := by
      simpa [hs4eq] using Mem.get_set_ne s3.mem 25 19 0 (by decide)
    calc
      s4.mem.get 19 = s4'.mem.get 19 := by simpa [hrun]
      _ = s3.mem.get 19 := d
      _ = s2.mem.get 19 := c
      _ = s1.mem.get 19 := b
      _ = 0 := a
  have h16 : s4.mem.get 16 = 0 := by
    have a : s2.mem.get 16 = 0 := by
      simpa [hs2eq] using Mem.get_set_eq s1.mem 16 0
    have b : s3.mem.get 16 = s2.mem.get 16 := by
      simpa [hs3eq] using Mem.get_set_ne s2.mem 27 16 0 (by decide)
    have c : s4'.mem.get 16 = s3.mem.get 16 := by
      simpa [hs4eq] using Mem.get_set_ne s3.mem 25 16 0 (by decide)
    calc
      s4.mem.get 16 = s4'.mem.get 16 := by simpa [hrun]
      _ = s3.mem.get 16 := c
      _ = s2.mem.get 16 := b
      _ = 0 := a
  have h27 : s4.mem.get 27 = 0 := by
    have a : s3.mem.get 27 = 0 := by
      simpa [hs3eq] using Mem.get_set_eq s2.mem 27 0
    have b : s4'.mem.get 27 = s3.mem.get 27 := by
      simpa [hs4eq] using Mem.get_set_ne s3.mem 25 27 0 (by decide)
    calc
      s4.mem.get 27 = s4'.mem.get 27 := by simpa [hrun]
      _ = s3.mem.get 27 := b
      _ = 0 := a
  have h25 : s4.mem.get 25 = 0 := by
    have a : s4'.mem.get 25 = 0 := by
      simpa [hs4eq] using Mem.get_set_eq s3.mem 25 0
    simpa [hrun] using a
  have hZ : s4.mem.get 0 = 0 := by
    have a : s1.mem.get 0 = 0 := step1.2.2.2.2.2.2.2
    have b : s2.mem.get 0 = s1.mem.get 0 := by
      simpa [hs2eq] using Mem.get_set_ne s1.mem 16 0 0 (by decide)
    have c : s3.mem.get 0 = s2.mem.get 0 := by
      simpa [hs3eq] using Mem.get_set_ne s2.mem 27 0 0 (by decide)
    have d : s4'.mem.get 0 = s3.mem.get 0 := by
      simpa [hs4eq] using Mem.get_set_ne s3.mem 25 0 0 (by decide)
    calc
      s4.mem.get 0 = s4'.mem.get 0 := by simpa [hrun]
      _ = s3.mem.get 0 := d
      _ = s2.mem.get 0 := c
      _ = s1.mem.get 0 := b
      _ = 0 := a
  exact ⟨hs0pc, hs4pc, hs4h, h19, h16, h27, h25, hZ⟩

end IntFmt
