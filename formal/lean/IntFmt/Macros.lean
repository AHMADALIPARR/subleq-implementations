/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Hoare-style lemmas for the assembler macros, in terms of `Subleq.step`.
Each lemma assumes the instruction cells at `s.pc` match the encoding
produced by `asm16`, and that cell 0 (`Z`) is 0 at the start of MOV/ADD
(the assembler re-zeroes Z at the end of those macros).
-/

import IntFmt.Exec

namespace IntFmt.Subleq

/-- `JMP dest` is encoded as `subleq Z, Z, dest` (three cells). -/
theorem step_JMP {s : Machine} {dest : Word}
    (hh : s.halted = false)
    (hpc : s.pc.toNat < 32768)
    (hZ : s.mem.get 0 = 0)
    (ha : s.mem.get s.pc = 0)
    (hb : s.mem.get (s.pc + 1) = 0)
    (hc : s.mem.get (s.pc + 2) = dest) :
    step s = { s with pc := dest } := by
  have hs := step_sub (s := s) (a := 0) (b := 0) (c := dest) hh hpc ha hb hc
    (by decide) (by decide)
  -- r = 0 - 0 = 0, so the branch is taken and Z is unchanged
  have hr : s.mem.get 0 - s.mem.get 0 = 0 := by simp [hZ]
  have hset : s.mem.set 0 0 = s.mem := by
    funext y
    simp [Mem.set]
    intro hy
    subst hy
    simpa [Mem.get] using hZ.symm
  simp [hs, hr, hset]

/-- `ZERO x` is `subleq x, x, pc+3`. -/
theorem step_ZERO {s : Machine} {x : Word}
    (hh : s.halted = false)
    (hpc : s.pc.toNat < 32768)
    (ha : s.mem.get s.pc = x)
    (hb : s.mem.get (s.pc + 1) = x)
    (hc : s.mem.get (s.pc + 2) = s.pc + 3)
    (hnio : x ≠ 0xFFFF) :
    step s = { s with mem := s.mem.set x 0, pc := s.pc + 3 } := by
  have hs := step_sub (s := s) (a := x) (b := x) (c := s.pc + 3)
    hh hpc ha hb hc hnio hnio
  have hr : s.mem.get x - s.mem.get x = 0 := by simp
  simp [hs, hr]

/-- `JLEZ x dest` is `subleq Z, x, dest`. Requires `Z = 0`, so `x` is
unchanged and the branch is taken iff `x` is `0` or has the sign bit. -/
theorem step_JLEZ {s : Machine} {x dest : Word}
    (hh : s.halted = false)
    (hpc : s.pc.toNat < 32768)
    (hZ : s.mem.get 0 = 0)
    (ha : s.mem.get s.pc = 0)
    (hb : s.mem.get (s.pc + 1) = x)
    (hc : s.mem.get (s.pc + 2) = dest)
    (hnio : x ≠ 0xFFFF) :
    step s =
      { s with
        pc := if s.mem.get x = 0 || 0x8000 ≤ s.mem.get x then dest else s.pc + 3 } := by
  have hs := step_sub (s := s) (a := 0) (b := x) (c := dest)
    hh hpc ha hb hc (by decide) hnio
  have hr : s.mem.get x - s.mem.get 0 = s.mem.get x := by simp [hZ]
  have hset : s.mem.set x (s.mem.get x) = s.mem := by
    funext y
    simp [Mem.set]
    intro hy
    subst hy
    rfl
  simp [hs, hr, hset]

/-- Two-argument `SUB a, b` (fall-through `c = pc+3`). -/
theorem step_SUB {s : Machine} {a b : Word}
    (hh : s.halted = false)
    (hpc : s.pc.toNat < 32768)
    (ha : s.mem.get s.pc = a)
    (hb : s.mem.get (s.pc + 1) = b)
    (hc : s.mem.get (s.pc + 2) = s.pc + 3)
    (hna : a ≠ 0xFFFF)
    (hnb : b ≠ 0xFFFF) :
    step s =
      { s with
        mem := s.mem.set b (s.mem.get b - s.mem.get a)
        pc := s.pc + 3 } := by
  have hs := step_sub (s := s) (a := a) (b := b) (c := s.pc + 3)
    hh hpc ha hb hc hna hnb
  -- whether or not the result is ≤ 0, the branch target is pc+3
  have : (if (s.mem.get b - s.mem.get a) = 0 || 0x8000 ≤ (s.mem.get b - s.mem.get a)
          then s.pc + 3 else s.pc + 3) = s.pc + 3 := by
    split <;> rfl
  simp [hs]

/-- `DEC x` is `subleq ONE, x, pc+3`. -/
theorem step_DEC {s : Machine} {x : Word}
    (hh : s.halted = false)
    (hpc : s.pc.toNat < 32768)
    (hONE : s.mem.get 3 = 1)
    (ha : s.mem.get s.pc = 3)
    (hb : s.mem.get (s.pc + 1) = x)
    (hc : s.mem.get (s.pc + 2) = s.pc + 3)
    (hnio : x ≠ 0xFFFF) :
    step s = { s with mem := s.mem.set x (s.mem.get x - 1), pc := s.pc + 3 } := by
  have hs := step_SUB (s := s) (a := 3) (b := x) hh hpc ha hb hc (by decide) hnio
  simp [hs, hONE]

/-- `HALT` is `subleq Z, Z, 32768`. -/
theorem step_HALT {s : Machine}
    (hh : s.halted = false)
    (hpc : s.pc.toNat < 32768)
    (hZ : s.mem.get 0 = 0)
    (ha : s.mem.get s.pc = 0)
    (hb : s.mem.get (s.pc + 1) = 0)
    (hc : s.mem.get (s.pc + 2) = 32768) :
    step s = { s with pc := 32768 } :=
  step_JMP (dest := 32768) hh hpc hZ ha hb hc

/-- Signed-nonpositive test used by JLEZ: `le0 w` iff `w = 0` or the
high bit is set (Howe / eForth convention). -/
def le0 (w : Word) : Bool := w = 0 || 0x8000 ≤ w

theorem le0_zero : le0 0 = true := rfl

theorem le0_pos {w : Word} (h : 0 < w.toNat) (h2 : w.toNat < 32768) :
    le0 w = false := by
  unfold le0
  have hz : w ≠ 0 := by
    intro hz
    have : w.toNat = 0 := by simp [hz]
    omega
  have hhi : ¬ 0x8000 ≤ w := by
    intro hp
    have : 32768 ≤ w.toNat := by
      simpa [UInt16.le_iff_toNat_le] using hp
    omega
  simp [hz, hhi]

/-- Wrap-add of a small `Nat` agrees with `Nat` addition. -/
theorem word_add_toNat (pc : Word) (n : Nat) (h : pc.toNat + n < 65536) :
    (pc + UInt16.ofNat n).toNat = pc.toNat + n := by
  have hn : n < 65536 := Nat.lt_of_le_of_lt (Nat.le_add_left n pc.toNat) h
  have hnt : (UInt16.ofNat n).toNat = n := UInt16.toNat_ofNat_of_lt hn
  have hadd : (pc + UInt16.ofNat n).toNat =
      (pc.toNat + (UInt16.ofNat n).toNat) % 65536 := UInt16.toNat_add pc (UInt16.ofNat n)
  rw [hadd, hnt, Nat.mod_eq_of_lt h]

theorem word_add_off (pc : Word) (a b : Nat)
    (ha : pc.toNat + a < 65536) (hab : pc.toNat + (a + b) < 65536)
    (hb : b < 65536) :
    (pc + UInt16.ofNat a) + UInt16.ofNat b = pc + UInt16.ofNat (a + b) := by
  apply UInt16.toNat.inj
  have ha' := word_add_toNat pc a ha
  have hab' := word_add_toNat pc (a + b) hab
  have hbt : (UInt16.ofNat b).toNat = b := UInt16.toNat_ofNat_of_lt hb
  rw [UInt16.toNat_add, ha', hbt, Nat.mod_eq_of_lt (by omega), hab']
  omega

theorem add_ofNat_0 (pc : Word) (h : pc.toNat + 0 < 65536) :
    pc + UInt16.ofNat 0 = pc + 0 := by
  apply UInt16.toNat.inj
  rw [word_add_toNat pc 0 h, UInt16.toNat_add]
  have : (0 : Word).toNat = 0 := rfl
  rw [this, Nat.mod_eq_of_lt h]

theorem add_ofNat_1 (pc : Word) (h : pc.toNat + 1 < 65536) :
    pc + UInt16.ofNat 1 = pc + 1 := by
  apply UInt16.toNat.inj
  rw [word_add_toNat pc 1 h, UInt16.toNat_add]
  have : (1 : Word).toNat = 1 := rfl
  rw [this, Nat.mod_eq_of_lt h]

theorem add_ofNat_2 (pc : Word) (h : pc.toNat + 2 < 65536) :
    pc + UInt16.ofNat 2 = pc + 2 := by
  apply UInt16.toNat.inj
  rw [word_add_toNat pc 2 h, UInt16.toNat_add]
  have : (2 : Word).toNat = 2 := rfl
  rw [this, Nat.mod_eq_of_lt h]

theorem add_ofNat_3 (pc : Word) (h : pc.toNat + 3 < 65536) :
    pc + UInt16.ofNat 3 = pc + 3 := by
  apply UInt16.toNat.inj
  rw [word_add_toNat pc 3 h, UInt16.toNat_add]
  have : (3 : Word).toNat = 3 := rfl
  rw [this, Nat.mod_eq_of_lt h]

theorem add_ofNat_4 (pc : Word) (h : pc.toNat + 4 < 65536) :
    pc + UInt16.ofNat 4 = pc + 4 := by
  apply UInt16.toNat.inj
  rw [word_add_toNat pc 4 h, UInt16.toNat_add]
  have : (4 : Word).toNat = 4 := rfl
  rw [this, Nat.mod_eq_of_lt h]

theorem add_ofNat_5 (pc : Word) (h : pc.toNat + 5 < 65536) :
    pc + UInt16.ofNat 5 = pc + 5 := by
  apply UInt16.toNat.inj
  rw [word_add_toNat pc 5 h, UInt16.toNat_add]
  have : (5 : Word).toNat = 5 := rfl
  rw [this, Nat.mod_eq_of_lt h]

theorem add_ofNat_6 (pc : Word) (h : pc.toNat + 6 < 65536) :
    pc + UInt16.ofNat 6 = pc + 6 := by
  apply UInt16.toNat.inj
  rw [word_add_toNat pc 6 h, UInt16.toNat_add]
  have : (6 : Word).toNat = 6 := rfl
  rw [this, Nat.mod_eq_of_lt h]

theorem add_ofNat_7 (pc : Word) (h : pc.toNat + 7 < 65536) :
    pc + UInt16.ofNat 7 = pc + 7 := by
  apply UInt16.toNat.inj
  rw [word_add_toNat pc 7 h, UInt16.toNat_add]
  have : (7 : Word).toNat = 7 := rfl
  rw [this, Nat.mod_eq_of_lt h]

theorem add_ofNat_8 (pc : Word) (h : pc.toNat + 8 < 65536) :
    pc + UInt16.ofNat 8 = pc + 8 := by
  apply UInt16.toNat.inj
  rw [word_add_toNat pc 8 h, UInt16.toNat_add]
  have : (8 : Word).toNat = 8 := rfl
  rw [this, Nat.mod_eq_of_lt h]

theorem add_ofNat_9 (pc : Word) (h : pc.toNat + 9 < 65536) :
    pc + UInt16.ofNat 9 = pc + 9 := by
  apply UInt16.toNat.inj
  rw [word_add_toNat pc 9 h, UInt16.toNat_add]
  have : (9 : Word).toNat = 9 := rfl
  rw [this, Nat.mod_eq_of_lt h]

theorem add_ofNat_10 (pc : Word) (h : pc.toNat + 10 < 65536) :
    pc + UInt16.ofNat 10 = pc + 10 := by
  apply UInt16.toNat.inj
  rw [word_add_toNat pc 10 h, UInt16.toNat_add]
  have : (10 : Word).toNat = 10 := rfl
  rw [this, Nat.mod_eq_of_lt h]

theorem add_ofNat_11 (pc : Word) (h : pc.toNat + 11 < 65536) :
    pc + UInt16.ofNat 11 = pc + 11 := by
  apply UInt16.toNat.inj
  rw [word_add_toNat pc 11 h, UInt16.toNat_add]
  have : (11 : Word).toNat = 11 := rfl
  rw [this, Nat.mod_eq_of_lt h]

theorem add_ofNat_12 (pc : Word) (h : pc.toNat + 12 < 65536) :
    pc + UInt16.ofNat 12 = pc + 12 := by
  apply UInt16.toNat.inj
  rw [word_add_toNat pc 12 h, UInt16.toNat_add]
  have : (12 : Word).toNat = 12 := rfl
  rw [this, Nat.mod_eq_of_lt h]

/-- `0 - (0 - w) = w` in wrap-around 16-bit arithmetic. -/
theorem sub_sub_zero (w : Word) : (0 : Word) - (0 - w) = w := by
  apply UInt16.toNat.inj
  have hw : w.toNat < 65536 := by
    simpa [show UInt16.size = 65536 from rfl] using UInt16.toNat_lt_size w
  rw [UInt16.toNat_sub, UInt16.toNat_sub]
  have hpow : (2 : Nat) ^ 16 = 65536 := rfl
  simp [hpow]
  by_cases h0 : w.toNat = 0
  · simp [h0]
  · have hpos : 0 < w.toNat := Nat.pos_of_ne_zero h0
    have hmid : 65536 - w.toNat < 65536 := Nat.sub_lt (by decide) hpos
    rw [Nat.mod_eq_of_lt hmid, Nat.sub_sub_self (Nat.le_of_lt hw), Nat.mod_eq_of_lt hw]

/-- `a - (0 - b) = a + b` in wrap-around 16-bit arithmetic. -/
theorem add_sub_neg (a b : Word) : a - (0 - b) = a + b := by
  apply UInt16.toNat.inj
  have hb : b.toNat < 65536 := by
    simpa [show UInt16.size = 65536 from rfl] using UInt16.toNat_lt_size b
  rw [UInt16.toNat_sub, UInt16.toNat_add, UInt16.toNat_sub]
  have hpow : (2 : Nat) ^ 16 = 65536 := rfl
  simp [hpow]
  by_cases h0 : b.toNat = 0
  · simp [h0]
  · have hpos : 0 < b.toNat := Nat.pos_of_ne_zero h0
    have hmid : 65536 - b.toNat < 65536 := Nat.sub_lt (by decide) hpos
    rw [Nat.mod_eq_of_lt hmid]
    have : 65536 - (65536 - b.toNat) + a.toNat = a.toNat + b.toNat := by omega
    rw [this]

/-! ## Multi-instruction assembler macros

`MOV src dst` is 12 cells / 4 steps: `ZERO dst; SUB src, Z; SUB Z, dst; ZERO Z`.
`ADD src dst` is 9 cells / 3 steps: `SUB src, Z; SUB Z, dst; ZERO Z`.
`INC x` is `ADD ONE x` (cell 3 must hold `1`).
-/

/-- `MOV src, dst` (12 cells, 4 steps). Requires `Z = 0`, `dst ≠ Z`,
neither address is I/O, `src ≠ dst`, and the instruction cells are
not `dst` or `Z` (so the encoding is preserved while the macro runs). -/
theorem runN_MOV {s : Machine} {src dst : Word}
    (hh : s.halted = false)
    (hpc : s.pc.toNat + 12 ≤ 32768)
    (hpc0 : 0 < s.pc.toNat)
    (hZ : s.mem.get 0 = 0)
    (hdstZ : dst ≠ 0)
    (hsrcD : src ≠ dst)
    (hsrcN : src ≠ 0xFFFF)
    (hdstN : dst ≠ 0xFFFF)
    (h0 : s.mem.get s.pc = dst)
    (h1 : s.mem.get (s.pc + UInt16.ofNat 1) = dst)
    (h2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3)
    (h3 : s.mem.get (s.pc + UInt16.ofNat 3) = src)
    (h4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0)
    (h5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6)
    (h6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0)
    (h7 : s.mem.get (s.pc + UInt16.ofNat 7) = dst)
    (h8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9)
    (h9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0)
    (h10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0)
    (h11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12)
    (hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ dst)
    (hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ 0) :
    let s4 := runN s 4
    s4.pc = s.pc + UInt16.ofNat 12 ∧
    s4.halted = false ∧
    s4.mem.get dst = s.mem.get src ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get src = s.mem.get src ∧
    (∀ a, a ≠ dst → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hbound {k : Nat} (hk : k ≤ 12) :
      (s.pc + UInt16.ofNat k).toNat = s.pc.toNat + k :=
    word_add_toNat s.pc k (Nat.lt_of_le_of_lt (Nat.add_le_add_left hk _) (by omega))
  have hpc_lt {k : Nat} (hk : k < 12) :
      (s.pc + UInt16.ofNat k).toNat < 32768 := by
    rw [hbound (Nat.le_of_lt hk)]
    omega
  -- Step 1: ZERO dst
  have hp0 : s.pc.toNat < 32768 := by omega
  have hstep1 := step_ZERO (s := s) (x := dst) hh hp0 h0 h1 h2 hdstN
  let s1 := step s
  have hs1 : s1 = { s with mem := s.mem.set dst 0, pc := s.pc + 3 } := hstep1
  have hs1h : s1.halted = false := by simpa [hs1] using hh
  have hs1pc : s1.pc = s.pc + 3 := by simpa [hs1]
  have hs1pcn : s1.pc.toNat < 32768 := by
    simpa [hs1pc, add_ofNat_3 s.pc (by omega)] using hpc_lt (k := 3) (by decide)
  have get1 (off : Nat) (ho : off < 12) :
      s1.mem.get (s.pc + UInt16.ofNat off) = s.mem.get (s.pc + UInt16.ofNat off) := by
    have hne := hcodeD off ho
    simpa [hs1] using Mem.get_set_ne s.mem dst (s.pc + UInt16.ofNat off) 0 hne
  have hs1Z : s1.mem.get 0 = 0 := by
    have : s1.mem.get 0 = s.mem.get 0 := by
      simpa [hs1] using Mem.get_set_ne s.mem dst 0 0 hdstZ.symm
    exact this.trans hZ
  have hs1src : s1.mem.get src = s.mem.get src := by
    simpa [hs1] using Mem.get_set_ne s.mem dst src 0 hsrcD
  -- Step 2: SUB src, Z
  have ha2 : s1.mem.get s1.pc = src := by
    have : s1.pc = s.pc + UInt16.ofNat 3 := by simpa [hs1pc, add_ofNat_3 s.pc (by omega)]
    rw [this, get1 3 (by decide), h3]
  have hb2 : s1.mem.get (s1.pc + 1) = 0 := by
    have : s1.pc + 1 = s.pc + UInt16.ofNat 4 := by
      have : s1.pc = s.pc + UInt16.ofNat 3 := by simpa [hs1pc, add_ofNat_3 s.pc (by omega)]
      rw [this]
      -- (pc+3)+1 = pc+4
      apply UInt16.toNat.inj
      have h3' := hbound (k := 3) (by decide)
      have h4' := hbound (k := 4) (by decide)
      rw [UInt16.toNat_add, h3']
      simp
    rw [this, get1 4 (by decide), h4]
  have hc2 : s1.mem.get (s1.pc + 2) = s1.pc + 3 := by
    have hp2 : s1.pc + 2 = s.pc + UInt16.ofNat 5 := by
      have : s1.pc = s.pc + UInt16.ofNat 3 := by simpa [hs1pc, add_ofNat_3 s.pc (by omega)]
      rw [this]
      apply UInt16.toNat.inj
      have h3' := hbound (k := 3) (by decide)
      have h5' := hbound (k := 5) (by decide)
      rw [UInt16.toNat_add, h3']
      simp
    have hd : s1.pc + 3 = s.pc + UInt16.ofNat 6 := by
      have : s1.pc = s.pc + UInt16.ofNat 3 := by simpa [hs1pc, add_ofNat_3 s.pc (by omega)]
      rw [this]
      apply UInt16.toNat.inj
      have h3' := hbound (k := 3) (by decide)
      have h6' := hbound (k := 6) (by decide)
      rw [UInt16.toNat_add, h3']
      simp
    rw [hp2, hd, get1 5 (by decide), h5]
  have hstep2 := step_SUB (s := s1) (a := src) (b := 0) hs1h hs1pcn ha2 hb2 hc2
    hsrcN (by decide)
  let s2 := step s1
  have hs2 : s2 = { s1 with mem := s1.mem.set 0 (s1.mem.get 0 - s1.mem.get src), pc := s1.pc + 3 } := hstep2
  have hs2h : s2.halted = false := by simpa [hs2] using hs1h
  have hs2pc : s2.pc = s.pc + 6 := by
    have : s1.pc + 3 = s.pc + UInt16.ofNat 6 := by
      have : s1.pc = s.pc + UInt16.ofNat 3 := by simpa [hs1pc, add_ofNat_3 s.pc (by omega)]
      rw [this]
      apply UInt16.toNat.inj
      have h3' := hbound (k := 3) (by decide)
      have h6' := hbound (k := 6) (by decide)
      rw [UInt16.toNat_add, h3']
      simp
    simpa [hs2, hs1pc, add_ofNat_3 s.pc (by omega), add_ofNat_6 s.pc (by omega)] using this
  have hs2pcn : s2.pc.toNat < 32768 := by
    simpa [hs2pc, add_ofNat_6 s.pc (by omega)] using hpc_lt (k := 6) (by decide)
  have hs2Z : s2.mem.get 0 = 0 - s.mem.get src := by
    have : s2.mem.get 0 = s1.mem.get 0 - s1.mem.get src := by
      simpa [hs2] using Mem.get_set_eq s1.mem 0 (s1.mem.get 0 - s1.mem.get src)
    simpa [this, hs1Z, hs1src]
  have hs2dst : s2.mem.get dst = 0 := by
    have : s2.mem.get dst = s1.mem.get dst := by
      simpa [hs2] using Mem.get_set_ne s1.mem 0 dst (s1.mem.get 0 - s1.mem.get src) hdstZ
    have h1d : s1.mem.get dst = 0 := by
      simpa [hs1] using Mem.get_set_eq s.mem dst 0
    exact this.trans h1d
  have hs2src : s2.mem.get src = s.mem.get src := by
    by_cases hsz : src = 0
    · subst hsz
      simpa [hs2Z, hZ]
    · have : s2.mem.get src = s1.mem.get src := by
        simpa [hs2] using Mem.get_set_ne s1.mem 0 src (s1.mem.get 0 - s1.mem.get src) hsz
      exact this.trans hs1src
  have get2 (off : Nat) (ho : off < 12) :
      s2.mem.get (s.pc + UInt16.ofNat off) = s.mem.get (s.pc + UInt16.ofNat off) := by
    have hne0 := hcodeZ off ho
    have : s2.mem.get (s.pc + UInt16.ofNat off) =
        s1.mem.get (s.pc + UInt16.ofNat off) := by
      simpa [hs2] using
        Mem.get_set_ne s1.mem 0 (s.pc + UInt16.ofNat off)
          (s1.mem.get 0 - s1.mem.get src) hne0
    exact this.trans (get1 off ho)
  -- Step 3: SUB Z, dst
  have ha3 : s2.mem.get s2.pc = 0 := by
    have : s2.pc = s.pc + UInt16.ofNat 6 := by simpa [hs2pc, add_ofNat_6 s.pc (by omega)]
    rw [this, get2 6 (by decide), h6]
  have hb3 : s2.mem.get (s2.pc + 1) = dst := by
    have : s2.pc + 1 = s.pc + UInt16.ofNat 7 := by
      have : s2.pc = s.pc + UInt16.ofNat 6 := by simpa [hs2pc, add_ofNat_6 s.pc (by omega)]
      rw [this]
      apply UInt16.toNat.inj
      have h6' := hbound (k := 6) (by decide)
      have h7' := hbound (k := 7) (by decide)
      rw [UInt16.toNat_add, h6']
      simp
    rw [this, get2 7 (by decide), h7]
  have hc3 : s2.mem.get (s2.pc + 2) = s2.pc + 3 := by
    have hp2 : s2.pc + 2 = s.pc + UInt16.ofNat 8 := by
      have : s2.pc = s.pc + UInt16.ofNat 6 := by simpa [hs2pc, add_ofNat_6 s.pc (by omega)]
      rw [this]
      apply UInt16.toNat.inj
      have h6' := hbound (k := 6) (by decide)
      have h8' := hbound (k := 8) (by decide)
      rw [UInt16.toNat_add, h6']
      simp
    have hd : s2.pc + 3 = s.pc + UInt16.ofNat 9 := by
      have : s2.pc = s.pc + UInt16.ofNat 6 := by simpa [hs2pc, add_ofNat_6 s.pc (by omega)]
      rw [this]
      apply UInt16.toNat.inj
      have h6' := hbound (k := 6) (by decide)
      have h9' := hbound (k := 9) (by decide)
      rw [UInt16.toNat_add, h6']
      simp
    rw [hp2, hd, get2 8 (by decide), h8]
  have hstep3 := step_SUB (s := s2) (a := 0) (b := dst) hs2h hs2pcn ha3 hb3 hc3
    (by decide) hdstN
  let s3 := step s2
  have hs3 : s3 = { s2 with mem := s2.mem.set dst (s2.mem.get dst - s2.mem.get 0), pc := s2.pc + 3 } := hstep3
  have hs3h : s3.halted = false := by simpa [hs3] using hs2h
  have hs3pc : s3.pc = s.pc + 9 := by
    have : s2.pc + 3 = s.pc + UInt16.ofNat 9 := by
      have : s2.pc = s.pc + UInt16.ofNat 6 := by simpa [hs2pc, add_ofNat_6 s.pc (by omega)]
      rw [this]
      apply UInt16.toNat.inj
      have h6' := hbound (k := 6) (by decide)
      have h9' := hbound (k := 9) (by decide)
      rw [UInt16.toNat_add, h6']
      simp
    simpa [hs3, hs2pc, add_ofNat_6 s.pc (by omega), add_ofNat_9 s.pc (by omega)] using this
  have hs3pcn : s3.pc.toNat < 32768 := by
    simpa [hs3pc, add_ofNat_9 s.pc (by omega)] using hpc_lt (k := 9) (by decide)
  have hs3dst : s3.mem.get dst = s.mem.get src := by
    have : s3.mem.get dst = s2.mem.get dst - s2.mem.get 0 := by
      simpa [hs3] using Mem.get_set_eq s2.mem dst (s2.mem.get dst - s2.mem.get 0)
    -- 0 - (0 - src) = src
    have : s2.mem.get dst - s2.mem.get 0 = (0 : Word) - (0 - s.mem.get src) := by
      simp [hs2dst, hs2Z]
    rw [‹s3.mem.get dst = _›, this, sub_sub_zero]
  have hs3Z : s3.mem.get 0 = 0 - s.mem.get src := by
    have : s3.mem.get 0 = s2.mem.get 0 := by
      simpa [hs3] using Mem.get_set_ne s2.mem dst 0 (s2.mem.get dst - s2.mem.get 0) hdstZ.symm
    exact this.trans hs2Z
  have get3 (off : Nat) (ho : off < 12) :
      s3.mem.get (s.pc + UInt16.ofNat off) = s.mem.get (s.pc + UInt16.ofNat off) := by
    have hne := hcodeD off ho
    have : s3.mem.get (s.pc + UInt16.ofNat off) =
        s2.mem.get (s.pc + UInt16.ofNat off) := by
      simpa [hs3] using
        Mem.get_set_ne s2.mem dst (s.pc + UInt16.ofNat off)
          (s2.mem.get dst - s2.mem.get 0) hne
    exact this.trans (get2 off ho)
  -- Step 4: ZERO Z
  have ha4 : s3.mem.get s3.pc = 0 := by
    have : s3.pc = s.pc + UInt16.ofNat 9 := by simpa [hs3pc, add_ofNat_9 s.pc (by omega)]
    rw [this, get3 9 (by decide), h9]
  have hb4 : s3.mem.get (s3.pc + 1) = 0 := by
    have : s3.pc + 1 = s.pc + UInt16.ofNat 10 := by
      have : s3.pc = s.pc + UInt16.ofNat 9 := by simpa [hs3pc, add_ofNat_9 s.pc (by omega)]
      rw [this]
      apply UInt16.toNat.inj
      have h9' := hbound (k := 9) (by decide)
      have h10' := hbound (k := 10) (by decide)
      rw [UInt16.toNat_add, h9']
      simp
    rw [this, get3 10 (by decide), h10]
  have hc4 : s3.mem.get (s3.pc + 2) = s3.pc + 3 := by
    have hp2 : s3.pc + 2 = s.pc + UInt16.ofNat 11 := by
      have : s3.pc = s.pc + UInt16.ofNat 9 := by simpa [hs3pc, add_ofNat_9 s.pc (by omega)]
      rw [this]
      apply UInt16.toNat.inj
      have h9' := hbound (k := 9) (by decide)
      have h11' := hbound (k := 11) (by decide)
      rw [UInt16.toNat_add, h9']
      simp
    have hd : s3.pc + 3 = s.pc + UInt16.ofNat 12 := by
      have : s3.pc = s.pc + UInt16.ofNat 9 := by simpa [hs3pc, add_ofNat_9 s.pc (by omega)]
      rw [this]
      apply UInt16.toNat.inj
      have h9' := hbound (k := 9) (by decide)
      have h12' := hbound (k := 12) (by decide)
      rw [UInt16.toNat_add, h9']
      simp
    rw [hp2, hd, get3 11 (by decide), h11]
  have hstep4 := step_ZERO (s := s3) (x := 0) hs3h hs3pcn ha4 hb4 hc4 (by decide)
  let s4' := step s3
  have hs4eq : s4' = { s3 with mem := s3.mem.set 0 0, pc := s3.pc + 3 } := hstep4
  have hs4pc' : s4'.pc = s.pc + 12 := by
    have : s3.pc + 3 = s.pc + UInt16.ofNat 12 := by
      have : s3.pc = s.pc + UInt16.ofNat 9 := by simpa [hs3pc, add_ofNat_9 s.pc (by omega)]
      rw [this]
      apply UInt16.toNat.inj
      have h9' := hbound (k := 9) (by decide)
      have h12' := hbound (k := 12) (by decide)
      rw [UInt16.toNat_add, h9']
      simp
    simpa [hs4eq, hs3pc, add_ofNat_9 s.pc (by omega), add_ofNat_12 s.pc (by omega)] using this
  have hr0 : runN s 4 = runN (step s) 3 :=
    runN_succ_go s 3 hh hp0
  have hr1 : runN s1 3 = runN (step s1) 2 :=
    runN_succ_go s1 2 hs1h hs1pcn
  have hr2 : runN s2 2 = runN (step s2) 1 :=
    runN_succ_go s2 1 hs2h hs2pcn
  have hr3 : runN s3 1 = runN (step s3) 0 :=
    runN_succ_go s3 0 hs3h hs3pcn
  have hrun : s4 = s4' := by
    calc
      s4 = runN s 4 := rfl
      _  = runN (step s) 3 := hr0
      _  = runN s1 3 := rfl
      _  = runN (step s1) 2 := hr1
      _  = runN s2 2 := rfl
      _  = runN (step s2) 1 := hr2
      _  = runN s3 1 := rfl
      _  = runN (step s3) 0 := hr3
      _  = step s3 := runN_zero _
      _  = s4' := rfl
  have hs4h : s4.halted = false := by
    have : s4'.halted = false := by simpa [hs4eq] using hs3h
    simpa [hrun] using this
  have hs4pc : s4.pc = s.pc + UInt16.ofNat 12 := by simpa [hrun] using hs4pc'
  have hdst : s4.mem.get dst = s.mem.get src := by
    have : s4'.mem.get dst = s3.mem.get dst := by
      simpa [hs4eq] using Mem.get_set_ne s3.mem 0 dst 0 hdstZ
    simpa [hrun, this] using hs3dst
  have hZ' : s4.mem.get 0 = 0 := by
    have : s4'.mem.get 0 = 0 := by
      simpa [hs4eq] using Mem.get_set_eq s3.mem 0 0
    simpa [hrun] using this
  have hsrc : s4.mem.get src = s.mem.get src := by
    by_cases hz : src = 0
    · subst hz
      simpa [hrun, hZ] using hZ'
    · have hs3src : s3.mem.get src = s.mem.get src := by
        have : s3.mem.get src = s2.mem.get src := by
          simpa [hs3] using Mem.get_set_ne s2.mem dst src
            (s2.mem.get dst - s2.mem.get 0) hsrcD
        exact this.trans hs2src
      have : s4'.mem.get src = s3.mem.get src := by
        simpa [hs4eq] using Mem.get_set_ne s3.mem 0 src 0 hz
      simpa [hrun, this] using hs3src
  have hrest : ∀ a, a ≠ dst → a ≠ 0 → s4.mem.get a = s.mem.get a := by
    intro a had hazz
    have a1 : s1.mem.get a = s.mem.get a := by
      simpa [hs1] using Mem.get_set_ne s.mem dst a 0 had
    have a2 : s2.mem.get a = s1.mem.get a := by
      simpa [hs2] using Mem.get_set_ne s1.mem 0 a (s1.mem.get 0 - s1.mem.get src) hazz
    have a3 : s3.mem.get a = s2.mem.get a := by
      simpa [hs3] using Mem.get_set_ne s2.mem dst a (s2.mem.get dst - s2.mem.get 0) had
    have a4 : s4'.mem.get a = s3.mem.get a := by
      simpa [hs4eq] using Mem.get_set_ne s3.mem 0 a 0 hazz
    calc
      s4.mem.get a = s4'.mem.get a := by simpa [hrun]
      _ = s3.mem.get a := a4
      _ = s2.mem.get a := a3
      _ = s1.mem.get a := a2
      _ = s.mem.get a := a1
  exact ⟨hs4pc, hs4h, hdst, hZ', hsrc, hrest⟩

/-- `ADD src, dst` (9 cells, 3 steps): `Z -= src; dst -= Z; ZERO Z`. -/
theorem runN_ADD {s : Machine} {src dst : Word}
    (hh : s.halted = false)
    (hpc : s.pc.toNat + 9 ≤ 32768)
    (hpc0 : 0 < s.pc.toNat)
    (hZ : s.mem.get 0 = 0)
    (hdstZ : dst ≠ 0)
    (hsrcN : src ≠ 0xFFFF)
    (hdstN : dst ≠ 0xFFFF)
    (h0 : s.mem.get s.pc = src)
    (h1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0)
    (h2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3)
    (h3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0)
    (h4 : s.mem.get (s.pc + UInt16.ofNat 4) = dst)
    (h5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6)
    (h6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0)
    (h7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0)
    (h8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9)
    (hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ dst)
    (hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ 0) :
    let s3 := runN s 3
    s3.pc = s.pc + UInt16.ofNat 9 ∧
    s3.halted = false ∧
    s3.mem.get dst = s.mem.get dst + s.mem.get src ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ dst → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hbound {k : Nat} (hk : k ≤ 9) :
      (s.pc + UInt16.ofNat k).toNat = s.pc.toNat + k :=
    word_add_toNat s.pc k (Nat.lt_of_le_of_lt (Nat.add_le_add_left hk _) (by omega))
  have hpc_lt {k : Nat} (hk : k < 9) :
      (s.pc + UInt16.ofNat k).toNat < 32768 := by
    rw [hbound (Nat.le_of_lt hk)]
    omega
  have add_off (a b : Nat) (ha : a ≤ 9) (hb : a + b ≤ 9) :
      (s.pc + UInt16.ofNat a) + UInt16.ofNat b = s.pc + UInt16.ofNat (a + b) := by
    apply UInt16.toNat.inj
    have ha' := hbound ha
    have hab := hbound hb
    rw [UInt16.toNat_add, ha']
    have hn : b < 65536 := by omega
    have : (UInt16.ofNat b).toNat = b := UInt16.toNat_ofNat_of_lt hn
    rw [this]
    have : s.pc.toNat + a + b < 65536 := by omega
    rw [Nat.mod_eq_of_lt this, hab]
    omega
  have hp0 : s.pc.toNat < 32768 := by omega
  -- Step 1: SUB src, Z
  have hstep1 := step_SUB (s := s) (a := src) (b := 0) hh hp0 h0 h1 h2 hsrcN (by decide)
  let s1 := step s
  have hs1 : s1 = { s with mem := s.mem.set 0 (s.mem.get 0 - s.mem.get src), pc := s.pc + 3 } := hstep1
  have hs1h : s1.halted = false := by simpa [hs1] using hh
  have hs1pc : s1.pc = s.pc + 3 := by simpa [hs1]
  have hs1pcn : s1.pc.toNat < 32768 := by
    simpa [hs1pc, add_ofNat_3 s.pc (by omega)] using hpc_lt (k := 3) (by decide)
  have hs1Z : s1.mem.get 0 = 0 - s.mem.get src := by
    have : s1.mem.get 0 = s.mem.get 0 - s.mem.get src := by
      simpa [hs1] using Mem.get_set_eq s.mem 0 (s.mem.get 0 - s.mem.get src)
    simpa [this, hZ]
  have hs1dst : s1.mem.get dst = s.mem.get dst := by
    simpa [hs1] using Mem.get_set_ne s.mem 0 dst (s.mem.get 0 - s.mem.get src) hdstZ
  have get1 (off : Nat) (ho : off < 9) :
      s1.mem.get (s.pc + UInt16.ofNat off) = s.mem.get (s.pc + UInt16.ofNat off) := by
    have hne := hcodeZ off ho
    simpa [hs1] using Mem.get_set_ne s.mem 0 (s.pc + UInt16.ofNat off)
      (s.mem.get 0 - s.mem.get src) hne
  -- Step 2: SUB Z, dst
  have ha2 : s1.mem.get s1.pc = 0 := by
    have : s1.pc = s.pc + UInt16.ofNat 3 := by simpa [hs1pc, add_ofNat_3 s.pc (by omega)]
    rw [this, get1 3 (by decide), h3]
  have hb2 : s1.mem.get (s1.pc + 1) = dst := by
    have : s1.pc + 1 = s.pc + UInt16.ofNat 4 := by
      have : s1.pc = s.pc + UInt16.ofNat 3 := by simp [hs1pc, add_ofNat_3 s.pc (by omega)]
      rw [← add_ofNat_1 s1.pc (by omega), this]
      exact word_add_off s.pc 3 1 (by omega) (by omega) (by decide)
    rw [this, get1 4 (by decide), h4]
  have hc2 : s1.mem.get (s1.pc + 2) = s1.pc + 3 := by
    have hp2 : s1.pc + 2 = s.pc + UInt16.ofNat 5 := by
      have : s1.pc = s.pc + UInt16.ofNat 3 := by simp [hs1pc, add_ofNat_3 s.pc (by omega)]
      rw [← add_ofNat_2 s1.pc (by omega), this]
      exact word_add_off s.pc 3 2 (by omega) (by omega) (by decide)
    have hd : s1.pc + 3 = s.pc + UInt16.ofNat 6 := by
      have : s1.pc = s.pc + UInt16.ofNat 3 := by simp [hs1pc, add_ofNat_3 s.pc (by omega)]
      rw [← add_ofNat_3 s1.pc (by omega), this]
      exact word_add_off s.pc 3 3 (by omega) (by omega) (by decide)
    rw [hp2, hd, get1 5 (by decide), h5]
  have hstep2 := step_SUB (s := s1) (a := 0) (b := dst) hs1h hs1pcn ha2 hb2 hc2
    (by decide) hdstN
  let s2 := step s1
  have hs2 : s2 = { s1 with mem := s1.mem.set dst (s1.mem.get dst - s1.mem.get 0), pc := s1.pc + 3 } := hstep2
  have hs2h : s2.halted = false := by simpa [hs2] using hs1h
  have hs2pc : s2.pc = s.pc + 6 := by
    have : s1.pc + 3 = s.pc + UInt16.ofNat 6 := by
      have : s1.pc = s.pc + UInt16.ofNat 3 := by simp [hs1pc, add_ofNat_3 s.pc (by omega)]
      rw [← add_ofNat_3 s1.pc (by omega), this]
      exact word_add_off s.pc 3 3 (by omega) (by omega) (by decide)
    simpa [hs2, hs1pc, add_ofNat_3 s.pc (by omega), add_ofNat_6 s.pc (by omega)] using this
  have hs2pcn : s2.pc.toNat < 32768 := by
    simpa [hs2pc, add_ofNat_6 s.pc (by omega)] using hpc_lt (k := 6) (by decide)
  have hs2dst : s2.mem.get dst = s.mem.get dst + s.mem.get src := by
    have : s2.mem.get dst = s1.mem.get dst - s1.mem.get 0 := by
      simpa [hs2] using Mem.get_set_eq s1.mem dst (s1.mem.get dst - s1.mem.get 0)
    -- dst - (0 - src) = dst + src
    have hneg : s1.mem.get dst - s1.mem.get 0 =
        s.mem.get dst - (0 - s.mem.get src) := by
      simp [hs1dst, hs1Z]
    have hadd : s.mem.get dst - (0 - s.mem.get src) =
        s.mem.get dst + s.mem.get src := add_sub_neg _ _
    exact this.trans (hneg.trans hadd)
  have get2 (off : Nat) (ho : off < 9) :
      s2.mem.get (s.pc + UInt16.ofNat off) = s.mem.get (s.pc + UInt16.ofNat off) := by
    have hne := hcodeD off ho
    have : s2.mem.get (s.pc + UInt16.ofNat off) =
        s1.mem.get (s.pc + UInt16.ofNat off) := by
      simpa [hs2] using Mem.get_set_ne s1.mem dst (s.pc + UInt16.ofNat off)
        (s1.mem.get dst - s1.mem.get 0) hne
    exact this.trans (get1 off ho)
  -- Step 3: ZERO Z
  have ha3 : s2.mem.get s2.pc = 0 := by
    have : s2.pc = s.pc + UInt16.ofNat 6 := by simpa [hs2pc, add_ofNat_6 s.pc (by omega)]
    rw [this, get2 6 (by decide), h6]
  have hb3 : s2.mem.get (s2.pc + 1) = 0 := by
    have : s2.pc + 1 = s.pc + UInt16.ofNat 7 := by
      have : s2.pc = s.pc + UInt16.ofNat 6 := by simp [hs2pc, add_ofNat_6 s.pc (by omega)]
      rw [← add_ofNat_1 s2.pc (by omega), this]
      exact word_add_off s.pc 6 1 (by omega) (by omega) (by decide)
    rw [this, get2 7 (by decide), h7]
  have hc3 : s2.mem.get (s2.pc + 2) = s2.pc + 3 := by
    have hp2 : s2.pc + 2 = s.pc + UInt16.ofNat 8 := by
      have : s2.pc = s.pc + UInt16.ofNat 6 := by simp [hs2pc, add_ofNat_6 s.pc (by omega)]
      rw [← add_ofNat_2 s2.pc (by omega), this]
      exact word_add_off s.pc 6 2 (by omega) (by omega) (by decide)
    have hd : s2.pc + 3 = s.pc + UInt16.ofNat 9 := by
      have : s2.pc = s.pc + UInt16.ofNat 6 := by simp [hs2pc, add_ofNat_6 s.pc (by omega)]
      rw [← add_ofNat_3 s2.pc (by omega), this]
      exact word_add_off s.pc 6 3 (by omega) (by omega) (by decide)
    rw [hp2, hd, get2 8 (by decide), h8]
  have hstep3 := step_ZERO (s := s2) (x := 0) hs2h hs2pcn ha3 hb3 hc3 (by decide)
  let s3' := step s2
  have hs3eq : s3' = { s2 with mem := s2.mem.set 0 0, pc := s2.pc + 3 } := hstep3
  have hs3pc' : s3'.pc = s.pc + 9 := by
    have : s2.pc + 3 = s.pc + UInt16.ofNat 9 := by
      have : s2.pc = s.pc + UInt16.ofNat 6 := by simp [hs2pc, add_ofNat_6 s.pc (by omega)]
      rw [← add_ofNat_3 s2.pc (by omega), this]
      exact word_add_off s.pc 6 3 (by omega) (by omega) (by decide)
    simpa [hs3eq, hs2pc, add_ofNat_6 s.pc (by omega), add_ofNat_9 s.pc (by omega)] using this
  have hr0 : runN s 3 = runN (step s) 2 := runN_succ_go s 2 hh hp0
  have hr1 : runN s1 2 = runN (step s1) 1 := runN_succ_go s1 1 hs1h hs1pcn
  have hr2 : runN s2 1 = runN (step s2) 0 := runN_succ_go s2 0 hs2h hs2pcn
  have hrun : s3 = s3' := by
    calc
      s3 = runN s 3 := rfl
      _  = runN (step s) 2 := hr0
      _  = runN s1 2 := rfl
      _  = runN (step s1) 1 := hr1
      _  = runN s2 1 := rfl
      _  = runN (step s2) 0 := hr2
      _  = step s2 := runN_zero _
      _  = s3' := rfl
  have hs3h : s3.halted = false := by
    have : s3'.halted = false := by simpa [hs3eq] using hs2h
    simpa [hrun] using this
  have hs3pc : s3.pc = s.pc + 9 := by simpa [hrun] using hs3pc'
  have hdst : s3.mem.get dst = s.mem.get dst + s.mem.get src := by
    have : s3'.mem.get dst = s2.mem.get dst := by
      simpa [hs3eq] using Mem.get_set_ne s2.mem 0 dst 0 hdstZ
    simpa [hrun, this] using hs2dst
  have hZ' : s3.mem.get 0 = 0 := by
    have : s3'.mem.get 0 = 0 := by
      simpa [hs3eq] using Mem.get_set_eq s2.mem 0 0
    simpa [hrun] using this
  have hrest : ∀ a, a ≠ dst → a ≠ 0 → s3.mem.get a = s.mem.get a := by
    intro a had hazz
    have a1 : s1.mem.get a = s.mem.get a := by
      simpa [hs1] using Mem.get_set_ne s.mem 0 a (s.mem.get 0 - s.mem.get src) hazz
    have a2 : s2.mem.get a = s1.mem.get a := by
      simpa [hs2] using Mem.get_set_ne s1.mem dst a (s1.mem.get dst - s1.mem.get 0) had
    have a3 : s3'.mem.get a = s2.mem.get a := by
      simpa [hs3eq] using Mem.get_set_ne s2.mem 0 a 0 hazz
    calc
      s3.mem.get a = s3'.mem.get a := by simpa [hrun]
      _ = s2.mem.get a := a3
      _ = s1.mem.get a := a2
      _ = s.mem.get a := a1
  exact ⟨hs3pc, hs3h, hdst, hZ', hrest⟩

/-- `INC x` is `ADD ONE x` (9 cells, 3 steps). Cell 3 must hold `1`. -/
theorem runN_INC {s : Machine} {x : Word}
    (hh : s.halted = false)
    (hpc : s.pc.toNat + 9 ≤ 32768)
    (hpc0 : 0 < s.pc.toNat)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hxZ : x ≠ 0)
    (hxN : x ≠ 0xFFFF)
    (hx3 : x ≠ 3)
    (h0 : s.mem.get s.pc = 3)
    (h1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0)
    (h2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3)
    (h3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0)
    (h4 : s.mem.get (s.pc + UInt16.ofNat 4) = x)
    (h5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6)
    (h6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0)
    (h7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0)
    (h8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9)
    (hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ x)
    (hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ 0) :
    let s3 := runN s 3
    s3.pc = s.pc + UInt16.ofNat 9 ∧
    s3.halted = false ∧
    s3.mem.get x = s.mem.get x + 1 ∧
    s3.mem.get 0 = 0 ∧
    s3.mem.get 3 = 1 := by
  intro s3
  have hadd := runN_ADD (s := s) (src := 3) (dst := x)
    hh hpc hpc0 hZ hxZ (by decide) hxN h0 h1 h2 h3 h4 h5 h6 h7 h8 hcodeD hcodeZ
  have hrest := hadd.2.2.2.2
  have h3stay : s3.mem.get 3 = s.mem.get 3 :=
    hrest 3 hx3.symm (by decide)
  refine ⟨hadd.1, hadd.2.1, ?inc, hadd.2.2.2.1, ?one⟩
  · simpa [hONE] using hadd.2.2.1
  · simpa [h3stay] using hONE

end IntFmt.Subleq
