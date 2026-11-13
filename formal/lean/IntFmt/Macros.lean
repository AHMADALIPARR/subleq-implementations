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

end IntFmt.Subleq
