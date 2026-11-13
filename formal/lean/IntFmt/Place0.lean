/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

`DIGITS` prelude and the `P0_LOOP`..`P0_DONE` place-10000 loop on the
assembled `intfmt.dec` image. Block lemmas, not end-to-end correctness.

Invariant at `P0_LOOP`: `Q0 * 10000 + N` is the value of `N` on entry
to the loop (after the five `ZERO`s). The loop exits at `P0_DONE` with
`N < 10000` in `p0PlaceSteps N.toNat` steps (≤ 16 + 21 * (N / 10000)).
-/

import IntFmt.PlaceCore

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

private theorem cell160 (off : Nat) (h : off < 16) :
    intfmtImage[160 + off]! = decChunk010[off]! :=
  extract_chunk 160 decChunk010 image_chunk010 off h (by decide)

private theorem cell176 (off : Nat) (h : off < 16) :
    intfmtImage[176 + off]! = decChunk011[off]! :=
  extract_chunk 176 decChunk011 image_chunk011 off h (by decide)

private theorem cell192 (off : Nat) (h : off < 16) :
    intfmtImage[192 + off]! = decChunk012[off]! :=
  extract_chunk 192 decChunk012 image_chunk012 off h (by decide)

private theorem cell208 (off : Nat) (h : off < 16) :
    intfmtImage[208 + off]! = decChunk013[off]! :=
  extract_chunk 208 decChunk013 image_chunk013 off h (by decide)

private theorem cell224 (off : Nat) (h : off < 16) :
    intfmtImage[224 + off]! = decChunk014[off]! :=
  extract_chunk 224 decChunk014 image_chunk014 off h (by decide)

private theorem cell240 (off : Nat) (h : off < 16) :
    intfmtImage[240 + off]! = decChunk015[off]! :=
  extract_chunk 240 decChunk015 image_chunk015 off h (by decide)

private theorem cell256 (off : Nat) (h : off < 16) :
    intfmtImage[256 + off]! = decChunk016[off]! :=
  extract_chunk 256 decChunk016 image_chunk016 off h (by decide)

/-- After the five `ZERO Q0`..`ZERO Q4` at `DIGITS` (pc 174), the machine
is at `P0_LOOP` (pc 189) with `Q0..Q4 = 0`. -/
theorem digits_zero_Qs {s : Machine}
    (hpc : s.pc = 174)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 174 ≤ k → k < 189 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 189 ∧
    s5.halted = false ∧
    s5.mem.get 20 = 0 ∧
    s5.mem.get 21 = 0 ∧
    s5.mem.get 22 = 0 ∧
    s5.mem.get 23 = 0 ∧
    s5.mem.get 24 = 0 ∧
    (∀ a, a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 24 →
      s5.mem.get a = s.mem.get a) := by
  intro s5
  have hp : s.pc = UInt16.ofNat 174 :=
    hpc.trans (rfl : (174 : Word) = UInt16.ofNat 174)
  have g (k : Nat) (h1 : 174 ≤ k) (h2 : k < 189) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 15) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (174 + off) :=
    word_pc_off 174 off hp (by omega)
  -- ZERO Q0 at 174
  have a0 : s.mem.get s.pc = 20 := by
    rw [hp]
    have hval : decChunk010[14]! = 20 := rfl
    exact (g 174 (by decide) (by decide)).trans ((cell160 14 (by decide)).trans hval)
  have a1 : s.mem.get (s.pc + 1) = 20 := by
    have : s.pc + 1 = (175 : Word) := by simp [hpc]
    rw [this, (rfl : (175 : Word) = UInt16.ofNat 175)]
    have hval : decChunk010[15]! = 20 := rfl
    exact (g 175 (by decide) (by decide)).trans ((cell160 15 (by decide)).trans hval)
  have a2 : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp176 : s.pc + 2 = (176 : Word) := by simp [hpc]
    have hp177 : s.pc + 3 = (177 : Word) := by simp [hpc]
    rw [hp176, hp177, (rfl : (176 : Word) = UInt16.ofNat 176)]
    have hval : decChunk011[0]! = 177 := rfl
    have hv : (177 : Word) = UInt16.ofNat 177 := rfl
    exact (g 176 (by decide) (by decide)).trans ((cell176 0 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hz0 := step_ZERO (s := s) (x := 20) hh hpc0 a0 a1 a2 (by decide)
  have hs1pc : (step s).pc = 177 := by
    have : s.pc + 3 = (177 : Word) := by simp [hpc]
    rw [hz0]; exact this
  have hs1h : (step s).halted = false := by rw [hz0]; exact hh
  have hs1Q0 : (step s).mem.get 20 = 0 := by
    rw [hz0]; exact Mem.get_set_eq s.mem 20 0
  have g1 (k : Nat) (h1 : 177 ≤ k) (h2 : k < 189) :
      (step s).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    rw [hz0]
    have hne : UInt16.ofNat k ≠ 20 :=
      ofNat_ne k 20 (by omega) (by omega) (by omega)
    exact (Mem.get_set_ne s.mem 20 (UInt16.ofNat k) 0 hne).trans (g k (by omega) h2)
  -- ZERO Q1 at 177
  have b0 : (step s).mem.get (step s).pc = 21 := by
    have hp1 : (step s).pc = UInt16.ofNat 177 :=
      hs1pc.trans (rfl : (177 : Word) = UInt16.ofNat 177)
    rw [hp1]
    have hval : decChunk011[1]! = 21 := rfl
    exact (g1 177 (by decide) (by decide)).trans ((cell176 1 (by decide)).trans hval)
  have b1 : (step s).mem.get ((step s).pc + 1) = 21 := by
    have : (step s).pc + 1 = (178 : Word) := by simp [hs1pc]
    rw [this, (rfl : (178 : Word) = UInt16.ofNat 178)]
    have hval : decChunk011[2]! = 21 := rfl
    exact (g1 178 (by decide) (by decide)).trans ((cell176 2 (by decide)).trans hval)
  have b2 : (step s).mem.get ((step s).pc + 2) = (step s).pc + 3 := by
    have hp179 : (step s).pc + 2 = (179 : Word) := by simp [hs1pc]
    have hp180 : (step s).pc + 3 = (180 : Word) := by simp [hs1pc]
    rw [hp179, hp180, (rfl : (179 : Word) = UInt16.ofNat 179)]
    have hval : decChunk011[3]! = 180 := rfl
    have hv : (180 : Word) = UInt16.ofNat 180 := rfl
    exact (g1 179 (by decide) (by decide)).trans ((cell176 3 (by decide)).trans (hval.trans hv))
  have hpc1 : (step s).pc.toNat < 32768 := by simp [hs1pc]
  have hz1 := step_ZERO (s := step s) (x := 21) hs1h hpc1 b0 b1 b2 (by decide)
  have hs2pc : (step (step s)).pc = 180 := by
    have : (step s).pc + 3 = (180 : Word) := by simp [hs1pc]
    rw [hz1]; exact this
  have hs2h : (step (step s)).halted = false := by rw [hz1]; exact hs1h
  have hs2Q1 : (step (step s)).mem.get 21 = 0 := by
    rw [hz1]; exact Mem.get_set_eq (step s).mem 21 0
  have hs2Q0 : (step (step s)).mem.get 20 = 0 := by
    rw [hz1]
    exact (Mem.get_set_ne (step s).mem 21 20 0 (by decide)).trans hs1Q0
  have g2 (k : Nat) (h1 : 180 ≤ k) (h2 : k < 189) :
      (step (step s)).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    rw [hz1]
    have hne : UInt16.ofNat k ≠ 21 :=
      ofNat_ne k 21 (by omega) (by omega) (by omega)
    exact (Mem.get_set_ne (step s).mem 21 (UInt16.ofNat k) 0 hne).trans (g1 k (by omega) h2)
  -- ZERO Q2 at 180
  have c0 : (step (step s)).mem.get (step (step s)).pc = 22 := by
    have hp2 : (step (step s)).pc = UInt16.ofNat 180 :=
      hs2pc.trans (rfl : (180 : Word) = UInt16.ofNat 180)
    rw [hp2]
    have hval : decChunk011[4]! = 22 := rfl
    exact (g2 180 (by decide) (by decide)).trans ((cell176 4 (by decide)).trans hval)
  have c1 : (step (step s)).mem.get ((step (step s)).pc + 1) = 22 := by
    have : (step (step s)).pc + 1 = (181 : Word) := by simp [hs2pc]
    rw [this, (rfl : (181 : Word) = UInt16.ofNat 181)]
    have hval : decChunk011[5]! = 22 := rfl
    exact (g2 181 (by decide) (by decide)).trans ((cell176 5 (by decide)).trans hval)
  have c2 : (step (step s)).mem.get ((step (step s)).pc + 2) = (step (step s)).pc + 3 := by
    have hp182 : (step (step s)).pc + 2 = (182 : Word) := by simp [hs2pc]
    have hp183 : (step (step s)).pc + 3 = (183 : Word) := by simp [hs2pc]
    rw [hp182, hp183, (rfl : (182 : Word) = UInt16.ofNat 182)]
    have hval : decChunk011[6]! = 183 := rfl
    have hv : (183 : Word) = UInt16.ofNat 183 := rfl
    exact (g2 182 (by decide) (by decide)).trans ((cell176 6 (by decide)).trans (hval.trans hv))
  have hpc2 : (step (step s)).pc.toNat < 32768 := by simp [hs2pc]
  have hz2 := step_ZERO (s := step (step s)) (x := 22) hs2h hpc2 c0 c1 c2 (by decide)
  have hs3pc : (step (step (step s))).pc = 183 := by
    have : (step (step s)).pc + 3 = (183 : Word) := by simp [hs2pc]
    rw [hz2]; exact this
  have hs3h : (step (step (step s))).halted = false := by rw [hz2]; exact hs2h
  have hs3Q2 : (step (step (step s))).mem.get 22 = 0 := by
    rw [hz2]; exact Mem.get_set_eq (step (step s)).mem 22 0
  have hs3Q0 : (step (step (step s))).mem.get 20 = 0 := by
    rw [hz2]; exact (Mem.get_set_ne (step (step s)).mem 22 20 0 (by decide)).trans hs2Q0
  have hs3Q1 : (step (step (step s))).mem.get 21 = 0 := by
    rw [hz2]; exact (Mem.get_set_ne (step (step s)).mem 22 21 0 (by decide)).trans hs2Q1
  have g3 (k : Nat) (h1 : 183 ≤ k) (h2 : k < 189) :
      (step (step (step s))).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    rw [hz2]
    have hne : UInt16.ofNat k ≠ 22 :=
      ofNat_ne k 22 (by omega) (by omega) (by omega)
    exact (Mem.get_set_ne (step (step s)).mem 22 (UInt16.ofNat k) 0 hne).trans (g2 k (by omega) h2)
  -- ZERO Q3 at 183
  have d0 : (step (step (step s))).mem.get (step (step (step s))).pc = 23 := by
    have hp3 : (step (step (step s))).pc = UInt16.ofNat 183 :=
      hs3pc.trans (rfl : (183 : Word) = UInt16.ofNat 183)
    rw [hp3]
    have hval : decChunk011[7]! = 23 := rfl
    exact (g3 183 (by decide) (by decide)).trans ((cell176 7 (by decide)).trans hval)
  have d1 : (step (step (step s))).mem.get ((step (step (step s))).pc + 1) = 23 := by
    have : (step (step (step s))).pc + 1 = (184 : Word) := by simp [hs3pc]
    rw [this, (rfl : (184 : Word) = UInt16.ofNat 184)]
    have hval : decChunk011[8]! = 23 := rfl
    exact (g3 184 (by decide) (by decide)).trans ((cell176 8 (by decide)).trans hval)
  have d2 : (step (step (step s))).mem.get ((step (step (step s))).pc + 2) =
      (step (step (step s))).pc + 3 := by
    have hp185 : (step (step (step s))).pc + 2 = (185 : Word) := by simp [hs3pc]
    have hp186 : (step (step (step s))).pc + 3 = (186 : Word) := by simp [hs3pc]
    rw [hp185, hp186, (rfl : (185 : Word) = UInt16.ofNat 185)]
    have hval : decChunk011[9]! = 186 := rfl
    have hv : (186 : Word) = UInt16.ofNat 186 := rfl
    exact (g3 185 (by decide) (by decide)).trans ((cell176 9 (by decide)).trans (hval.trans hv))
  have hpc3 : (step (step (step s))).pc.toNat < 32768 := by simp [hs3pc]
  have hz3 := step_ZERO (s := step (step (step s))) (x := 23) hs3h hpc3 d0 d1 d2 (by decide)
  have hs4pc : (step (step (step (step s)))).pc = 186 := by
    have : (step (step (step s))).pc + 3 = (186 : Word) := by simp [hs3pc]
    rw [hz3]; exact this
  have hs4h : (step (step (step (step s)))).halted = false := by rw [hz3]; exact hs3h
  have hs4Q3 : (step (step (step (step s)))).mem.get 23 = 0 := by
    rw [hz3]; exact Mem.get_set_eq (step (step (step s))).mem 23 0
  have hs4Q0 : (step (step (step (step s)))).mem.get 20 = 0 := by
    rw [hz3]; exact (Mem.get_set_ne (step (step (step s))).mem 23 20 0 (by decide)).trans hs3Q0
  have hs4Q1 : (step (step (step (step s)))).mem.get 21 = 0 := by
    rw [hz3]; exact (Mem.get_set_ne (step (step (step s))).mem 23 21 0 (by decide)).trans hs3Q1
  have hs4Q2 : (step (step (step (step s)))).mem.get 22 = 0 := by
    rw [hz3]; exact (Mem.get_set_ne (step (step (step s))).mem 23 22 0 (by decide)).trans hs3Q2
  have g4 (k : Nat) (h1 : 186 ≤ k) (h2 : k < 189) :
      (step (step (step (step s)))).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    rw [hz3]
    have hne : UInt16.ofNat k ≠ 23 :=
      ofNat_ne k 23 (by omega) (by omega) (by omega)
    exact (Mem.get_set_ne (step (step (step s))).mem 23 (UInt16.ofNat k) 0 hne).trans
      (g3 k (by omega) h2)
  -- ZERO Q4 at 186
  have e0 : (step (step (step (step s)))).mem.get (step (step (step (step s)))).pc = 24 := by
    have hp4 : (step (step (step (step s)))).pc = UInt16.ofNat 186 :=
      hs4pc.trans (rfl : (186 : Word) = UInt16.ofNat 186)
    rw [hp4]
    have hval : decChunk011[10]! = 24 := rfl
    exact (g4 186 (by decide) (by decide)).trans ((cell176 10 (by decide)).trans hval)
  have e1 : (step (step (step (step s)))).mem.get
      ((step (step (step (step s)))).pc + 1) = 24 := by
    have : (step (step (step (step s)))).pc + 1 = (187 : Word) := by simp [hs4pc]
    rw [this, (rfl : (187 : Word) = UInt16.ofNat 187)]
    have hval : decChunk011[11]! = 24 := rfl
    exact (g4 187 (by decide) (by decide)).trans ((cell176 11 (by decide)).trans hval)
  have e2 : (step (step (step (step s)))).mem.get
      ((step (step (step (step s)))).pc + 2) =
      (step (step (step (step s)))).pc + 3 := by
    have hp188 : (step (step (step (step s)))).pc + 2 = (188 : Word) := by simp [hs4pc]
    have hp189 : (step (step (step (step s)))).pc + 3 = (189 : Word) := by simp [hs4pc]
    rw [hp188, hp189, (rfl : (188 : Word) = UInt16.ofNat 188)]
    have hval : decChunk011[12]! = 189 := rfl
    have hv : (189 : Word) = UInt16.ofNat 189 := rfl
    exact (g4 188 (by decide) (by decide)).trans ((cell176 12 (by decide)).trans (hval.trans hv))
  have hpc4 : (step (step (step (step s)))).pc.toNat < 32768 := by simp [hs4pc]
  have hz4 :=
    step_ZERO (s := step (step (step (step s)))) (x := 24)
      hs4h hpc4 e0 e1 e2 (by decide)
  have hrun : s5 = step (step (step (step (step s)))) := by
    have h5 : runN s 5 = runN (step s) 4 := runN_succ_go s 4 hh hpc0
    have h4 : runN (step s) 4 = runN (step (step s)) 3 :=
      runN_succ_go (step s) 3 hs1h hpc1
    have h3 := runN_3_steps (step (step s)) hs2h hpc2 hs3h hpc3 hs4h hpc4
    exact h5.trans (h4.trans h3)
  have hs5pc : s5.pc = 189 := by
    have : (step (step (step (step s)))).pc + 3 = (189 : Word) := by simp [hs4pc]
    rw [hrun, hz4]; exact this
  have hs5h : s5.halted = false := by rw [hrun, hz4]; exact hs4h
  have hs5Q4 : s5.mem.get 24 = 0 := by
    rw [hrun, hz4]; exact Mem.get_set_eq (step (step (step (step s)))).mem 24 0
  have hs5Q0 : s5.mem.get 20 = 0 := by
    rw [hrun, hz4]
    exact (Mem.get_set_ne (step (step (step (step s)))).mem 24 20 0 (by decide)).trans hs4Q0
  have hs5Q1 : s5.mem.get 21 = 0 := by
    rw [hrun, hz4]
    exact (Mem.get_set_ne (step (step (step (step s)))).mem 24 21 0 (by decide)).trans hs4Q1
  have hs5Q2 : s5.mem.get 22 = 0 := by
    rw [hrun, hz4]
    exact (Mem.get_set_ne (step (step (step (step s)))).mem 24 22 0 (by decide)).trans hs4Q2
  have hs5Q3 : s5.mem.get 23 = 0 := by
    rw [hrun, hz4]
    exact (Mem.get_set_ne (step (step (step (step s)))).mem 24 23 0 (by decide)).trans hs4Q3
  have hpres : ∀ a, a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 24 →
      s5.mem.get a = s.mem.get a := by
    intro a h20 h21 h22 h23 h24
    rw [hrun, hz4, hz3, hz2, hz1, hz0]
    exact
      (Mem.get_set_ne _ 24 a 0 h24).trans
      ((Mem.get_set_ne _ 23 a 0 h23).trans
      ((Mem.get_set_ne _ 22 a 0 h22).trans
      ((Mem.get_set_ne _ 21 a 0 h21).trans
      (Mem.get_set_ne s.mem 20 a 0 h20))))
  exact ⟨hs5pc, hs5h, hs5Q0, hs5Q1, hs5Q2, hs5Q3, hs5Q4, hpres⟩


/-- One `P0_GE` body: `SUB C10000 N; INC Q0; JMP P0_LOOP` (5 steps).
Requires `N ≥ 10000` so the subtraction does not wrap. -/
theorem p0_ge_body {s : Machine}
    (hpc : s.pc = 255)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hC : s.mem.get 7 = 10000)
    (hNge : 10000 ≤ (s.mem.get 17).toNat)
    (hQ : (s.mem.get 20).toNat + 1 < 65536)
    (hcode : ∀ k : Nat, 255 ≤ k → k < 270 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    let n := s.mem.get 17
    let q := s.mem.get 20
    s5.pc = 189 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 17 = n - 10000 ∧
    s5.mem.get 20 = q + 1 ∧
    (s5.mem.get 17).toNat = n.toNat - 10000 ∧
    (s5.mem.get 20).toNat = q.toNat + 1 ∧
    (∀ a, a ≠ 17 → a ≠ 20 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5 n q
  have hp : s.pc = UInt16.ofNat 255 :=
    hpc.trans (rfl : (255 : Word) = UInt16.ofNat 255)
  have g (k : Nat) (h1 : 255 ≤ k) (h2 : k < 270) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have sub0 : s.mem.get s.pc = 7 := by
    rw [hp]
    have hval : decChunk015[15]! = 7 := rfl
    exact (g 255 (by decide) (by decide)).trans ((cell240 15 (by decide)).trans hval)
  have sub1 : s.mem.get (s.pc + 1) = 17 := by
    have : s.pc + 1 = (256 : Word) := by simp [hpc]
    rw [this, (rfl : (256 : Word) = UInt16.ofNat 256)]
    have hval : decChunk016[0]! = 17 := rfl
    exact (g 256 (by decide) (by decide)).trans ((cell256 0 (by decide)).trans hval)
  have sub2 : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp257 : s.pc + 2 = (257 : Word) := by simp [hpc]
    have hp258 : s.pc + 3 = (258 : Word) := by simp [hpc]
    rw [hp257, hp258, (rfl : (257 : Word) = UInt16.ofNat 257)]
    have hval : decChunk016[1]! = 258 := rfl
    have hv : (258 : Word) = UInt16.ofNat 258 := rfl
    exact (g 257 (by decide) (by decide)).trans ((cell256 1 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 7) (b := 17) hh hpc0 sub0 sub1 sub2 (by decide) (by decide)
  have hs1pc : (step s).pc = 258 := by
    have : s.pc + 3 = (258 : Word) := by simp [hpc]
    rw [hsub]; exact this
  have hs1h : (step s).halted = false := by rw [hsub]; exact hh
  have hs1N : (step s).mem.get 17 = n - 10000 := by
    rw [hsub]
    have : s.mem.get 17 - s.mem.get 7 = n - 10000 := by
      simp [n, hC]
    exact (Mem.get_set_eq s.mem 17 (s.mem.get 17 - s.mem.get 7)).trans this
  have hs1Z : (step s).mem.get 0 = 0 := by
    rw [hsub]
    exact (Mem.get_set_ne s.mem 17 0 (s.mem.get 17 - s.mem.get 7) (by decide)).trans hZ
  have hs1ONE : (step s).mem.get 3 = 1 := by
    rw [hsub]
    exact (Mem.get_set_ne s.mem 17 3 (s.mem.get 17 - s.mem.get 7) (by decide)).trans hONE
  have hs1Q : (step s).mem.get 20 = q := by
    rw [hsub]
    exact (Mem.get_set_ne s.mem 17 20 (s.mem.get 17 - s.mem.get 7) (by decide)).trans (rfl : s.mem.get 20 = q)
  have g1 (k : Nat) (h1 : 258 ≤ k) (h2 : k < 270) :
      (step s).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    rw [hsub]
    have hne : UInt16.ofNat k ≠ 17 :=
      ofNat_ne k 17 (by omega) (by omega) (by omega)
    exact (Mem.get_set_ne s.mem 17 (UInt16.ofNat k) (s.mem.get 17 - s.mem.get 7) hne).trans
      (g k (by omega) h2)
  -- INC Q0 at 258
  let s1 := step s
  have hp1 : s1.pc = UInt16.ofNat 258 :=
    hs1pc.trans (rfl : (258 : Word) = UInt16.ofNat 258)
  have poff (off : Nat) (hoff : off ≤ 9) :
      s1.pc + UInt16.ofNat off = UInt16.ofNat (258 + off) :=
    word_pc_off 258 off hp1 (by omega)
  have i0 : s1.mem.get s1.pc = 3 := by
    rw [hp1]
    have hval : decChunk016[2]! = 3 := rfl
    exact (g1 258 (by decide) (by decide)).trans ((cell256 2 (by decide)).trans hval)
  have i1 : s1.mem.get (s1.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk016[3]! = 0 := rfl
    exact (g1 259 (by decide) (by decide)).trans ((cell256 3 (by decide)).trans hval)
  have i2 : s1.mem.get (s1.pc + UInt16.ofNat 2) = s1.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk016[4]! = 261 := rfl
    have hv : (261 : Word) = UInt16.ofNat 261 := rfl
    exact (g1 260 (by decide) (by decide)).trans ((cell256 4 (by decide)).trans (hval.trans hv))
  have i3 : s1.mem.get (s1.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk016[5]! = 0 := rfl
    exact (g1 261 (by decide) (by decide)).trans ((cell256 5 (by decide)).trans hval)
  have i4 : s1.mem.get (s1.pc + UInt16.ofNat 4) = 20 := by
    rw [poff 4 (by decide)]
    have hval : decChunk016[6]! = 20 := rfl
    exact (g1 262 (by decide) (by decide)).trans ((cell256 6 (by decide)).trans hval)
  have i5 : s1.mem.get (s1.pc + UInt16.ofNat 5) = s1.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk016[7]! = 264 := rfl
    have hv : (264 : Word) = UInt16.ofNat 264 := rfl
    exact (g1 263 (by decide) (by decide)).trans ((cell256 7 (by decide)).trans (hval.trans hv))
  have i6 : s1.mem.get (s1.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk016[8]! = 0 := rfl
    exact (g1 264 (by decide) (by decide)).trans ((cell256 8 (by decide)).trans hval)
  have i7 : s1.mem.get (s1.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk016[9]! = 0 := rfl
    exact (g1 265 (by decide) (by decide)).trans ((cell256 9 (by decide)).trans hval)
  have i8 : s1.mem.get (s1.pc + UInt16.ofNat 8) = s1.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk016[10]! = 267 := rfl
    have hv : (267 : Word) = UInt16.ofNat 267 := rfl
    exact (g1 266 (by decide) (by decide)).trans ((cell256 10 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s1.pc + UInt16.ofNat i ≠ (20 : Word) := by
    intro i hi
    have : (20 : Word) = UInt16.ofNat 20 := rfl
    rw [this]
    exact pc_off_ne 258 i 20 hp1 (by omega) (by omega) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s1.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 258 i 0 hp1 (by omega) (by omega) (by omega)
  have hpc1b : s1.pc.toNat + 9 ≤ 32768 := by
    have : s1.pc = 258 := hs1pc
    simp [this]
  have hpc10 : 0 < s1.pc.toNat := by
    have : s1.pc = 258 := hs1pc
    simp [this]
  have hinc :=
    runN_ADD (s := s1) (src := 3) (dst := 20)
      hs1h hpc1b hpc10 hs1Z (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  let s4 := runN s1 3
  have hs4pc : s4.pc = 267 := by
    have hadd : s1.pc + UInt16.ofNat 9 = (267 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 267 = (267 : Word))
    exact hinc.1.trans hadd
  have hs4h : s4.halted = false := hinc.2.1
  have hs4Q : s4.mem.get 20 = q + 1 := by
    have : s1.mem.get 20 + s1.mem.get 3 = q + 1 := by
      rw [hs1Q, hs1ONE]
    exact hinc.2.2.1.trans this
  have hs4Z : s4.mem.get 0 = 0 := hinc.2.2.2.1
  have hpres4 := hinc.2.2.2.2
  have hs4N : s4.mem.get 17 = n - 10000 :=
    (hpres4 17 (by decide) (by decide)).trans hs1N
  have g4 (k : Nat) (h1 : 267 ≤ k) (h2 : k < 270) :
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres4 (UInt16.ofNat k) (ofNat_ne k 20 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans
      (g1 k (by omega) h2)
  -- JMP P0_LOOP at 267
  have j0 : s4.mem.get s4.pc = 0 := by
    have hp4 : s4.pc = UInt16.ofNat 267 :=
      hs4pc.trans (rfl : (267 : Word) = UInt16.ofNat 267)
    rw [hp4]
    have hval : decChunk016[11]! = 0 := rfl
    exact (g4 267 (by decide) (by decide)).trans ((cell256 11 (by decide)).trans hval)
  have j1 : s4.mem.get (s4.pc + 1) = 0 := by
    have : s4.pc + 1 = (268 : Word) := by simp [hs4pc]
    rw [this, (rfl : (268 : Word) = UInt16.ofNat 268)]
    have hval : decChunk016[12]! = 0 := rfl
    exact (g4 268 (by decide) (by decide)).trans ((cell256 12 (by decide)).trans hval)
  have j2 : s4.mem.get (s4.pc + 2) = 189 := by
    have : s4.pc + 2 = (269 : Word) := by simp [hs4pc]
    rw [this, (rfl : (269 : Word) = UInt16.ofNat 269)]
    have hval : decChunk016[13]! = 189 := rfl
    exact (g4 269 (by decide) (by decide)).trans ((cell256 13 (by decide)).trans hval)
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 189) hs4h hpc4 hs4Z j0 j1 j2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s1 4 := runN_succ_go s 4 hh hpc0
    have h4 : runN s1 4 = runN s4 1 := runN_add_eq s1 3 1 4 (by decide)
    have h1 := runN_one s4 hs4h hpc4
    exact h5.trans (h4.trans h1)
  have hs5pc : s5.pc = 189 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5N : s5.mem.get 17 = n - 10000 := by rw [hrun, hjmp]; exact hs4N
  have hs5Q : s5.mem.get 20 = q + 1 := by rw [hrun, hjmp]; exact hs4Q
  have hNton : (s5.mem.get 17).toNat = n.toNat - 10000 := by
    rw [hs5N]
    have hCton : (10000 : Word).toNat = 10000 := by
      decide
    have : n.toNat ≥ 10000 := hNge
    -- n is s.mem.get 17
    have hn : n = s.mem.get 17 := rfl
    simpa [hn, hCton] using word_sub_ge n (10000 : Word) (by simpa [hn, hCton] using hNge)
  have hQton : (s5.mem.get 20).toNat = q.toNat + 1 := by
    rw [hs5Q]
    exact word_add_one_toNat q hQ
  have hpres : ∀ a, a ≠ 17 → a ≠ 20 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha17 ha20 ha0
    have h1 : s5.mem.get a = s1.mem.get a := by
      rw [hrun, hjmp]
      exact hpres4 a ha20 ha0
    have h0 : s1.mem.get a = s.mem.get a := by
      rw [show s1 = step s from rfl, hsub]
      exact Mem.get_set_ne s.mem 17 a (s.mem.get 17 - s.mem.get 7) ha17
    exact h1.trans h0
  exact ⟨hs5pc, hs5h, hs5Z, hs5N, hs5Q, hNton, hQton, hpres⟩


/-- `N = 0` at `P0_LOOP`: the `P0_LE0` arm exits to `P0_DONE` in 10 steps
without changing `N` or `Q0`. -/
theorem p0_exit_zero {s : Machine}
    (hpc : s.pc = 189)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hN : s.mem.get 17 = 0)
    (hcode : ∀ k : Nat, 189 ≤ k → k < 270 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s10 := runN s 10
    s10.pc = 270 ∧
    s10.halted = false ∧
    s10.mem.get 17 = 0 ∧
    s10.mem.get 20 = s.mem.get 20 ∧
    s10.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a) := by
  intro s10
  have hp : s.pc = UInt16.ofNat 189 :=
    hpc.trans (rfl : (189 : Word) = UInt16.ofNat 189)
  have g (k : Nat) (h1 : 189 ≤ k) (h2 : k < 270) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (189 + off) :=
    word_pc_off 189 off hp (by omega)
  -- MOV N T at 189
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk011[13]! = 18 := rfl
    exact (g 189 (by decide) (by decide)).trans ((cell176 13 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk011[14]! = 18 := rfl
    exact (g 190 (by decide) (by decide)).trans ((cell176 14 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk011[15]! = 192 := rfl
    have hv : (192 : Word) = UInt16.ofNat 192 := rfl
    exact (g 191 (by decide) (by decide)).trans ((cell176 15 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 17 := by
    rw [poff 3 (by decide)]
    have hval : decChunk012[0]! = 17 := rfl
    exact (g 192 (by decide) (by decide)).trans ((cell192 0 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk012[1]! = 0 := rfl
    exact (g 193 (by decide) (by decide)).trans ((cell192 1 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk012[2]! = 195 := rfl
    have hv : (195 : Word) = UInt16.ofNat 195 := rfl
    exact (g 194 (by decide) (by decide)).trans ((cell192 2 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk012[3]! = 0 := rfl
    exact (g 195 (by decide) (by decide)).trans ((cell192 3 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk012[4]! = 18 := rfl
    exact (g 196 (by decide) (by decide)).trans ((cell192 4 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk012[5]! = 198 := rfl
    have hv : (198 : Word) = UInt16.ofNat 198 := rfl
    exact (g 197 (by decide) (by decide)).trans ((cell192 5 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk012[6]! = 0 := rfl
    exact (g 198 (by decide) (by decide)).trans ((cell192 6 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk012[7]! = 0 := rfl
    exact (g 199 (by decide) (by decide)).trans ((cell192 7 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk012[8]! = 201 := rfl
    have hv : (201 : Word) = UInt16.ofNat 201 := rfl
    exact (g 200 (by decide) (by decide)).trans ((cell192 8 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 189 i 18 hp (by omega) (by omega) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 189 i 0 hp (by omega) (by omega) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 17) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  let s4 := runN s 4
  have hs4pc : s4.pc = 201 := by
    have hadd : s.pc + UInt16.ofNat 12 = (201 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 201 = (201 : Word))
    exact hmov.1.trans hadd
  have hs4h : s4.halted = false := hmov.2.1
  have hT4 : s4.mem.get 18 = 0 := hmov.2.2.1.trans hN
  have hZ4 : s4.mem.get 0 = 0 := hmov.2.2.2.1
  have hpres4 := hmov.2.2.2.2.2
  have hN4 : s4.mem.get 17 = 0 := hmov.2.2.2.2.1.trans hN
  have g4 (k : Nat) (h1 : 201 ≤ k) (h2 : k < 270) :
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres4 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (g k (by omega) h2)
  -- JLEZ T P0_LE0, T = 0, taken
  have j0 : s4.mem.get s4.pc = 0 := by
    have hp4 : s4.pc = UInt16.ofNat 201 :=
      hs4pc.trans (rfl : (201 : Word) = UInt16.ofNat 201)
    rw [hp4]
    have hval : decChunk012[9]! = 0 := rfl
    exact (g4 201 (by decide) (by decide)).trans ((cell192 9 (by decide)).trans hval)
  have j1 : s4.mem.get (s4.pc + 1) = 18 := by
    have : s4.pc + 1 = (202 : Word) := by simp [hs4pc]
    rw [this, (rfl : (202 : Word) = UInt16.ofNat 202)]
    have hval : decChunk012[10]! = 18 := rfl
    exact (g4 202 (by decide) (by decide)).trans ((cell192 10 (by decide)).trans hval)
  have j2 : s4.mem.get (s4.pc + 2) = 207 := by
    have : s4.pc + 2 = (203 : Word) := by simp [hs4pc]
    rw [this, (rfl : (203 : Word) = UInt16.ofNat 203)]
    have hval : decChunk012[11]! = 207 := rfl
    exact (g4 203 (by decide) (by decide)).trans ((cell192 11 (by decide)).trans hval)
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez :=
    step_JLEZ (s := s4) (x := 18) (dest := 207)
      hs4h hpc4 hZ4 j0 j1 j2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = true := by
    have : le0 (s4.mem.get 18) = true := by
      rw [hT4]; exact le0_zero
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 207 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18 then (207 : Word)
          else s4.pc + 3) = (207 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hs5pc : (step s4).pc = 207 := by rw [hs5eq]
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by rw [hs5eq]; exact hZ4
  have hs5ONE : (step s4).mem.get 3 = 1 := by
    rw [hs5eq]; exact (hpres4 3 (by decide) (by decide)).trans hONE
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact hpres4 a ha18 ha0
  -- INC T at P0_LE0 (pc 207)
  let s5 := step s4
  have hp5 : s5.pc = UInt16.ofNat 207 :=
    hs5pc.trans (rfl : (207 : Word) = UInt16.ofNat 207)
  have poff5 (off : Nat) (hoff : off ≤ 9) :
      s5.pc + UInt16.ofNat off = UInt16.ofNat (207 + off) :=
    word_pc_off 207 off hp5 (by omega)
  have g5 (off : Nat) (hoff : off < 15) :
      s5.mem.get (UInt16.ofNat (207 + off)) = intfmtImage[207 + off]! := by
    have hcell := g (207 + off) (by omega) (by omega)
    exact (hpres5 (UInt16.ofNat (207 + off))
      (ofNat_ne (207 + off) 18 (by omega) (by omega) (by omega))
      (ofNat_ne (207 + off) 0 (by omega) (by omega) (by omega))).trans hcell
  have i0 : s5.mem.get s5.pc = 3 := by
    rw [hp5]
    have hval : decChunk012[15]! = 3 := rfl
    exact (g5 0 (by decide)).trans ((cell192 15 (by decide)).trans hval)
  have i1 : s5.mem.get (s5.pc + UInt16.ofNat 1) = 0 := by
    rw [poff5 1 (by decide)]
    have hval : decChunk013[0]! = 0 := rfl
    exact (g5 1 (by decide)).trans ((cell208 0 (by decide)).trans hval)
  have i2 : s5.mem.get (s5.pc + UInt16.ofNat 2) = s5.pc + UInt16.ofNat 3 := by
    rw [poff5 2 (by decide), poff5 3 (by decide)]
    have hval : decChunk013[1]! = 210 := rfl
    have hv : (210 : Word) = UInt16.ofNat 210 := rfl
    exact (g5 2 (by decide)).trans ((cell208 1 (by decide)).trans (hval.trans hv))
  have i3 : s5.mem.get (s5.pc + UInt16.ofNat 3) = 0 := by
    rw [poff5 3 (by decide)]
    have hval : decChunk013[2]! = 0 := rfl
    exact (g5 3 (by decide)).trans ((cell208 2 (by decide)).trans hval)
  have i4 : s5.mem.get (s5.pc + UInt16.ofNat 4) = 18 := by
    rw [poff5 4 (by decide)]
    have hval : decChunk013[3]! = 18 := rfl
    exact (g5 4 (by decide)).trans ((cell208 3 (by decide)).trans hval)
  have i5 : s5.mem.get (s5.pc + UInt16.ofNat 5) = s5.pc + UInt16.ofNat 6 := by
    rw [poff5 5 (by decide), poff5 6 (by decide)]
    have hval : decChunk013[4]! = 213 := rfl
    have hv : (213 : Word) = UInt16.ofNat 213 := rfl
    exact (g5 5 (by decide)).trans ((cell208 4 (by decide)).trans (hval.trans hv))
  have i6 : s5.mem.get (s5.pc + UInt16.ofNat 6) = 0 := by
    rw [poff5 6 (by decide)]
    have hval : decChunk013[5]! = 0 := rfl
    exact (g5 6 (by decide)).trans ((cell208 5 (by decide)).trans hval)
  have i7 : s5.mem.get (s5.pc + UInt16.ofNat 7) = 0 := by
    rw [poff5 7 (by decide)]
    have hval : decChunk013[6]! = 0 := rfl
    exact (g5 7 (by decide)).trans ((cell208 6 (by decide)).trans hval)
  have i8 : s5.mem.get (s5.pc + UInt16.ofNat 8) = s5.pc + UInt16.ofNat 9 := by
    rw [poff5 8 (by decide), poff5 9 (by decide)]
    have hval : decChunk013[7]! = 216 := rfl
    have hv : (216 : Word) = UInt16.ofNat 216 := rfl
    exact (g5 8 (by decide)).trans ((cell208 7 (by decide)).trans (hval.trans hv))
  have hcodeD5 : ∀ i : Nat, i < 9 → s5.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 207 i 18 hp5 (by omega) (by omega) (by omega)
  have hcodeZ5 : ∀ i : Nat, i < 9 → s5.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 207 i 0 hp5 (by omega) (by omega) (by omega)
  have hpc5b : s5.pc.toNat + 9 ≤ 32768 := by
    have : s5.pc = 207 := hs5pc
    simp [this]
  have hpc50 : 0 < s5.pc.toNat := by
    have : s5.pc = 207 := hs5pc
    simp [this]
  have hinc :=
    runN_ADD (s := s5) (src := 3) (dst := 18)
      hs5h hpc5b hpc50 hs5Z (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD5 hcodeZ5
  let s8 := runN s5 3
  have hs8pc : s8.pc = 216 := by
    have hadd : s5.pc + UInt16.ofNat 9 = (216 : Word) := by
      rw [poff5 9 (by decide)]
      exact (rfl : UInt16.ofNat 216 = (216 : Word))
    exact hinc.1.trans hadd
  have hs8h : s8.halted = false := hinc.2.1
  have hT8 : s8.mem.get 18 = 1 := by
    have hT5 : s5.mem.get 18 = 0 := by
      rw [show s5 = step s4 from rfl, hs5eq]; exact hT4
    have : s5.mem.get 18 + s5.mem.get 3 = (0 : Word) + 1 := by
      rw [hT5, hs5ONE]
    exact hinc.2.2.1.trans this
  have hZ8 : s8.mem.get 0 = 0 := hinc.2.2.2.1
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres5 a ha18 ha0)
  -- JLEZ T P0_GE, T = 1, not taken; JMP P0_DONE
  have k0 : s8.mem.get s8.pc = 0 := by
    have hp8 : s8.pc = UInt16.ofNat 216 :=
      hs8pc.trans (rfl : (216 : Word) = UInt16.ofNat 216)
    rw [hp8]
    have hval : decChunk013[8]! = 0 := rfl
    exact (hpres8 (UInt16.ofNat 216) (by decide) (by decide)).trans
      ((g 216 (by decide) (by decide)).trans ((cell208 8 (by decide)).trans hval))
  have k1 : s8.mem.get (s8.pc + 1) = 18 := by
    have : s8.pc + 1 = (217 : Word) := by simp [hs8pc]
    rw [this, (rfl : (217 : Word) = UInt16.ofNat 217)]
    have hval : decChunk013[9]! = 18 := rfl
    exact (hpres8 (UInt16.ofNat 217) (by decide) (by decide)).trans
      ((g 217 (by decide) (by decide)).trans ((cell208 9 (by decide)).trans hval))
  have k2 : s8.mem.get (s8.pc + 2) = 255 := by
    have : s8.pc + 2 = (218 : Word) := by simp [hs8pc]
    rw [this, (rfl : (218 : Word) = UInt16.ofNat 218)]
    have hval : decChunk013[10]! = 255 := rfl
    exact (hpres8 (UInt16.ofNat 218) (by decide) (by decide)).trans
      ((g 218 (by decide) (by decide)).trans ((cell208 10 (by decide)).trans hval))
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 255)
      hs8h hpc8 hZ8 k0 k1 k2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hT8]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := s8.pc + 3 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18 then (255 : Word)
          else s8.pc + 3) = s8.pc + 3 := by
      simp [hle2]
    rw [hjlez2, hif]
  have hs9pc : (step s8).pc = 219 := by
    have : s8.pc + 3 = (219 : Word) := by simp [hs8pc]
    rw [hs9eq]; exact this
  have hs9h : (step s8).halted = false := by rw [hs9eq]; exact hs8h
  have hs9Z : (step s8).mem.get 0 = 0 := by rw [hs9eq]; exact hZ8
  have jmp0 : (step s8).mem.get (step s8).pc = 0 := by
    have hp9 : (step s8).pc = UInt16.ofNat 219 :=
      hs9pc.trans (rfl : (219 : Word) = UInt16.ofNat 219)
    rw [hp9]
    have hmem : (step s8).mem.get (UInt16.ofNat 219) = s8.mem.get (UInt16.ofNat 219) := by
      rw [hs9eq]
    have hval : decChunk013[11]! = 0 := rfl
    exact hmem.trans ((hpres8 (UInt16.ofNat 219) (by decide) (by decide)).trans
      ((g 219 (by decide) (by decide)).trans ((cell208 11 (by decide)).trans hval)))
  have jmp1 : (step s8).mem.get ((step s8).pc + 1) = 0 := by
    have : (step s8).pc + 1 = (220 : Word) := by simp [hs9pc]
    rw [this, (rfl : (220 : Word) = UInt16.ofNat 220)]
    have hmem : (step s8).mem.get (UInt16.ofNat 220) = s8.mem.get (UInt16.ofNat 220) := by
      rw [hs9eq]
    have hval : decChunk013[12]! = 0 := rfl
    exact hmem.trans ((hpres8 (UInt16.ofNat 220) (by decide) (by decide)).trans
      ((g 220 (by decide) (by decide)).trans ((cell208 12 (by decide)).trans hval)))
  have jmp2 : (step s8).mem.get ((step s8).pc + 2) = 270 := by
    have : (step s8).pc + 2 = (221 : Word) := by simp [hs9pc]
    rw [this, (rfl : (221 : Word) = UInt16.ofNat 221)]
    have hmem : (step s8).mem.get (UInt16.ofNat 221) = s8.mem.get (UInt16.ofNat 221) := by
      rw [hs9eq]
    have hval : decChunk013[13]! = 270 := rfl
    exact hmem.trans ((hpres8 (UInt16.ofNat 221) (by decide) (by decide)).trans
      ((g 221 (by decide) (by decide)).trans ((cell208 13 (by decide)).trans hval)))
  have hpc9 : (step s8).pc.toNat < 32768 := by simp [hs9pc]
  have hjmp :=
    step_JMP (s := step s8) (dest := 270) hs9h hpc9 hs9Z jmp0 jmp1 jmp2
  have hrun : s10 = step (step s8) := by
    have h10 : runN s 10 = runN s4 6 := runN_add_eq s 4 6 10 (by decide)
    have h6 : runN s4 6 = runN s5 5 := runN_succ_go s4 5 hs4h hpc4
    have h5 : runN s5 5 = runN s8 2 := runN_add_eq s5 3 2 5 (by decide)
    have h2 := runN_2_steps s8 hs8h hpc8 hs9h hpc9
    exact h10.trans (h6.trans (h5.trans h2))
  have hmem : (step (step s8)).mem = s8.mem := by
    have h1 : (step s8).mem = s8.mem := by rw [hs9eq]
    have h2 : (step (step s8)).mem = (step s8).mem := by rw [hjmp]
    exact h2.trans h1
  have hs10pc : s10.pc = 270 := by rw [hrun, hjmp]
  have hs10h : s10.halted = false := by rw [hrun, hjmp]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by rw [hrun, hmem]; exact hZ8
  have hs10N : s10.mem.get 17 = 0 := by
    rw [hrun, hmem]; exact (hpres8 17 (by decide) (by decide)).trans hN
  have hs10Q : s10.mem.get 20 = s.mem.get 20 := by
    rw [hrun, hmem]; exact hpres8 20 (by decide) (by decide)
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hmem]
    exact hpres8 a ha18 ha0
  exact ⟨hs10pc, hs10h, hs10N, hs10Q, hs10Z, hpres⟩


/- Arithmetic helpers and the remaining P0_LOOP compare-diamond arms.
These are block lemmas, not end-to-end correctness. -/

/-- MOV N T at P0_LOOP (pc 189), 4 steps, exit pc 201. -/
theorem p0_loop_mov_N_T {s : Machine}
    (hpc : s.pc = 189)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 189 ≤ k → k < 201 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 201 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 17 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 17 = s.mem.get 17 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 189 :=
    hpc.trans (rfl : (189 : Word) = UInt16.ofNat 189)
  have g (k : Nat) (h1 : 189 ≤ k) (h2 : k < 201) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (189 + off) :=
    word_pc_off 189 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk011[13]! = 18 := rfl
    exact (g 189 (by decide) (by decide)).trans ((cell176 13 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk011[14]! = 18 := rfl
    exact (g 190 (by decide) (by decide)).trans ((cell176 14 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk011[15]! = 192 := rfl
    have hv : (192 : Word) = UInt16.ofNat 192 := rfl
    exact (g 191 (by decide) (by decide)).trans ((cell176 15 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 17 := by
    rw [poff 3 (by decide)]
    have hval : decChunk012[0]! = 17 := rfl
    exact (g 192 (by decide) (by decide)).trans ((cell192 0 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk012[1]! = 0 := rfl
    exact (g 193 (by decide) (by decide)).trans ((cell192 1 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk012[2]! = 195 := rfl
    have hv : (195 : Word) = UInt16.ofNat 195 := rfl
    exact (g 194 (by decide) (by decide)).trans ((cell192 2 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk012[3]! = 0 := rfl
    exact (g 195 (by decide) (by decide)).trans ((cell192 3 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk012[4]! = 18 := rfl
    exact (g 196 (by decide) (by decide)).trans ((cell192 4 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk012[5]! = 198 := rfl
    have hv : (198 : Word) = UInt16.ofNat 198 := rfl
    exact (g 197 (by decide) (by decide)).trans ((cell192 5 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk012[6]! = 0 := rfl
    exact (g 198 (by decide) (by decide)).trans ((cell192 6 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk012[7]! = 0 := rfl
    exact (g 199 (by decide) (by decide)).trans ((cell192 7 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk012[8]! = 201 := rfl
    have hv : (201 : Word) = UInt16.ofNat 201 := rfl
    exact (g 200 (by decide) (by decide)).trans ((cell192 8 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 189 i 18 hp (by omega) (by omega) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 189 i 0 hp (by omega) (by omega) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 17) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 201 := by
    have hadd : s.pc + UInt16.ofNat 12 = (201 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 201 = (201 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩


/-- MOV N T at P0_POS (pc 222), 4 steps, exit pc 234. -/
theorem p0_pos_mov_N_T {s : Machine}
    (hpc : s.pc = 222)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 222 ≤ k → k < 234 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 234 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 17 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 17 = s.mem.get 17 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 222 :=
    hpc.trans (rfl : (222 : Word) = UInt16.ofNat 222)
  have g (k : Nat) (h1 : 222 ≤ k) (h2 : k < 234) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (222 + off) :=
    word_pc_off 222 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk013[14]! = 18 := rfl
    exact (g 222 (by decide) (by decide)).trans ((cell208 14 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk013[15]! = 18 := rfl
    exact (g 223 (by decide) (by decide)).trans ((cell208 15 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk014[0]! = 225 := rfl
    have hv : (225 : Word) = UInt16.ofNat 225 := rfl
    exact (g 224 (by decide) (by decide)).trans ((cell224 0 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 17 := by
    rw [poff 3 (by decide)]
    have hval : decChunk014[1]! = 17 := rfl
    exact (g 225 (by decide) (by decide)).trans ((cell224 1 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk014[2]! = 0 := rfl
    exact (g 226 (by decide) (by decide)).trans ((cell224 2 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk014[3]! = 228 := rfl
    have hv : (228 : Word) = UInt16.ofNat 228 := rfl
    exact (g 227 (by decide) (by decide)).trans ((cell224 3 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk014[4]! = 0 := rfl
    exact (g 228 (by decide) (by decide)).trans ((cell224 4 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk014[5]! = 18 := rfl
    exact (g 229 (by decide) (by decide)).trans ((cell224 5 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk014[6]! = 231 := rfl
    have hv : (231 : Word) = UInt16.ofNat 231 := rfl
    exact (g 230 (by decide) (by decide)).trans ((cell224 6 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk014[7]! = 0 := rfl
    exact (g 231 (by decide) (by decide)).trans ((cell224 7 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk014[8]! = 0 := rfl
    exact (g 232 (by decide) (by decide)).trans ((cell224 8 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk014[9]! = 234 := rfl
    have hv : (234 : Word) = UInt16.ofNat 234 := rfl
    exact (g 233 (by decide) (by decide)).trans ((cell224 9 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 222 i 18 hp (by omega) (by omega) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 222 i 0 hp (by omega) (by omega) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 17) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 234 := by
    have hadd : s.pc + UInt16.ofNat 12 = (234 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 234 = (234 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩


/-- INC T at P0_LE0 (pc 207), 3 steps, exit pc 216. -/
theorem p0_le0_inc_T {s : Machine}
    (hpc : s.pc = 207)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 207 ≤ k → k < 216 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 216 ∧
    s3.halted = false ∧
    s3.mem.get 18 = s.mem.get 18 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp5 : s.pc = UInt16.ofNat 207 :=
    hpc.trans (rfl : (207 : Word) = UInt16.ofNat 207)
  have g (k : Nat) (h1 : 207 ≤ k) (h2 : k < 216) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff5 (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (207 + off) :=
    word_pc_off 207 off hp5 (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp5]
    have hval : decChunk012[15]! = 3 := rfl
    exact (g 207 (by decide) (by decide)).trans ((cell192 15 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff5 1 (by decide)]
    have hval : decChunk013[0]! = 0 := rfl
    exact (g 208 (by decide) (by decide)).trans ((cell208 0 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff5 2 (by decide), poff5 3 (by decide)]
    have hval : decChunk013[1]! = 210 := rfl
    have hv : (210 : Word) = UInt16.ofNat 210 := rfl
    exact (g 209 (by decide) (by decide)).trans ((cell208 1 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff5 3 (by decide)]
    have hval : decChunk013[2]! = 0 := rfl
    exact (g 210 (by decide) (by decide)).trans ((cell208 2 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 18 := by
    rw [poff5 4 (by decide)]
    have hval : decChunk013[3]! = 18 := rfl
    exact (g 211 (by decide) (by decide)).trans ((cell208 3 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff5 5 (by decide), poff5 6 (by decide)]
    have hval : decChunk013[4]! = 213 := rfl
    have hv : (213 : Word) = UInt16.ofNat 213 := rfl
    exact (g 212 (by decide) (by decide)).trans ((cell208 4 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff5 6 (by decide)]
    have hval : decChunk013[5]! = 0 := rfl
    exact (g 213 (by decide) (by decide)).trans ((cell208 5 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff5 7 (by decide)]
    have hval : decChunk013[6]! = 0 := rfl
    exact (g 214 (by decide) (by decide)).trans ((cell208 6 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff5 8 (by decide), poff5 9 (by decide)]
    have hval : decChunk013[7]! = 216 := rfl
    have hv : (216 : Word) = UInt16.ofNat 216 := rfl
    exact (g 215 (by decide) (by decide)).trans ((cell208 7 (by decide)).trans (hval.trans hv))
  have hcodeD5 : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 207 i 18 hp5 (by omega) (by omega) (by omega)
  have hcodeZ5 : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 207 i 0 hp5 (by omega) (by omega) (by omega)
  have hpc5b : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpc50 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 18)
      hh hpc5b hpc50 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD5 hcodeZ5
  have hs3pc : s3.pc = 216 := by
    have hadd : s.pc + UInt16.ofNat 9 = (216 : Word) := by
      rw [poff5 9 (by decide)]
      exact (rfl : UInt16.ofNat 216 = (216 : Word))
    exact hinc.1.trans hadd
  have hT : s3.mem.get 18 = s.mem.get 18 + 1 := by
    have : s.mem.get 18 + s.mem.get 3 = s.mem.get 18 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hT, hinc.2.2.2.1, hinc.2.2.2.2⟩


/-- INC T at P0_LE (pc 243), 3 steps, exit pc 252. -/
theorem p0_le_inc_T {s : Machine}
    (hpc : s.pc = 243)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 243 ≤ k → k < 252 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 252 ∧
    s3.halted = false ∧
    s3.mem.get 18 = s.mem.get 18 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp5 : s.pc = UInt16.ofNat 243 :=
    hpc.trans (rfl : (243 : Word) = UInt16.ofNat 243)
  have g (k : Nat) (h1 : 243 ≤ k) (h2 : k < 252) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff5 (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (243 + off) :=
    word_pc_off 243 off hp5 (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp5]
    have hval : decChunk015[3]! = 3 := rfl
    exact (g 243 (by decide) (by decide)).trans ((cell240 3 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff5 1 (by decide)]
    have hval : decChunk015[4]! = 0 := rfl
    exact (g 244 (by decide) (by decide)).trans ((cell240 4 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff5 2 (by decide), poff5 3 (by decide)]
    have hval : decChunk015[5]! = 246 := rfl
    have hv : (246 : Word) = UInt16.ofNat 246 := rfl
    exact (g 245 (by decide) (by decide)).trans ((cell240 5 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff5 3 (by decide)]
    have hval : decChunk015[6]! = 0 := rfl
    exact (g 246 (by decide) (by decide)).trans ((cell240 6 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 18 := by
    rw [poff5 4 (by decide)]
    have hval : decChunk015[7]! = 18 := rfl
    exact (g 247 (by decide) (by decide)).trans ((cell240 7 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff5 5 (by decide), poff5 6 (by decide)]
    have hval : decChunk015[8]! = 249 := rfl
    have hv : (249 : Word) = UInt16.ofNat 249 := rfl
    exact (g 248 (by decide) (by decide)).trans ((cell240 8 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff5 6 (by decide)]
    have hval : decChunk015[9]! = 0 := rfl
    exact (g 249 (by decide) (by decide)).trans ((cell240 9 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff5 7 (by decide)]
    have hval : decChunk015[10]! = 0 := rfl
    exact (g 250 (by decide) (by decide)).trans ((cell240 10 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff5 8 (by decide), poff5 9 (by decide)]
    have hval : decChunk015[11]! = 252 := rfl
    have hv : (252 : Word) = UInt16.ofNat 252 := rfl
    exact (g 251 (by decide) (by decide)).trans ((cell240 11 (by decide)).trans (hval.trans hv))
  have hcodeD5 : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 243 i 18 hp5 (by omega) (by omega) (by omega)
  have hcodeZ5 : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 243 i 0 hp5 (by omega) (by omega) (by omega)
  have hpc5b : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpc50 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 18)
      hh hpc5b hpc50 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD5 hcodeZ5
  have hs3pc : s3.pc = 252 := by
    have hadd : s.pc + UInt16.ofNat 9 = (252 : Word) := by
      rw [poff5 9 (by decide)]
      exact (rfl : UInt16.ofNat 252 = (252 : Word))
    exact hinc.1.trans hadd
  have hT : s3.mem.get 18 = s.mem.get 18 + 1 := by
    have : s.mem.get 18 + s.mem.get 3 = s.mem.get 18 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hT, hinc.2.2.2.1, hinc.2.2.2.2⟩


/-- JLEZ T P0_LE0 at pc 201. -/
theorem p0_enc_jlez_201 {s : Machine}
    (hpc : s.pc = 201)
    (hcode : ∀ k : Nat, 201 ≤ k → k < 201+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 207 := by
  have hp : s.pc = UInt16.ofNat 201 :=
    hpc.trans (rfl : (201 : Word) = UInt16.ofNat 201)
  have g (k : Nat) (h1 : 201 ≤ k) (h2 : k < 201+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have p0_enc_jlez_2010 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk012[9]! = 0 := rfl
    exact (g 201 (by decide) (by decide)).trans ((cell192 9 (by decide)).trans hval)
  have p0_enc_jlez_2011 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (202 : Word) := by simp [hpc]
    rw [this, (rfl : (202 : Word) = UInt16.ofNat 202)]
    have hval : decChunk012[10]! = 18 := rfl
    exact (g 202 (by decide) (by decide)).trans ((cell192 10 (by decide)).trans hval)
  have p0_enc_jlez_2012 : s.mem.get (s.pc + 2) = 207 := by
    have : s.pc + 2 = (203 : Word) := by simp [hpc]
    rw [this, (rfl : (203 : Word) = UInt16.ofNat 203)]
    have hval : decChunk012[11]! = 207 := rfl
    exact (g 203 (by decide) (by decide)).trans ((cell192 11 (by decide)).trans hval)
  exact ⟨p0_enc_jlez_2010, p0_enc_jlez_2011, p0_enc_jlez_2012⟩


/-- JMP P0_POS at pc 204. -/
theorem p0_enc_jmp_204 {s : Machine}
    (hpc : s.pc = 204)
    (hcode : ∀ k : Nat, 204 ≤ k → k < 204+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 222 := by
  have hp : s.pc = UInt16.ofNat 204 :=
    hpc.trans (rfl : (204 : Word) = UInt16.ofNat 204)
  have g (k : Nat) (h1 : 204 ≤ k) (h2 : k < 204+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have p0_enc_jmp_2040 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk012[12]! = 0 := rfl
    exact (g 204 (by decide) (by decide)).trans ((cell192 12 (by decide)).trans hval)
  have p0_enc_jmp_2041 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (205 : Word) := by simp [hpc]
    rw [this, (rfl : (205 : Word) = UInt16.ofNat 205)]
    have hval : decChunk012[13]! = 0 := rfl
    exact (g 205 (by decide) (by decide)).trans ((cell192 13 (by decide)).trans hval)
  have p0_enc_jmp_2042 : s.mem.get (s.pc + 2) = 222 := by
    have : s.pc + 2 = (206 : Word) := by simp [hpc]
    rw [this, (rfl : (206 : Word) = UInt16.ofNat 206)]
    have hval : decChunk012[14]! = 222 := rfl
    exact (g 206 (by decide) (by decide)).trans ((cell192 14 (by decide)).trans hval)
  exact ⟨p0_enc_jmp_2040, p0_enc_jmp_2041, p0_enc_jmp_2042⟩


/-- JLEZ T P0_GE at pc 216. -/
theorem p0_enc_jlez_216 {s : Machine}
    (hpc : s.pc = 216)
    (hcode : ∀ k : Nat, 216 ≤ k → k < 216+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 255 := by
  have hp : s.pc = UInt16.ofNat 216 :=
    hpc.trans (rfl : (216 : Word) = UInt16.ofNat 216)
  have g (k : Nat) (h1 : 216 ≤ k) (h2 : k < 216+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have p0_enc_jlez_2160 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk013[8]! = 0 := rfl
    exact (g 216 (by decide) (by decide)).trans ((cell208 8 (by decide)).trans hval)
  have p0_enc_jlez_2161 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (217 : Word) := by simp [hpc]
    rw [this, (rfl : (217 : Word) = UInt16.ofNat 217)]
    have hval : decChunk013[9]! = 18 := rfl
    exact (g 217 (by decide) (by decide)).trans ((cell208 9 (by decide)).trans hval)
  have p0_enc_jlez_2162 : s.mem.get (s.pc + 2) = 255 := by
    have : s.pc + 2 = (218 : Word) := by simp [hpc]
    rw [this, (rfl : (218 : Word) = UInt16.ofNat 218)]
    have hval : decChunk013[10]! = 255 := rfl
    exact (g 218 (by decide) (by decide)).trans ((cell208 10 (by decide)).trans hval)
  exact ⟨p0_enc_jlez_2160, p0_enc_jlez_2161, p0_enc_jlez_2162⟩


/-- JMP P0_DONE at pc 219. -/
theorem p0_enc_jmp_219 {s : Machine}
    (hpc : s.pc = 219)
    (hcode : ∀ k : Nat, 219 ≤ k → k < 219+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 270 := by
  have hp : s.pc = UInt16.ofNat 219 :=
    hpc.trans (rfl : (219 : Word) = UInt16.ofNat 219)
  have g (k : Nat) (h1 : 219 ≤ k) (h2 : k < 219+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have p0_enc_jmp_2190 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk013[11]! = 0 := rfl
    exact (g 219 (by decide) (by decide)).trans ((cell208 11 (by decide)).trans hval)
  have p0_enc_jmp_2191 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (220 : Word) := by simp [hpc]
    rw [this, (rfl : (220 : Word) = UInt16.ofNat 220)]
    have hval : decChunk013[12]! = 0 := rfl
    exact (g 220 (by decide) (by decide)).trans ((cell208 12 (by decide)).trans hval)
  have p0_enc_jmp_2192 : s.mem.get (s.pc + 2) = 270 := by
    have : s.pc + 2 = (221 : Word) := by simp [hpc]
    rw [this, (rfl : (221 : Word) = UInt16.ofNat 221)]
    have hval : decChunk013[13]! = 270 := rfl
    exact (g 221 (by decide) (by decide)).trans ((cell208 13 (by decide)).trans hval)
  exact ⟨p0_enc_jmp_2190, p0_enc_jmp_2191, p0_enc_jmp_2192⟩


/-- SUB C10000 T at pc 234. -/
theorem p0_enc_sub_234 {s : Machine}
    (hpc : s.pc = 234)
    (hcode : ∀ k : Nat, 234 ≤ k → k < 234+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 7 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 237 := by
  have hp : s.pc = UInt16.ofNat 234 :=
    hpc.trans (rfl : (234 : Word) = UInt16.ofNat 234)
  have g (k : Nat) (h1 : 234 ≤ k) (h2 : k < 234+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have p0_enc_sub_2340 : s.mem.get s.pc = 7 := by
    rw [hp]
    have hval : decChunk014[10]! = 7 := rfl
    exact (g 234 (by decide) (by decide)).trans ((cell224 10 (by decide)).trans hval)
  have p0_enc_sub_2341 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (235 : Word) := by simp [hpc]
    rw [this, (rfl : (235 : Word) = UInt16.ofNat 235)]
    have hval : decChunk014[11]! = 18 := rfl
    exact (g 235 (by decide) (by decide)).trans ((cell224 11 (by decide)).trans hval)
  have p0_enc_sub_2342 : s.mem.get (s.pc + 2) = 237 := by
    have : s.pc + 2 = (236 : Word) := by simp [hpc]
    rw [this, (rfl : (236 : Word) = UInt16.ofNat 236)]
    have hval : decChunk014[12]! = 237 := rfl
    exact (g 236 (by decide) (by decide)).trans ((cell224 12 (by decide)).trans hval)
  exact ⟨p0_enc_sub_2340, p0_enc_sub_2341, p0_enc_sub_2342⟩


/-- JLEZ T P0_LE at pc 237. -/
theorem p0_enc_jlez_237 {s : Machine}
    (hpc : s.pc = 237)
    (hcode : ∀ k : Nat, 237 ≤ k → k < 237+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 243 := by
  have hp : s.pc = UInt16.ofNat 237 :=
    hpc.trans (rfl : (237 : Word) = UInt16.ofNat 237)
  have g (k : Nat) (h1 : 237 ≤ k) (h2 : k < 237+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have p0_enc_jlez_2370 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk014[13]! = 0 := rfl
    exact (g 237 (by decide) (by decide)).trans ((cell224 13 (by decide)).trans hval)
  have p0_enc_jlez_2371 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (238 : Word) := by simp [hpc]
    rw [this, (rfl : (238 : Word) = UInt16.ofNat 238)]
    have hval : decChunk014[14]! = 18 := rfl
    exact (g 238 (by decide) (by decide)).trans ((cell224 14 (by decide)).trans hval)
  have p0_enc_jlez_2372 : s.mem.get (s.pc + 2) = 243 := by
    have : s.pc + 2 = (239 : Word) := by simp [hpc]
    rw [this, (rfl : (239 : Word) = UInt16.ofNat 239)]
    have hval : decChunk014[15]! = 243 := rfl
    exact (g 239 (by decide) (by decide)).trans ((cell224 15 (by decide)).trans hval)
  exact ⟨p0_enc_jlez_2370, p0_enc_jlez_2371, p0_enc_jlez_2372⟩


/-- JMP P0_GE at pc 240. -/
theorem p0_enc_jmp_240 {s : Machine}
    (hpc : s.pc = 240)
    (hcode : ∀ k : Nat, 240 ≤ k → k < 240+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 255 := by
  have hp : s.pc = UInt16.ofNat 240 :=
    hpc.trans (rfl : (240 : Word) = UInt16.ofNat 240)
  have g (k : Nat) (h1 : 240 ≤ k) (h2 : k < 240+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have p0_enc_jmp_2400 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk015[0]! = 0 := rfl
    exact (g 240 (by decide) (by decide)).trans ((cell240 0 (by decide)).trans hval)
  have p0_enc_jmp_2401 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (241 : Word) := by simp [hpc]
    rw [this, (rfl : (241 : Word) = UInt16.ofNat 241)]
    have hval : decChunk015[1]! = 0 := rfl
    exact (g 241 (by decide) (by decide)).trans ((cell240 1 (by decide)).trans hval)
  have p0_enc_jmp_2402 : s.mem.get (s.pc + 2) = 255 := by
    have : s.pc + 2 = (242 : Word) := by simp [hpc]
    rw [this, (rfl : (242 : Word) = UInt16.ofNat 242)]
    have hval : decChunk015[2]! = 255 := rfl
    exact (g 242 (by decide) (by decide)).trans ((cell240 2 (by decide)).trans hval)
  exact ⟨p0_enc_jmp_2400, p0_enc_jmp_2401, p0_enc_jmp_2402⟩


/-- JLEZ T P0_DONE at pc 252. -/
theorem p0_enc_jlez_252 {s : Machine}
    (hpc : s.pc = 252)
    (hcode : ∀ k : Nat, 252 ≤ k → k < 252+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 270 := by
  have hp : s.pc = UInt16.ofNat 252 :=
    hpc.trans (rfl : (252 : Word) = UInt16.ofNat 252)
  have g (k : Nat) (h1 : 252 ≤ k) (h2 : k < 252+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have p0_enc_jlez_2520 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk015[12]! = 0 := rfl
    exact (g 252 (by decide) (by decide)).trans ((cell240 12 (by decide)).trans hval)
  have p0_enc_jlez_2521 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (253 : Word) := by simp [hpc]
    rw [this, (rfl : (253 : Word) = UInt16.ofNat 253)]
    have hval : decChunk015[13]! = 18 := rfl
    exact (g 253 (by decide) (by decide)).trans ((cell240 13 (by decide)).trans hval)
  have p0_enc_jlez_2522 : s.mem.get (s.pc + 2) = 270 := by
    have : s.pc + 2 = (254 : Word) := by simp [hpc]
    rw [this, (rfl : (254 : Word) = UInt16.ofNat 254)]
    have hval : decChunk015[14]! = 270 := rfl
    exact (g 254 (by decide) (by decide)).trans ((cell240 14 (by decide)).trans hval)
  exact ⟨p0_enc_jlez_2520, p0_enc_jlez_2521, p0_enc_jlez_2522⟩


/-- `N` has the high bit set (`N.toNat ≥ 32768`) at `P0_LOOP`: the
`P0_LE0` arm reaches `P0_GE` in 9 steps without changing `N` or `Q0`. -/
theorem p0_to_ge_hi {s : Machine}
    (hpc : s.pc = 189)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hN : 32768 ≤ (s.mem.get 17).toNat)
    (hcode : ∀ k : Nat, 189 ≤ k → k < 270 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s9 := runN s 9
    s9.pc = 255 ∧
    s9.halted = false ∧
    s9.mem.get 17 = s.mem.get 17 ∧
    s9.mem.get 20 = s.mem.get 20 ∧
    s9.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a) := by
  intro s9
  have hmov :=
    p0_loop_mov_N_T (s := s) hpc hh hZ (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 201 := hmov.1
  have hs4h := hmov.2.1
  have hT4 : s4.mem.get 18 = s.mem.get 17 := hmov.2.2.1
  have hZ4 := hmov.2.2.2.1
  have hpres4 := hmov.2.2.2.2.2
  have g4 (k : Nat) (h1 : 201 ≤ k) (h2 : k < 270) :
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres4 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) h2)
  have enc := p0_enc_jlez_201 (s := s4) hs4pc (fun k h1 h2 => g4 k h1 (by omega))
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez :=
    step_JLEZ (s := s4) (x := 18) (dest := 207)
      hs4h hpc4 hZ4 enc.1 enc.2.1 enc.2.2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = true := by
    have : le0 (s4.mem.get 18) = true := by
      rw [hT4]; exact le0_hi hN
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 207 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18 then (207 : Word)
          else s4.pc + 3) = (207 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hs5pc : (step s4).pc = 207 := by rw [hs5eq]
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by rw [hs5eq]; exact hZ4
  have hs5ONE : (step s4).mem.get 3 = 1 := by
    rw [hs5eq]; exact (hpres4 3 (by decide) (by decide)).trans hONE
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact hpres4 a ha18 ha0
  have hT5 : (step s4).mem.get 18 = s.mem.get 17 := by
    rw [hs5eq]; exact hT4
  let s5 := step s4
  have g5 (k : Nat) (h1 : 207 ≤ k) (h2 : k < 216) :
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    have hne18 : UInt16.ofNat k ≠ 18 := ofNat_ne k 18 (by omega) (by omega) (by omega)
    have hne0 : UInt16.ofNat k ≠ 0 := ofNat_ne k 0 (by omega) (by omega) (by omega)
    exact (hpres5 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have hinc :=
    p0_le0_inc_T (s := s5) hs5pc hs5h hs5Z hs5ONE g5
  let s8 := runN s5 3
  have hs8pc : s8.pc = 216 := hinc.1
  have hs8h := hinc.2.1
  have hT8 : s8.mem.get 18 = s.mem.get 17 + 1 := hinc.2.2.1.trans (by rw [hT5])
  have hZ8 := hinc.2.2.2.1
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres5 a ha18 ha0)
  have g8 (k : Nat) (h1 : 216 ≤ k) (h2 : k < 219) :
      s8.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres8 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have enc2 := p0_enc_jlez_216 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 255)
      hs8h hpc8 hZ8 enc2.1 enc2.2.1 enc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = true := by
    have : le0 (s8.mem.get 18) = true := by
      rw [hT8]
      by_cases hmax : (s.mem.get 17).toNat = 65535
      · have hw : s.mem.get 17 + 1 = 0 := word_add_one_wrap (s.mem.get 17) hmax
        rw [hw]; exact le0_zero
      · have hbound : (s.mem.get 17).toNat + 1 < 65536 := by
          have hlt := UInt16.toNat_lt_size (s.mem.get 17)
          have : UInt16.size = 65536 := rfl
          omega
        have hton := word_add_one_toNat (s.mem.get 17) hbound
        have hhi : 32768 ≤ (s.mem.get 17 + 1).toNat := by
          rw [hton]; omega
        exact le0_hi hhi
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 255 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18 then (255 : Word)
          else s8.pc + 3) = (255 : Word) := by
      simp [hle2]
    rw [hjlez2, hif]
  have hrun : s9 = step s8 := by
    have h9 : runN s 9 = runN s4 5 := runN_add_eq s 4 5 9 (by decide)
    have h5 : runN s4 5 = runN s5 4 := runN_succ_go s4 4 hs4h hpc4
    have h4 : runN s5 4 = runN s8 1 := runN_add_eq s5 3 1 4 (by decide)
    have h1 := runN_one s8 hs8h hpc8
    exact h9.trans (h5.trans (h4.trans h1))
  have hs9pc : s9.pc = 255 := by rw [hrun, hs9eq]
  have hs9h : s9.halted = false := by rw [hrun, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by rw [hrun, hs9eq]; exact hZ8
  have hs9N : s9.mem.get 17 = s.mem.get 17 := by
    rw [hrun, hs9eq]; exact hpres8 17 (by decide) (by decide)
  have hs9Q : s9.mem.get 20 = s.mem.get 20 := by
    rw [hrun, hs9eq]; exact hpres8 20 (by decide) (by decide)
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hs9eq]
    exact hpres8 a ha18 ha0
  exact ⟨hs9pc, hs9h, hs9N, hs9Q, hs9Z, hpres⟩

/-- From `P0_LOOP`, a positive `N` with a clear high bit (`0 < N < 32768`)
takes the fall-through to `P0_POS` in 6 steps. `N` is unchanged. -/
theorem p0_goto_pos {s : Machine}
    (hpc : s.pc = 189)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hN0 : 0 < (s.mem.get 17).toNat)
    (hNhi : (s.mem.get 17).toNat < 32768)
    (hcode : ∀ k : Nat, 189 ≤ k → k < 270 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s6 := runN s 6
    s6.pc = 222 ∧
    s6.halted = false ∧
    s6.mem.get 18 = s.mem.get 17 ∧
    s6.mem.get 17 = s.mem.get 17 ∧
    s6.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a) := by
  intro s6
  have hmov :=
    p0_loop_mov_N_T (s := s) hpc hh hZ (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 201 := hmov.1
  have hs4h := hmov.2.1
  have hT4 : s4.mem.get 18 = s.mem.get 17 := hmov.2.2.1
  have hZ4 := hmov.2.2.2.1
  have hpres4 := hmov.2.2.2.2.2
  have g4 (k : Nat) (h1 : 201 ≤ k) (h2 : k < 207) :
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres4 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have enc := p0_enc_jlez_201 (s := s4) hs4pc (fun k h1 h2 => g4 k h1 (by omega))
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez :=
    step_JLEZ (s := s4) (x := 18) (dest := 207)
      hs4h hpc4 hZ4 enc.1 enc.2.1 enc.2.2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hT4]; exact le0_pos hN0 hNhi
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := s4.pc + 3 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18 then (207 : Word)
          else s4.pc + 3) = s4.pc + 3 := by
      simp [hle]
    rw [hjlez, hif]
  have hs5pc : (step s4).pc = 204 := by
    have : s4.pc + 3 = (204 : Word) := by simp [hs4pc]
    rw [hs5eq]; exact this
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by rw [hs5eq]; exact hZ4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact hpres4 a ha18 ha0
  have g5 (k : Nat) (h1 : 204 ≤ k) (h2 : k < 207) :
      (step s4).mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres5 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have encJ := p0_enc_jmp_204 (s := step s4) hs5pc g5
  have hpc5 : (step s4).pc.toNat < 32768 := by simp [hs5pc]
  have hjmp :=
    step_JMP (s := step s4) (dest := 222) hs5h hpc5 hs5Z encJ.1 encJ.2.1 encJ.2.2
  have hrun : s6 = step (step s4) := by
    have h6 : runN s 6 = runN s4 2 := runN_add_eq s 4 2 6 (by decide)
    have h2 := runN_2_steps s4 hs4h hpc4 hs5h hpc5
    exact h6.trans h2
  have hs6pc : s6.pc = 222 := by rw [hrun, hjmp]
  have hs6h : s6.halted = false := by rw [hrun, hjmp]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have hmem : (step (step s4)).mem = (step s4).mem := by rw [hjmp]
    rw [hrun, hmem, hs5eq]; exact hZ4
  have hs6T : s6.mem.get 18 = s.mem.get 17 := by
    have hmem : (step (step s4)).mem = (step s4).mem := by rw [hjmp]
    rw [hrun, hmem, hs5eq]; exact hT4
  have hs6N : s6.mem.get 17 = s.mem.get 17 := by
    have hmem : (step (step s4)).mem = (step s4).mem := by rw [hjmp]
    rw [hrun, hmem, hs5eq]; exact hmov.2.2.2.2.1
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have hmem : (step (step s4)).mem = (step s4).mem := by rw [hjmp]
    rw [hrun, hmem]
    exact hpres5 a ha18 ha0
  exact ⟨hs6pc, hs6h, hs6T, hs6N, hs6Z, hpres⟩

/-- `SUB C10000 T` at pc 234 (fall through to 237). -/
theorem p0_sub_C10000_T {s : Machine}
    (hpc : s.pc = 234)
    (hh : s.halted = false)
    (hC : s.mem.get 7 = 10000)
    (hcode : ∀ k : Nat, 234 ≤ k → k < 237 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - 10000)
        pc := 237 } := by
  have enc := p0_enc_sub_234 (s := s) hpc hcode
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have : s.pc + 3 = (237 : Word) := by simp [hpc]
    exact enc.2.2.trans this.symm
  have hsub :=
    step_SUB (s := s) (a := 7) (b := 18) hh hpc0 enc.1 enc.2.1 hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (237 : Word) := by simp [hpc]
  have hmem : s.mem.get 18 - s.mem.get 7 = s.mem.get 18 - 10000 := by
    simp [hC]
  rw [hsub, hpc', hmem]

/-- `0 < N < 10000` at `P0_LOOP`: the `P0_POS`/`P0_LE` arm exits to
`P0_DONE` in 16 steps without changing `N` or `Q0`. -/
theorem p0_exit_small {s : Machine}
    (hpc : s.pc = 189)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hC : s.mem.get 7 = 10000)
    (hN0 : 0 < (s.mem.get 17).toNat)
    (hN : (s.mem.get 17).toNat < 10000)
    (hcode : ∀ k : Nat, 189 ≤ k → k < 270 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s16 := runN s 16
    s16.pc = 270 ∧
    s16.halted = false ∧
    s16.mem.get 17 = s.mem.get 17 ∧
    s16.mem.get 20 = s.mem.get 20 ∧
    s16.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a) := by
  intro s16
  have hNhi : (s.mem.get 17).toNat < 32768 := Nat.lt_trans hN (by decide)
  have hgo := p0_goto_pos (s := s) hpc hh hZ hN0 hNhi hcode
  let s6 := runN s 6
  have hs6pc : s6.pc = 222 := hgo.1
  have hs6h := hgo.2.1
  have hT6 : s6.mem.get 18 = s.mem.get 17 := hgo.2.2.1
  have hZ6 := hgo.2.2.2.2.1
  have hpres6 := hgo.2.2.2.2.2
  have hs6ONE : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have hs6C : s6.mem.get 7 = 10000 := (hpres6 7 (by decide) (by decide)).trans hC
  have g6 (k : Nat) (h1 : 222 ≤ k) (h2 : k < 234) :
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres6 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have hmov := p0_pos_mov_N_T (s := s6) hs6pc hs6h hZ6 g6
  let s10 := runN s6 4
  have hs10pc : s10.pc = 234 := hmov.1
  have hs10h := hmov.2.1
  have hT10 : s10.mem.get 18 = s.mem.get 17 :=
    hmov.2.2.1.trans (hgo.2.2.2.1)
  have hZ10 := hmov.2.2.2.1
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hmov.2.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hs10C : s10.mem.get 7 = 10000 := (hpres10 7 (by decide) (by decide)).trans hC
  have hs10ONE : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have g10 (k : Nat) (h1 : 234 ≤ k) (h2 : k < 237) :
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres10 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have hsub := p0_sub_C10000_T (s := s10) hs10pc hs10h hs10C g10
  have hs11pc : (step s10).pc = 237 := by rw [hsub]
  have hs11h : (step s10).halted = false := by rw [hsub]; exact hs10h
  have hs11Z : (step s10).mem.get 0 = 0 := by
    rw [hsub]
    exact (Mem.get_set_ne s10.mem 18 0 (s10.mem.get 18 - 10000) (by decide)).trans hZ10
  have hT11 : (step s10).mem.get 18 = s.mem.get 17 - 10000 := by
    rw [hsub]
    exact (Mem.get_set_eq s10.mem 18 (s10.mem.get 18 - 10000)).trans
      (by rw [hT10])
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → (step s10).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hsub]
    exact (Mem.get_set_ne s10.mem 18 a (s10.mem.get 18 - 10000) ha18).trans
      (hpres10 a ha18 ha0)
  have hs11ONE : (step s10).mem.get 3 = 1 :=
    (hpres11 3 (by decide) (by decide)).trans hONE
  have g11 (k : Nat) (h1 : 237 ≤ k) (h2 : k < 240) :
      (step s10).mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres11 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have enc := p0_enc_jlez_237 (s := step s10) hs11pc g11
  have hpc11 : (step s10).pc.toNat < 32768 := by simp [hs11pc]
  have hjlez :=
    step_JLEZ (s := step s10) (x := 18) (dest := 243)
      hs11h hpc11 hs11Z enc.1 enc.2.1 enc.2.2 (by decide)
  have hCton : (10000 : Word).toNat = 10000 := rfl
  have hTwrap : 32768 ≤ (s.mem.get 17 - 10000).toNat := by
    have := word_sub_lt (s.mem.get 17) (10000 : Word) (by simpa [hCton] using hN)
    omega
  have hle : ( (step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18) = true := by
    have : le0 ((step s10).mem.get 18) = true := by
      rw [hT11]; exact le0_hi hTwrap
    simpa [le0] using this
  have hs12eq : step (step s10) = { step s10 with pc := 243 } := by
    have hif :
        (if (step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18 then (243 : Word)
          else (step s10).pc + 3) = (243 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hs12pc : (step (step s10)).pc = 243 := by rw [hs12eq]
  have hs12h : (step (step s10)).halted = false := by rw [hs12eq]; exact hs11h
  have hs12Z : (step (step s10)).mem.get 0 = 0 := by rw [hs12eq]; exact hs11Z
  have hs12ONE : (step (step s10)).mem.get 3 = 1 := by
    rw [hs12eq]; exact hs11ONE
  have hT12 : (step (step s10)).mem.get 18 = s.mem.get 17 - 10000 := by
    rw [hs12eq]; exact hT11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → (step (step s10)).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs12eq]
    exact hpres11 a ha18 ha0
  let s12 := step (step s10)
  have g12 (k : Nat) (h1 : 243 ≤ k) (h2 : k < 252) :
      s12.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres12 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have hinc := p0_le_inc_T (s := s12) hs12pc hs12h hs12Z hs12ONE g12
  let s15 := runN s12 3
  have hs15pc : s15.pc = 252 := hinc.1
  have hs15h := hinc.2.1
  have hT15 : s15.mem.get 18 = (s.mem.get 17 - 10000) + 1 :=
    hinc.2.2.1.trans (by rw [hT12])
  have hZ15 := hinc.2.2.2.1
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres12 a ha18 ha0)
  have g15 (k : Nat) (h1 : 252 ≤ k) (h2 : k < 255) :
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres15 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have enc2 := p0_enc_jlez_252 (s := s15) hs15pc g15
  have hpc15 : s15.pc.toNat < 32768 := by simp [hs15pc]
  have hjlez2 :=
    step_JLEZ (s := s15) (x := 18) (dest := 270)
      hs15h hpc15 hZ15 enc2.1 enc2.2.1 enc2.2.2 (by decide)
  have hle2 : (s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18) = true := by
    have : le0 (s15.mem.get 18) = true := by
      rw [hT15]
      by_cases hmax : (s.mem.get 17 - 10000).toNat = 65535
      · have hw : (s.mem.get 17 - 10000) + 1 = 0 :=
          word_add_one_wrap (s.mem.get 17 - 10000) hmax
        rw [hw]; exact le0_zero
      · have hbound : (s.mem.get 17 - 10000).toNat + 1 < 65536 := by
          have hlt := UInt16.toNat_lt_size (s.mem.get 17 - 10000)
          have : UInt16.size = 65536 := rfl
          omega
        have hton := word_add_one_toNat (s.mem.get 17 - 10000) hbound
        have hhi : 32768 ≤ ((s.mem.get 17 - 10000) + 1).toNat := by
          rw [hton]
          have hx := word_sub_lt (s.mem.get 17) (10000 : Word)
            (by simpa [hCton] using hN)
          omega
        exact le0_hi hhi
    simpa [le0] using this
  have hs16eq : step s15 = { s15 with pc := 270 } := by
    have hif :
        (if s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18 then (270 : Word)
          else s15.pc + 3) = (270 : Word) := by
      simp [hle2]
    rw [hjlez2, hif]
  have hrun : s16 = step s15 := by
    have h16 : runN s 16 = runN s6 10 := runN_add_eq s 6 10 16 (by decide)
    have h10 : runN s6 10 = runN s10 6 := runN_add_eq s6 4 6 10 (by decide)
    have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
    have h6 : runN s10 6 = runN (step s10) 5 := runN_succ_go s10 5 hs10h hpc10
    have h5 : runN (step s10) 5 = runN s12 4 := runN_succ_go (step s10) 4 hs11h hpc11
    have h4 : runN s12 4 = runN s15 1 := runN_add_eq s12 3 1 4 (by decide)
    have h1 := runN_one s15 hs15h hpc15
    exact h16.trans (h10.trans (h6.trans (h5.trans (h4.trans h1))))
  have hs16pc : s16.pc = 270 := by rw [hrun, hs16eq]
  have hs16h : s16.halted = false := by rw [hrun, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by rw [hrun, hs16eq]; exact hZ15
  have hs16N : s16.mem.get 17 = s.mem.get 17 := by
    rw [hrun, hs16eq]; exact hpres15 17 (by decide) (by decide)
  have hs16Q : s16.mem.get 20 = s.mem.get 20 := by
    rw [hrun, hs16eq]; exact hpres15 20 (by decide) (by decide)
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hs16eq]
    exact hpres15 a ha18 ha0
  exact ⟨hs16pc, hs16h, hs16N, hs16Q, hs16Z, hpres⟩

/-- `10000 < N < 32768` at `P0_LOOP`: the `P0_POS` arm reaches `P0_GE`
in 13 steps without changing `N` or `Q0`. -/
theorem p0_to_ge_mid {s : Machine}
    (hpc : s.pc = 189)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hC : s.mem.get 7 = 10000)
    (hN1 : 10000 < (s.mem.get 17).toNat)
    (hN2 : (s.mem.get 17).toNat < 32768)
    (hcode : ∀ k : Nat, 189 ≤ k → k < 270 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s13 := runN s 13
    s13.pc = 255 ∧
    s13.halted = false ∧
    s13.mem.get 17 = s.mem.get 17 ∧
    s13.mem.get 20 = s.mem.get 20 ∧
    s13.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a) := by
  intro s13
  have hN0 : 0 < (s.mem.get 17).toNat := Nat.lt_trans (by decide) hN1
  have hgo := p0_goto_pos (s := s) hpc hh hZ hN0 hN2 hcode
  let s6 := runN s 6
  have hs6pc : s6.pc = 222 := hgo.1
  have hs6h := hgo.2.1
  have hZ6 := hgo.2.2.2.2.1
  have hpres6 := hgo.2.2.2.2.2
  have g6 (k : Nat) (h1 : 222 ≤ k) (h2 : k < 234) :
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres6 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have hmov := p0_pos_mov_N_T (s := s6) hs6pc hs6h hZ6 g6
  let s10 := runN s6 4
  have hs10pc : s10.pc = 234 := hmov.1
  have hs10h := hmov.2.1
  have hT10 : s10.mem.get 18 = s.mem.get 17 :=
    hmov.2.2.1.trans (hgo.2.2.2.1)
  have hZ10 := hmov.2.2.2.1
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hmov.2.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hs10C : s10.mem.get 7 = 10000 := (hpres10 7 (by decide) (by decide)).trans hC
  have g10 (k : Nat) (h1 : 234 ≤ k) (h2 : k < 237) :
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres10 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have hsub := p0_sub_C10000_T (s := s10) hs10pc hs10h hs10C g10
  have hs11pc : (step s10).pc = 237 := by rw [hsub]
  have hs11h : (step s10).halted = false := by rw [hsub]; exact hs10h
  have hs11Z : (step s10).mem.get 0 = 0 := by
    rw [hsub]
    exact (Mem.get_set_ne s10.mem 18 0 (s10.mem.get 18 - 10000) (by decide)).trans hZ10
  have hT11 : (step s10).mem.get 18 = s.mem.get 17 - 10000 := by
    rw [hsub]
    exact (Mem.get_set_eq s10.mem 18 (s10.mem.get 18 - 10000)).trans (by rw [hT10])
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → (step s10).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hsub]
    exact (Mem.get_set_ne s10.mem 18 a (s10.mem.get 18 - 10000) ha18).trans
      (hpres10 a ha18 ha0)
  have g11 (k : Nat) (h1 : 237 ≤ k) (h2 : k < 240) :
      (step s10).mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres11 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have enc := p0_enc_jlez_237 (s := step s10) hs11pc g11
  have hpc11 : (step s10).pc.toNat < 32768 := by simp [hs11pc]
  have hjlez :=
    step_JLEZ (s := step s10) (x := 18) (dest := 243)
      hs11h hpc11 hs11Z enc.1 enc.2.1 enc.2.2 (by decide)
  have hCton : (10000 : Word).toNat = 10000 := rfl
  have hTnat : ((step s10).mem.get 18).toNat = (s.mem.get 17).toNat - 10000 := by
    rw [hT11]
    exact word_sub_ge (s.mem.get 17) (10000 : Word)
      (Nat.le_of_lt (by simpa [hCton] using hN1))
  have hle : ( (step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18) = false := by
    have : le0 ((step s10).mem.get 18) = false := by
      have hpos : 0 < ((step s10).mem.get 18).toNat := by
        rw [hTnat]; omega
      have hhi : ((step s10).mem.get 18).toNat < 32768 := by
        rw [hTnat]; omega
      exact le0_pos hpos hhi
    simpa [le0] using this
  have hs12eq : step (step s10) = { step s10 with pc := (step s10).pc + 3 } := by
    have hif :
        (if (step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18 then (243 : Word)
          else (step s10).pc + 3) = (step s10).pc + 3 := by
      simp [hle]
    rw [hjlez, hif]
  have hs12pc : (step (step s10)).pc = 240 := by
    have : (step s10).pc + 3 = (240 : Word) := by simp [hs11pc]
    rw [hs12eq]; exact this
  have hs12h : (step (step s10)).halted = false := by rw [hs12eq]; exact hs11h
  have hs12Z : (step (step s10)).mem.get 0 = 0 := by rw [hs12eq]; exact hs11Z
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → (step (step s10)).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs12eq]
    exact hpres11 a ha18 ha0
  have g12 (k : Nat) (h1 : 240 ≤ k) (h2 : k < 243) :
      (step (step s10)).mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres12 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have encJ := p0_enc_jmp_240 (s := step (step s10)) hs12pc g12
  have hpc12 : (step (step s10)).pc.toNat < 32768 := by simp [hs12pc]
  have hjmp :=
    step_JMP (s := step (step s10)) (dest := 255)
      hs12h hpc12 hs12Z encJ.1 encJ.2.1 encJ.2.2
  have hrun : s13 = step (step (step s10)) := by
    have h13 : runN s 13 = runN s6 7 := runN_add_eq s 6 7 13 (by decide)
    have h7 : runN s6 7 = runN s10 3 := runN_add_eq s6 4 3 7 (by decide)
    have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
    have h3 := runN_3_steps s10 hs10h hpc10 hs11h hpc11 hs12h hpc12
    exact h13.trans (h7.trans h3)
  have hs13pc : s13.pc = 255 := by rw [hrun, hjmp]
  have hs13h : s13.halted = false := by rw [hrun, hjmp]; exact hs12h
  have hmem : (step (step (step s10))).mem = (step (step s10)).mem := by rw [hjmp]
  have hs13Z : s13.mem.get 0 = 0 := by rw [hrun, hmem, hs12eq]; exact hs11Z
  have hs13N : s13.mem.get 17 = s.mem.get 17 := by
    rw [hrun, hmem]; exact hpres12 17 (by decide) (by decide)
  have hs13Q : s13.mem.get 20 = s.mem.get 20 := by
    rw [hrun, hmem]; exact hpres12 20 (by decide) (by decide)
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hmem]
    exact hpres12 a ha18 ha0
  exact ⟨hs13pc, hs13h, hs13N, hs13Q, hs13Z, hpres⟩

/-- `N = 10000` at `P0_LOOP`: the `P0_LE` arm falls through to `P0_GE`
in 16 steps without changing `N` or `Q0`. -/
theorem p0_to_ge_eq {s : Machine}
    (hpc : s.pc = 189)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hC : s.mem.get 7 = 10000)
    (hN : s.mem.get 17 = 10000)
    (hcode : ∀ k : Nat, 189 ≤ k → k < 270 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s16 := runN s 16
    s16.pc = 255 ∧
    s16.halted = false ∧
    s16.mem.get 17 = 10000 ∧
    s16.mem.get 20 = s.mem.get 20 ∧
    s16.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a) := by
  intro s16
  have hNton : (s.mem.get 17).toNat = 10000 := by
    have hCton : (10000 : Word).toNat = 10000 := rfl
    simpa [hN] using hCton
  have hN0 : 0 < (s.mem.get 17).toNat := by omega
  have hNhi : (s.mem.get 17).toNat < 32768 := by omega
  have hgo := p0_goto_pos (s := s) hpc hh hZ hN0 hNhi hcode
  let s6 := runN s 6
  have hs6pc : s6.pc = 222 := hgo.1
  have hs6h := hgo.2.1
  have hZ6 := hgo.2.2.2.2.1
  have hpres6 := hgo.2.2.2.2.2
  have g6 (k : Nat) (h1 : 222 ≤ k) (h2 : k < 234) :
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres6 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have hmov := p0_pos_mov_N_T (s := s6) hs6pc hs6h hZ6 g6
  let s10 := runN s6 4
  have hs10pc : s10.pc = 234 := hmov.1
  have hs10h := hmov.2.1
  have hT10 : s10.mem.get 18 = (10000 : Word) :=
    (hmov.2.2.1.trans (hgo.2.2.2.1)).trans hN
  have hZ10 := hmov.2.2.2.1
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hmov.2.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hs10C : s10.mem.get 7 = 10000 := (hpres10 7 (by decide) (by decide)).trans hC
  have hs10ONE : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have g10 (k : Nat) (h1 : 234 ≤ k) (h2 : k < 237) :
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres10 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have hsub := p0_sub_C10000_T (s := s10) hs10pc hs10h hs10C g10
  have hs11pc : (step s10).pc = 237 := by rw [hsub]
  have hs11h : (step s10).halted = false := by rw [hsub]; exact hs10h
  have hs11Z : (step s10).mem.get 0 = 0 := by
    rw [hsub]
    exact (Mem.get_set_ne s10.mem 18 0 (s10.mem.get 18 - 10000) (by decide)).trans hZ10
  have hT11 : (step s10).mem.get 18 = 0 := by
    rw [hsub]
    have : s10.mem.get 18 - 10000 = (0 : Word) := by
      rw [hT10]; rfl
    exact (Mem.get_set_eq s10.mem 18 (s10.mem.get 18 - 10000)).trans this
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → (step s10).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hsub]
    exact (Mem.get_set_ne s10.mem 18 a (s10.mem.get 18 - 10000) ha18).trans
      (hpres10 a ha18 ha0)
  have hs11ONE : (step s10).mem.get 3 = 1 :=
    (hpres11 3 (by decide) (by decide)).trans hONE
  have g11 (k : Nat) (h1 : 237 ≤ k) (h2 : k < 240) :
      (step s10).mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres11 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have enc := p0_enc_jlez_237 (s := step s10) hs11pc g11
  have hpc11 : (step s10).pc.toNat < 32768 := by simp [hs11pc]
  have hjlez :=
    step_JLEZ (s := step s10) (x := 18) (dest := 243)
      hs11h hpc11 hs11Z enc.1 enc.2.1 enc.2.2 (by decide)
  have hle : ( (step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18) = true := by
    have : le0 ((step s10).mem.get 18) = true := by
      rw [hT11]; exact le0_zero
    simpa [le0] using this
  have hs12eq : step (step s10) = { step s10 with pc := 243 } := by
    have hif :
        (if (step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18 then (243 : Word)
          else (step s10).pc + 3) = (243 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hs12pc : (step (step s10)).pc = 243 := by rw [hs12eq]
  have hs12h : (step (step s10)).halted = false := by rw [hs12eq]; exact hs11h
  have hs12Z : (step (step s10)).mem.get 0 = 0 := by rw [hs12eq]; exact hs11Z
  have hs12ONE : (step (step s10)).mem.get 3 = 1 := by rw [hs12eq]; exact hs11ONE
  have hT12 : (step (step s10)).mem.get 18 = 0 := by rw [hs12eq]; exact hT11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → (step (step s10)).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs12eq]
    exact hpres11 a ha18 ha0
  let s12 := step (step s10)
  have g12 (k : Nat) (h1 : 243 ≤ k) (h2 : k < 252) :
      s12.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres12 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have hinc := p0_le_inc_T (s := s12) hs12pc hs12h hs12Z hs12ONE g12
  let s15 := runN s12 3
  have hs15pc : s15.pc = 252 := hinc.1
  have hs15h := hinc.2.1
  have hT15 : s15.mem.get 18 = 1 := by
    have : s12.mem.get 18 + 1 = (0 : Word) + 1 := by rw [hT12]
    exact hinc.2.2.1.trans this
  have hZ15 := hinc.2.2.2.1
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres12 a ha18 ha0)
  have g15 (k : Nat) (h1 : 252 ≤ k) (h2 : k < 255) :
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres15 (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans (hcode k (by omega) (by omega))
  have enc2 := p0_enc_jlez_252 (s := s15) hs15pc g15
  have hpc15 : s15.pc.toNat < 32768 := by simp [hs15pc]
  have hjlez2 :=
    step_JLEZ (s := s15) (x := 18) (dest := 270)
      hs15h hpc15 hZ15 enc2.1 enc2.2.1 enc2.2.2 (by decide)
  have hle2 : (s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18) = false := by
    have : le0 (s15.mem.get 18) = false := by
      rw [hT15]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs16eq : step s15 = { s15 with pc := s15.pc + 3 } := by
    have hif :
        (if s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18 then (270 : Word)
          else s15.pc + 3) = s15.pc + 3 := by
      simp [hle2]
    rw [hjlez2, hif]
  have hs16pc' : (step s15).pc = 255 := by
    have : s15.pc + 3 = (255 : Word) := by simp [hs15pc]
    rw [hs16eq]; exact this
  have hrun : s16 = step s15 := by
    have h16 : runN s 16 = runN s6 10 := runN_add_eq s 6 10 16 (by decide)
    have h10 : runN s6 10 = runN s10 6 := runN_add_eq s6 4 6 10 (by decide)
    have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
    have h6 : runN s10 6 = runN (step s10) 5 := runN_succ_go s10 5 hs10h hpc10
    have h5 : runN (step s10) 5 = runN s12 4 := runN_succ_go (step s10) 4 hs11h hpc11
    have h4 : runN s12 4 = runN s15 1 := runN_add_eq s12 3 1 4 (by decide)
    have h1 := runN_one s15 hs15h hpc15
    exact h16.trans (h10.trans (h6.trans (h5.trans (h4.trans h1))))
  have hs16pc : s16.pc = 255 := by rw [hrun, hs16pc']
  have hs16h : s16.halted = false := by rw [hrun, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by rw [hrun, hs16eq]; exact hZ15
  have hs16N : s16.mem.get 17 = 10000 := by
    rw [hrun, hs16eq]; exact (hpres15 17 (by decide) (by decide)).trans hN
  have hs16Q : s16.mem.get 20 = s.mem.get 20 := by
    rw [hrun, hs16eq]; exact hpres15 20 (by decide) (by decide)
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hs16eq]
    exact hpres15 a ha18 ha0
  exact ⟨hs16pc, hs16h, hs16N, hs16Q, hs16Z, hpres⟩


/-- All `N ≥ 10000` compare arms reach `P0_GE` in `p0CmpSteps N` steps,
leaving `N` and `Q0` unchanged. -/
theorem p0_to_ge {s : Machine}
    (hpc : s.pc = 189)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hC : s.mem.get 7 = 10000)
    (hN : 10000 ≤ (s.mem.get 17).toNat)
    (hcode : ∀ k : Nat, 189 ≤ k → k < 270 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let n := (s.mem.get 17).toNat
    let sk := runN s (p0CmpSteps n)
    sk.pc = 255 ∧
    sk.halted = false ∧
    sk.mem.get 17 = s.mem.get 17 ∧
    sk.mem.get 20 = s.mem.get 20 ∧
    sk.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → sk.mem.get a = s.mem.get a) := by
  intro n sk
  by_cases hhi : 32768 ≤ n
  · have hst : p0CmpSteps n = 9 := p0CmpSteps_hi hhi
    have hge :=
      p0_to_ge_hi (s := s) hpc hh hZ hONE (by exact hhi) hcode
    have hsk : sk = runN s 9 := by simp [sk, hst]
    rw [hsk]
    exact hge
  · by_cases heq : n = 10000
    · have hst : p0CmpSteps n = 16 := by rw [heq, p0CmpSteps_eq]
      have hW : s.mem.get 17 = 10000 := by
        have := word_eq_of_toNat (s.mem.get 17) 10000 (by decide) (heq ▸ (rfl : n = (s.mem.get 17).toNat).symm)
        exact this
      have hge :=
        p0_to_ge_eq (s := s) hpc hh hZ hONE hC hW hcode
      have hsk : sk = runN s 16 := by simp [sk, hst]
      rw [hsk]
      refine ⟨hge.1, hge.2.1, hge.2.2.1.trans hW.symm, hge.2.2.2.1,
        hge.2.2.2.2.1, hge.2.2.2.2.2⟩
    · have h2 : n < 32768 := Nat.lt_of_not_ge hhi
      have h1 : 10000 < n := Nat.lt_of_le_of_ne hN (Ne.symm heq)
      have hst : p0CmpSteps n = 13 := p0CmpSteps_mid h1 h2
      have hge :=
        p0_to_ge_mid (s := s) hpc hh hZ hC h1 h2 hcode
      have hsk : sk = runN s 13 := by simp [sk, hst]
      rw [hsk]
      exact hge

/-- One full `P0` iteration: compare diamond plus the `P0_GE` body,
returning to `P0_LOOP` with `N` decreased by 10000 and `Q0` increased
by 1. Reconstructs the same magnitude. -/
theorem p0_one_iter {s : Machine}
    (hpc : s.pc = 189)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hC : s.mem.get 7 = 10000)
    (hN : 10000 ≤ (s.mem.get 17).toNat)
    (hQ : (s.mem.get 20).toNat + 1 < 65536)
    (hcode : ∀ k : Nat, 189 ≤ k → k < 270 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let n := (s.mem.get 17).toNat
    let q := (s.mem.get 20).toNat
    let s1 := runN s (p0CmpSteps n + 5)
    s1.pc = 189 ∧
    s1.halted = false ∧
    s1.mem.get 0 = 0 ∧
    s1.mem.get 3 = 1 ∧
    s1.mem.get 7 = 10000 ∧
    (s1.mem.get 17).toNat = n - 10000 ∧
    (s1.mem.get 20).toNat = q + 1 ∧
    q * 10000 + n = (s1.mem.get 20).toNat * 10000 + (s1.mem.get 17).toNat ∧
    (∀ k : Nat, 189 ≤ k → k < 270 →
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]!) ∧
    (∀ a, a ≠ 17 → a ≠ 20 → a ≠ 18 → a ≠ 0 → s1.mem.get a = s.mem.get a) := by
  intro n q s1
  have hto := p0_to_ge (s := s) hpc hh hZ hONE hC hN hcode
  let sk := runN s (p0CmpSteps n)
  have hskpc : sk.pc = 255 := hto.1
  have hskh : sk.halted = false := hto.2.1
  have hskN : sk.mem.get 17 = s.mem.get 17 := hto.2.2.1
  have hskQ : sk.mem.get 20 = s.mem.get 20 := hto.2.2.2.1
  have hskZ : sk.mem.get 0 = 0 := hto.2.2.2.2.1
  have hpresk := hto.2.2.2.2.2
  have hskONE : sk.mem.get 3 = 1 :=
    (hpresk 3 (by decide) (by decide)).trans hONE
  have hskC : sk.mem.get 7 = 10000 :=
    (hpresk 7 (by decide) (by decide)).trans hC
  have hcodek (k : Nat) (h1 : 255 ≤ k) (h2 : k < 270) :
      sk.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpresk (UInt16.ofNat k) (ofNat_ne k 18 (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by omega) (by omega))).trans
      (hcode k (by omega) h2)
  have hNge : 10000 ≤ (sk.mem.get 17).toNat := by
    rw [hskN]; exact hN
  have hQsk : (sk.mem.get 20).toNat + 1 < 65536 := by
    rw [hskQ]; exact hQ
  have hbody :=
    p0_ge_body (s := sk) hskpc hskh hskZ hskONE hskC hNge hQsk hcodek
  have hrun : s1 = runN sk 5 :=
    runN_add s (p0CmpSteps n) 5
  have hs1pc : s1.pc = 189 := by rw [hrun]; exact hbody.1
  have hs1h : s1.halted = false := by rw [hrun]; exact hbody.2.1
  have hs1Z : s1.mem.get 0 = 0 := by rw [hrun]; exact hbody.2.2.1
  have hs1Nton : (s1.mem.get 17).toNat = n - 10000 := by
    rw [hrun]
    have : (sk.mem.get 17).toNat = n := by rw [hskN]
    exact hbody.2.2.2.2.2.1.trans (by rw [this])
  have hs1Qton : (s1.mem.get 20).toNat = q + 1 := by
    rw [hrun]
    have : (sk.mem.get 20).toNat = q := by rw [hskQ]
    exact hbody.2.2.2.2.2.2.1.trans (by rw [this])
  have hs1ONE : s1.mem.get 3 = 1 := by
    rw [hrun]
    have hpresB := hbody.2.2.2.2.2.2.2
    exact (hpresB 3 (by decide) (by decide) (by decide)).trans hskONE
  have hs1C : s1.mem.get 7 = 10000 := by
    rw [hrun]
    have hpresB := hbody.2.2.2.2.2.2.2
    exact (hpresB 7 (by decide) (by decide) (by decide)).trans hskC
  have hinv : q * 10000 + n = (s1.mem.get 20).toNat * 10000 + (s1.mem.get 17).toNat := by
    rw [hs1Qton, hs1Nton]
    omega
  have hcode1 (k : Nat) (h1 : 189 ≤ k) (h2 : k < 270) :
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    rw [hrun]
    have hpresB := hbody.2.2.2.2.2.2.2
    have hne17 : UInt16.ofNat k ≠ 17 :=
      ofNat_ne k 17 (by omega) (by omega) (by omega)
    have hne20 : UInt16.ofNat k ≠ 20 :=
      ofNat_ne k 20 (by omega) (by omega) (by omega)
    have hne0 : UInt16.ofNat k ≠ 0 :=
      ofNat_ne k 0 (by omega) (by omega) (by omega)
    exact (hpresB (UInt16.ofNat k) hne17 hne20 hne0).trans
      ((hpresk (UInt16.ofNat k)
          (ofNat_ne k 18 (by omega) (by omega) (by omega)) hne0).trans
        (hcode k h1 h2))
  have hpres : ∀ a, a ≠ 17 → a ≠ 20 → a ≠ 18 → a ≠ 0 →
      s1.mem.get a = s.mem.get a := by
    intro a ha17 ha20 ha18 ha0
    rw [hrun]
    have hpresB := hbody.2.2.2.2.2.2.2
    exact (hpresB a ha17 ha20 ha0).trans (hpresk a ha18 ha0)
  exact ⟨hs1pc, hs1h, hs1Z, hs1ONE, hs1C, hs1Nton, hs1Qton, hinv, hcode1, hpres⟩


/-- The `P0_LOOP` reconstruction invariant: after `p0PlaceSteps N` steps
the machine is at `P0_DONE` with remainder `N < 10000` and
`Q0 * 10000 + N` equal to the entry magnitude. -/
theorem p0_loop_gen (n : Nat) :
    ∀ (s : Machine),
      s.pc = 189 →
      s.halted = false →
      s.mem.get 0 = 0 →
      s.mem.get 3 = 1 →
      s.mem.get 7 = 10000 →
      (s.mem.get 17).toNat = n →
      (s.mem.get 20).toNat + n / 10000 < 65536 →
      (∀ k : Nat, 189 ≤ k → k < 270 →
        s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) →
      let q := (s.mem.get 20).toNat
      let s' := runN s (p0PlaceSteps n)
      s'.pc = 270 ∧
      s'.halted = false ∧
      s'.mem.get 0 = 0 ∧
      (s'.mem.get 17).toNat < 10000 ∧
      q * 10000 + n = (s'.mem.get 20).toNat * 10000 + (s'.mem.get 17).toNat ∧
      (∀ a, a ≠ 17 → a ≠ 20 → a ≠ 18 → a ≠ 0 → s'.mem.get a = s.mem.get a) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s hpc hh hZ hONE hC hn hQ hcode
    intro q s'
    by_cases hlt : n < 10000
    · by_cases h0 : n = 0
      · subst h0
        have hW : s.mem.get 17 = 0 :=
          word_eq_of_toNat (s.mem.get 17) 0 (by decide) hn
        have hex := p0_exit_zero (s := s) hpc hh hZ hONE hW hcode
        have hs' : s' = runN s 10 := by
          simp [s', p0PlaceSteps_zero]
        rw [hs']
        have hltN : ((runN s 10).mem.get 17).toNat < 10000 := by
          have : (runN s 10).mem.get 17 = 0 := hex.2.2.1
          simp [this]
        have hinv0 :
            q * 10000 + 0 =
              ((runN s 10).mem.get 20).toNat * 10000 + ((runN s 10).mem.get 17).toNat := by
          have hQ0 : (runN s 10).mem.get 20 = s.mem.get 20 := hex.2.2.2.1
          have hN0 : (runN s 10).mem.get 17 = 0 := hex.2.2.1
          rw [hQ0, hN0]
          have : (s.mem.get 20).toNat = q := rfl
          simp [this]
        have hpres0 : ∀ a, a ≠ 17 → a ≠ 20 → a ≠ 18 → a ≠ 0 →
            (runN s 10).mem.get a = s.mem.get a := by
          intro a ha17 ha20 ha18 ha0
          exact hex.2.2.2.2.2 a ha18 ha0
        exact ⟨hex.1, hex.2.1, hex.2.2.2.2.1, hltN, hinv0, hpres0⟩
      · have hpos : 0 < n := Nat.pos_of_ne_zero h0
        have hNpos : 0 < (s.mem.get 17).toNat := by rw [hn]; exact hpos
        have hNlt : (s.mem.get 17).toNat < 10000 := by rw [hn]; exact hlt
        have hex :=
          p0_exit_small (s := s) hpc hh hZ hONE hC hNpos hNlt hcode
        have hs' : s' = runN s 16 := by
          simp [s', p0PlaceSteps_small hpos hlt]
        rw [hs']
        have hltN : ((runN s 16).mem.get 17).toNat < 10000 := by
          have : (runN s 16).mem.get 17 = s.mem.get 17 := hex.2.2.1
          rw [this, hn]; exact hlt
        have hinv0 :
            q * 10000 + n =
              ((runN s 16).mem.get 20).toNat * 10000 + ((runN s 16).mem.get 17).toNat := by
          have hQ0 : (runN s 16).mem.get 20 = s.mem.get 20 := hex.2.2.2.1
          have hNs : (runN s 16).mem.get 17 = s.mem.get 17 := hex.2.2.1
          rw [hQ0, hNs, hn]
        have hpres0 : ∀ a, a ≠ 17 → a ≠ 20 → a ≠ 18 → a ≠ 0 →
            (runN s 16).mem.get a = s.mem.get a := by
          intro a ha17 ha20 ha18 ha0
          exact hex.2.2.2.2.2 a ha18 ha0
        exact ⟨hex.1, hex.2.1, hex.2.2.2.2.1, hltN, hinv0, hpres0⟩
    · have hge : 10000 ≤ n := Nat.le_of_not_lt hlt
      have hNge : 10000 ≤ (s.mem.get 17).toNat := by rw [hn]; exact hge
      have hQ1 : (s.mem.get 20).toNat + 1 < 65536 := by
        have : 1 ≤ n / 10000 := Nat.div_pos hge (by decide)
        omega
      have hone :=
        p0_one_iter (s := s) hpc hh hZ hONE hC hNge hQ1 hcode
      rw [hn] at hone
      have hsteps := p0PlaceSteps_ge hge
      have hrun : s' = runN (runN s (p0CmpSteps n + 5)) (p0PlaceSteps (n - 10000)) := by
        have hadd :=
          runN_add s (p0CmpSteps n + 5) (p0PlaceSteps (n - 10000))
        have : p0PlaceSteps n = p0CmpSteps n + 5 + p0PlaceSteps (n - 10000) := hsteps
        simp [s', this, hadd]
      -- Work directly with `runN s (p0CmpSteps n + 5)` (no `set`/`let`).
      have hs1pc : (runN s (p0CmpSteps n + 5)).pc = 189 := hone.1
      have hs1h : (runN s (p0CmpSteps n + 5)).halted = false := hone.2.1
      have hs1Z : (runN s (p0CmpSteps n + 5)).mem.get 0 = 0 := hone.2.2.1
      have hs1ONE : (runN s (p0CmpSteps n + 5)).mem.get 3 = 1 := hone.2.2.2.1
      have hs1C : (runN s (p0CmpSteps n + 5)).mem.get 7 = 10000 := hone.2.2.2.2.1
      have hs1N : ((runN s (p0CmpSteps n + 5)).mem.get 17).toNat = n - 10000 :=
        hone.2.2.2.2.2.1
      have hs1Q : ((runN s (p0CmpSteps n + 5)).mem.get 20).toNat = q + 1 :=
        hone.2.2.2.2.2.2.1
      have hinv1 := hone.2.2.2.2.2.2.2.1
      have hcode1 := hone.2.2.2.2.2.2.2.2.1
      have hpres1 := hone.2.2.2.2.2.2.2.2.2
      have hQ1n :
          ((runN s (p0CmpSteps n + 5)).mem.get 20).toNat + (n - 10000) / 10000 < 65536 := by
        have hdiv : (n - 10000) / 10000 + 1 = n / 10000 :=
          (Nat.div_eq_sub_div (by decide : 0 < 10000) hge).symm
        rw [hs1Q]
        omega
      have ihn :=
        ih (n - 10000) (by omega) (runN s (p0CmpSteps n + 5))
          hs1pc hs1h hs1Z hs1ONE hs1C hs1N hQ1n hcode1
      rw [hrun]
      have hpc' : (runN (runN s (p0CmpSteps n + 5)) (p0PlaceSteps (n - 10000))).pc = 270 := ihn.1
      have hh' : (runN (runN s (p0CmpSteps n + 5)) (p0PlaceSteps (n - 10000))).halted = false := ihn.2.1
      have hZ' : (runN (runN s (p0CmpSteps n + 5)) (p0PlaceSteps (n - 10000))).mem.get 0 = 0 := ihn.2.2.1
      have hlt' :
          ((runN (runN s (p0CmpSteps n + 5)) (p0PlaceSteps (n - 10000))).mem.get 17).toNat < 10000 :=
        ihn.2.2.2.1
      have hinv' :
          ((runN s (p0CmpSteps n + 5)).mem.get 20).toNat * 10000 + (n - 10000) =
            ((runN (runN s (p0CmpSteps n + 5)) (p0PlaceSteps (n - 10000))).mem.get 20).toNat * 10000 +
              ((runN (runN s (p0CmpSteps n + 5)) (p0PlaceSteps (n - 10000))).mem.get 17).toNat :=
        ihn.2.2.2.2.1
      have hpres' :
          ∀ a, a ≠ 17 → a ≠ 20 → a ≠ 18 → a ≠ 0 →
            (runN (runN s (p0CmpSteps n + 5)) (p0PlaceSteps (n - 10000))).mem.get a =
              (runN s (p0CmpSteps n + 5)).mem.get a :=
        ihn.2.2.2.2.2
      have hinvF :
          q * 10000 + n =
            ((runN (runN s (p0CmpSteps n + 5)) (p0PlaceSteps (n - 10000))).mem.get 20).toNat * 10000 +
              ((runN (runN s (p0CmpSteps n + 5)) (p0PlaceSteps (n - 10000))).mem.get 17).toNat := by
        have hL : q * 10000 + n =
            ((runN s (p0CmpSteps n + 5)).mem.get 20).toNat * 10000 +
              ((runN s (p0CmpSteps n + 5)).mem.get 17).toNat := hinv1
        rw [hs1N] at hL
        exact hL.trans hinv'
      have hpresF : ∀ a, a ≠ 17 → a ≠ 20 → a ≠ 18 → a ≠ 0 →
          (runN (runN s (p0CmpSteps n + 5)) (p0PlaceSteps (n - 10000))).mem.get a =
            s.mem.get a := by
        intro a ha17 ha20 ha18 ha0
        exact (hpres' a ha17 ha20 ha18 ha0).trans (hpres1 a ha17 ha20 ha18 ha0)
      exact ⟨hpc', hh', hZ', hlt', hinvF, hpresF⟩

/-- Package of `p0_loop_gen` at the current machine's `N`. -/
theorem p0_loop {s : Machine}
    (hpc : s.pc = 189)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hC : s.mem.get 7 = 10000)
    (hQ : (s.mem.get 20).toNat + (s.mem.get 17).toNat / 10000 < 65536)
    (hcode : ∀ k : Nat, 189 ≤ k → k < 270 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let n := (s.mem.get 17).toNat
    let q := (s.mem.get 20).toNat
    let s' := runN s (p0PlaceSteps n)
    s'.pc = 270 ∧
    s'.halted = false ∧
    s'.mem.get 0 = 0 ∧
    (s'.mem.get 17).toNat < 10000 ∧
    q * 10000 + n = (s'.mem.get 20).toNat * 10000 + (s'.mem.get 17).toNat ∧
    (∀ a, a ≠ 17 → a ≠ 20 → a ≠ 18 → a ≠ 0 → s'.mem.get a = s.mem.get a) :=
  p0_loop_gen (s.mem.get 17).toNat s hpc hh hZ hONE hC rfl hQ hcode

end IntFmt
