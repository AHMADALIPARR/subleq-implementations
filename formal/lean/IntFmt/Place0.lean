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

end IntFmt
