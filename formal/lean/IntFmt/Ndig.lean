/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Leading-zero `NDIG` selection after ASCII conversion of `Q0`..`Q4`.
Block lemmas, not end-to-end correctness.
-/

import IntFmt.Ascii
import IntFmt.DecChunksB

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

-- cell560 lives in Ascii.lean as a private theorem; re-bind it here.
private theorem cell560 (off : Nat) (h : off < 16) :
    intfmtImage[560 + off]! = decChunk035[off]! :=
  extract_chunk 560 decChunk035 image_chunk035 off h (by decide)

private theorem cell576 (off : Nat) (h : off < 16) :
    intfmtImage[576 + off]! = decChunk036[off]! :=
  extract_chunk 576 decChunk036 image_chunk036 off h (by decide)


private theorem cell592 (off : Nat) (h : off < 16) :
    intfmtImage[592 + off]! = decChunk037[off]! :=
  extract_chunk 592 decChunk037 image_chunk037 off h (by decide)


private theorem cell608 (off : Nat) (h : off < 16) :
    intfmtImage[608 + off]! = decChunk038[off]! :=
  extract_chunk 608 decChunk038 image_chunk038 off h (by decide)


private theorem cell624 (off : Nat) (h : off < 16) :
    intfmtImage[624 + off]! = decChunk039[off]! :=
  extract_chunk 624 decChunk039 image_chunk039 off h (by decide)


private theorem cell640 (off : Nat) (h : off < 16) :
    intfmtImage[640 + off]! = decChunk040[off]! :=
  extract_chunk 640 decChunk040 image_chunk040 off h (by decide)


private theorem cell656 (off : Nat) (h : off < 16) :
    intfmtImage[656 + off]! = decChunk041[off]! :=
  extract_chunk 656 decChunk041 image_chunk041 off h (by decide)


private theorem cell672 (off : Nat) (h : off < 16) :
    intfmtImage[672 + off]! = decChunk042[off]! :=
  extract_chunk 672 decChunk042 image_chunk042 off h (by decide)


private theorem cell688 (off : Nat) (h : off < 16) :
    intfmtImage[688 + off]! = decChunk043[off]! :=
  extract_chunk 688 decChunk043 image_chunk043 off h (by decide)


private theorem cell704 (off : Nat) (h : off < 16) :
    intfmtImage[704 + off]! = decChunk044[off]! :=
  extract_chunk 704 decChunk044 image_chunk044 off h (by decide)


private theorem cell720 (off : Nat) (h : off < 16) :
    intfmtImage[720 + off]! = decChunk045[off]! :=
  extract_chunk 720 decChunk045 image_chunk045 off h (by decide)


private theorem cell736 (off : Nat) (h : off < 16) :
    intfmtImage[736 + off]! = decChunk046[off]! :=
  extract_chunk 736 decChunk046 image_chunk046 off h (by decide)


private theorem cell752 (off : Nat) (h : off < 16) :
    intfmtImage[752 + off]! = decChunk047[off]! :=
  extract_chunk 752 decChunk047 image_chunk047 off h (by decide)


private theorem cell768 (off : Nat) (h : off < 16) :
    intfmtImage[768 + off]! = decChunk048[off]! :=
  extract_chunk 768 decChunk048 image_chunk048 off h (by decide)


private theorem cell784 (off : Nat) (h : off < 16) :
    intfmtImage[784 + off]! = decChunk049[off]! :=
  extract_chunk 784 decChunk049 image_chunk049 off h (by decide)


private theorem cell800 (off : Nat) (h : off < 16) :
    intfmtImage[800 + off]! = decChunk050[off]! :=
  extract_chunk 800 decChunk050 image_chunk050 off h (by decide)


private theorem cell816 (off : Nat) (h : off < 16) :
    intfmtImage[816 + off]! = decChunk051[off]! :=
  extract_chunk 816 decChunk051 image_chunk051 off h (by decide)


private theorem cell832 (off : Nat) (h : off < 16) :
    intfmtImage[832 + off]! = decChunk052[off]! :=
  extract_chunk 832 decChunk052 image_chunk052 off h (by decide)


private theorem cell848 (off : Nat) (h : off < 16) :
    intfmtImage[848 + off]! = decChunk053[off]! :=
  extract_chunk 848 decChunk053 image_chunk053 off h (by decide)


private theorem cell864 (off : Nat) (h : off < 16) :
    intfmtImage[864 + off]! = decChunk054[off]! :=
  extract_chunk 864 decChunk054 image_chunk054 off h (by decide)

/-- MOV Q0 T at pc 570, 4 steps to 582. -/
theorem ndig_mov_Q0_T {s : Machine}
    (hpc : s.pc = 570)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 570 ≤ k → k < 582 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 582 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 20 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 20 = s.mem.get 20 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 570 :=
    hpc.trans (rfl : (570 : Word) = UInt16.ofNat 570)
  have g (k : Nat) (h1 : 570 ≤ k) (h2 : k < 582) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (570 + off) :=
    word_pc_off 570 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk035[10]! = 18 := rfl
    exact (g 570 (by decide) (by decide)).trans ((cell560 10 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk035[11]! = 18 := rfl
    exact (g 571 (by decide) (by decide)).trans ((cell560 11 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk035[12]! = 573 := rfl
    have hv : (573 : Word) = UInt16.ofNat 573 := rfl
    exact (g 572 (by decide) (by decide)).trans ((cell560 12 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 20 := by
    rw [poff 3 (by decide)]
    have hval : decChunk035[13]! = 20 := rfl
    exact (g 573 (by decide) (by decide)).trans ((cell560 13 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk035[14]! = 0 := rfl
    exact (g 574 (by decide) (by decide)).trans ((cell560 14 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk035[15]! = 576 := rfl
    have hv : (576 : Word) = UInt16.ofNat 576 := rfl
    exact (g 575 (by decide) (by decide)).trans ((cell560 15 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk036[0]! = 0 := rfl
    exact (g 576 (by decide) (by decide)).trans ((cell576 0 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk036[1]! = 18 := rfl
    exact (g 577 (by decide) (by decide)).trans ((cell576 1 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk036[2]! = 579 := rfl
    have hv : (579 : Word) = UInt16.ofNat 579 := rfl
    exact (g 578 (by decide) (by decide)).trans ((cell576 2 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk036[3]! = 0 := rfl
    exact (g 579 (by decide) (by decide)).trans ((cell576 3 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk036[4]! = 0 := rfl
    exact (g 580 (by decide) (by decide)).trans ((cell576 4 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk036[5]! = 582 := rfl
    have hv : (582 : Word) = UInt16.ofNat 582 := rfl
    exact (g 581 (by decide) (by decide)).trans ((cell576 5 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 570 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 570 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 20) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 582 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (582 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 582 = (582 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- SUB K48 T at pc 582. -/
theorem ndig_sub_K48_T_582 {s : Machine}
    (hpc : s.pc = 582)
    (hh : s.halted = false)
    (hK48 : s.mem.get 8 = 48)
    (hcode : ∀ k : Nat, 582 ≤ k → k < 585 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - 48)
        pc := 585 } := by
  have hp : s.pc = UInt16.ofNat 582 :=
    hpc.trans (rfl : (582 : Word) = UInt16.ofNat 582)
  have g (k : Nat) (h1 : 582 ≤ k) (h2 : k < 585) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 8 := by
    rw [hp]
    have hval : decChunk036[6]! = 8 := rfl
    exact (g 582 (by decide) (by decide)).trans ((cell576 6 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (583 : Word) := by simp [hpc]
    rw [this, (rfl : (583 : Word) = UInt16.ofNat 583)]
    have hval : decChunk036[7]! = 18 := rfl
    exact (g 583 (by decide) (by decide)).trans ((cell576 7 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (584 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (585 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (584 : Word) = UInt16.ofNat 584)]
    have hval : decChunk036[8]! = 585 := rfl
    have hv : (585 : Word) = UInt16.ofNat 585 := rfl
    exact (g 584 (by decide) (by decide)).trans ((cell576 8 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 8) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (585 : Word) := by simp [hpc]
  have hmem : s.mem.get 18 - s.mem.get 8 = s.mem.get 18 - 48 := by
    simp [hK48]
  rw [hsub, hpc', hmem]

/-- JLEZ T S1 at pc 585. -/
theorem ndig_enc_jlez_585 {s : Machine}
    (hpc : s.pc = 585)
    (hcode : ∀ k : Nat, 585 ≤ k → k < 585+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 591 := by
  have hp : s.pc = UInt16.ofNat 585 :=
    hpc.trans (rfl : (585 : Word) = UInt16.ofNat 585)
  have g (k : Nat) (h1 : 585 ≤ k) (h2 : k < 585+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk036[9]! = 0 := rfl
    exact (g 585 (by decide) (by decide)).trans ((cell576 9 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (586 : Word) := by simp [hpc]
    rw [this, (rfl : (586 : Word) = UInt16.ofNat 586)]
    have hval : decChunk036[10]! = 18 := rfl
    exact (g 586 (by decide) (by decide)).trans ((cell576 10 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 591 := by
    have : s.pc + 2 = (587 : Word) := by simp [hpc]
    rw [this, (rfl : (587 : Word) = UInt16.ofNat 587)]
    have hval : decChunk036[11]! = 591 := rfl
    exact (g 587 (by decide) (by decide)).trans ((cell576 11 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP FIVE at pc 588. -/
theorem ndig_enc_jmp_588 {s : Machine}
    (hpc : s.pc = 588)
    (hcode : ∀ k : Nat, 588 ≤ k → k < 588+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 657 := by
  have hp : s.pc = UInt16.ofNat 588 :=
    hpc.trans (rfl : (588 : Word) = UInt16.ofNat 588)
  have g (k : Nat) (h1 : 588 ≤ k) (h2 : k < 588+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk036[12]! = 0 := rfl
    exact (g 588 (by decide) (by decide)).trans ((cell576 12 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (589 : Word) := by simp [hpc]
    rw [this, (rfl : (589 : Word) = UInt16.ofNat 589)]
    have hval : decChunk036[13]! = 0 := rfl
    exact (g 589 (by decide) (by decide)).trans ((cell576 13 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 657 := by
    have : s.pc + 2 = (590 : Word) := by simp [hpc]
    rw [this, (rfl : (590 : Word) = UInt16.ofNat 590)]
    have hval : decChunk036[14]! = 657 := rfl
    exact (g 590 (by decide) (by decide)).trans ((cell576 14 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV Q1 T at S1 (pc 591), 4 steps to 603. -/
theorem ndig_mov_Q1_T {s : Machine}
    (hpc : s.pc = 591)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 591 ≤ k → k < 603 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 603 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 21 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 21 = s.mem.get 21 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 591 :=
    hpc.trans (rfl : (591 : Word) = UInt16.ofNat 591)
  have g (k : Nat) (h1 : 591 ≤ k) (h2 : k < 603) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (591 + off) :=
    word_pc_off 591 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk036[15]! = 18 := rfl
    exact (g 591 (by decide) (by decide)).trans ((cell576 15 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk037[0]! = 18 := rfl
    exact (g 592 (by decide) (by decide)).trans ((cell592 0 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk037[1]! = 594 := rfl
    have hv : (594 : Word) = UInt16.ofNat 594 := rfl
    exact (g 593 (by decide) (by decide)).trans ((cell592 1 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 21 := by
    rw [poff 3 (by decide)]
    have hval : decChunk037[2]! = 21 := rfl
    exact (g 594 (by decide) (by decide)).trans ((cell592 2 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk037[3]! = 0 := rfl
    exact (g 595 (by decide) (by decide)).trans ((cell592 3 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk037[4]! = 597 := rfl
    have hv : (597 : Word) = UInt16.ofNat 597 := rfl
    exact (g 596 (by decide) (by decide)).trans ((cell592 4 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk037[5]! = 0 := rfl
    exact (g 597 (by decide) (by decide)).trans ((cell592 5 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk037[6]! = 18 := rfl
    exact (g 598 (by decide) (by decide)).trans ((cell592 6 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk037[7]! = 600 := rfl
    have hv : (600 : Word) = UInt16.ofNat 600 := rfl
    exact (g 599 (by decide) (by decide)).trans ((cell592 7 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk037[8]! = 0 := rfl
    exact (g 600 (by decide) (by decide)).trans ((cell592 8 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk037[9]! = 0 := rfl
    exact (g 601 (by decide) (by decide)).trans ((cell592 9 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk037[10]! = 603 := rfl
    have hv : (603 : Word) = UInt16.ofNat 603 := rfl
    exact (g 602 (by decide) (by decide)).trans ((cell592 10 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 591 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 591 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 21) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 603 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (603 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 603 = (603 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- SUB K48 T at pc 603. -/
theorem ndig_sub_K48_T_603 {s : Machine}
    (hpc : s.pc = 603)
    (hh : s.halted = false)
    (hK48 : s.mem.get 8 = 48)
    (hcode : ∀ k : Nat, 603 ≤ k → k < 606 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - 48)
        pc := 606 } := by
  have hp : s.pc = UInt16.ofNat 603 :=
    hpc.trans (rfl : (603 : Word) = UInt16.ofNat 603)
  have g (k : Nat) (h1 : 603 ≤ k) (h2 : k < 606) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 8 := by
    rw [hp]
    have hval : decChunk037[11]! = 8 := rfl
    exact (g 603 (by decide) (by decide)).trans ((cell592 11 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (604 : Word) := by simp [hpc]
    rw [this, (rfl : (604 : Word) = UInt16.ofNat 604)]
    have hval : decChunk037[12]! = 18 := rfl
    exact (g 604 (by decide) (by decide)).trans ((cell592 12 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (605 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (606 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (605 : Word) = UInt16.ofNat 605)]
    have hval : decChunk037[13]! = 606 := rfl
    have hv : (606 : Word) = UInt16.ofNat 606 := rfl
    exact (g 605 (by decide) (by decide)).trans ((cell592 13 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 8) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (606 : Word) := by simp [hpc]
  have hmem : s.mem.get 18 - s.mem.get 8 = s.mem.get 18 - 48 := by
    simp [hK48]
  rw [hsub, hpc', hmem]

/-- JLEZ T S2 at pc 606. -/
theorem ndig_enc_jlez_606 {s : Machine}
    (hpc : s.pc = 606)
    (hcode : ∀ k : Nat, 606 ≤ k → k < 606+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 612 := by
  have hp : s.pc = UInt16.ofNat 606 :=
    hpc.trans (rfl : (606 : Word) = UInt16.ofNat 606)
  have g (k : Nat) (h1 : 606 ≤ k) (h2 : k < 606+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk037[14]! = 0 := rfl
    exact (g 606 (by decide) (by decide)).trans ((cell592 14 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (607 : Word) := by simp [hpc]
    rw [this, (rfl : (607 : Word) = UInt16.ofNat 607)]
    have hval : decChunk037[15]! = 18 := rfl
    exact (g 607 (by decide) (by decide)).trans ((cell592 15 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 612 := by
    have : s.pc + 2 = (608 : Word) := by simp [hpc]
    rw [this, (rfl : (608 : Word) = UInt16.ofNat 608)]
    have hval : decChunk038[0]! = 612 := rfl
    exact (g 608 (by decide) (by decide)).trans ((cell608 0 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP FOUR at pc 609. -/
theorem ndig_enc_jmp_609 {s : Machine}
    (hpc : s.pc = 609)
    (hcode : ∀ k : Nat, 609 ≤ k → k < 609+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 720 := by
  have hp : s.pc = UInt16.ofNat 609 :=
    hpc.trans (rfl : (609 : Word) = UInt16.ofNat 609)
  have g (k : Nat) (h1 : 609 ≤ k) (h2 : k < 609+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk038[1]! = 0 := rfl
    exact (g 609 (by decide) (by decide)).trans ((cell608 1 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (610 : Word) := by simp [hpc]
    rw [this, (rfl : (610 : Word) = UInt16.ofNat 610)]
    have hval : decChunk038[2]! = 0 := rfl
    exact (g 610 (by decide) (by decide)).trans ((cell608 2 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 720 := by
    have : s.pc + 2 = (611 : Word) := by simp [hpc]
    rw [this, (rfl : (611 : Word) = UInt16.ofNat 611)]
    have hval : decChunk038[3]! = 720 := rfl
    exact (g 611 (by decide) (by decide)).trans ((cell608 3 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV Q2 T at S2 (pc 612), 4 steps to 624. -/
theorem ndig_mov_Q2_T {s : Machine}
    (hpc : s.pc = 612)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 612 ≤ k → k < 624 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 624 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 22 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 22 = s.mem.get 22 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 612 :=
    hpc.trans (rfl : (612 : Word) = UInt16.ofNat 612)
  have g (k : Nat) (h1 : 612 ≤ k) (h2 : k < 624) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (612 + off) :=
    word_pc_off 612 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk038[4]! = 18 := rfl
    exact (g 612 (by decide) (by decide)).trans ((cell608 4 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk038[5]! = 18 := rfl
    exact (g 613 (by decide) (by decide)).trans ((cell608 5 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk038[6]! = 615 := rfl
    have hv : (615 : Word) = UInt16.ofNat 615 := rfl
    exact (g 614 (by decide) (by decide)).trans ((cell608 6 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 22 := by
    rw [poff 3 (by decide)]
    have hval : decChunk038[7]! = 22 := rfl
    exact (g 615 (by decide) (by decide)).trans ((cell608 7 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk038[8]! = 0 := rfl
    exact (g 616 (by decide) (by decide)).trans ((cell608 8 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk038[9]! = 618 := rfl
    have hv : (618 : Word) = UInt16.ofNat 618 := rfl
    exact (g 617 (by decide) (by decide)).trans ((cell608 9 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk038[10]! = 0 := rfl
    exact (g 618 (by decide) (by decide)).trans ((cell608 10 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk038[11]! = 18 := rfl
    exact (g 619 (by decide) (by decide)).trans ((cell608 11 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk038[12]! = 621 := rfl
    have hv : (621 : Word) = UInt16.ofNat 621 := rfl
    exact (g 620 (by decide) (by decide)).trans ((cell608 12 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk038[13]! = 0 := rfl
    exact (g 621 (by decide) (by decide)).trans ((cell608 13 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk038[14]! = 0 := rfl
    exact (g 622 (by decide) (by decide)).trans ((cell608 14 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk038[15]! = 624 := rfl
    have hv : (624 : Word) = UInt16.ofNat 624 := rfl
    exact (g 623 (by decide) (by decide)).trans ((cell608 15 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 612 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 612 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 22) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 624 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (624 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 624 = (624 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- SUB K48 T at pc 624. -/
theorem ndig_sub_K48_T_624 {s : Machine}
    (hpc : s.pc = 624)
    (hh : s.halted = false)
    (hK48 : s.mem.get 8 = 48)
    (hcode : ∀ k : Nat, 624 ≤ k → k < 627 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - 48)
        pc := 627 } := by
  have hp : s.pc = UInt16.ofNat 624 :=
    hpc.trans (rfl : (624 : Word) = UInt16.ofNat 624)
  have g (k : Nat) (h1 : 624 ≤ k) (h2 : k < 627) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 8 := by
    rw [hp]
    have hval : decChunk039[0]! = 8 := rfl
    exact (g 624 (by decide) (by decide)).trans ((cell624 0 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (625 : Word) := by simp [hpc]
    rw [this, (rfl : (625 : Word) = UInt16.ofNat 625)]
    have hval : decChunk039[1]! = 18 := rfl
    exact (g 625 (by decide) (by decide)).trans ((cell624 1 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (626 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (627 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (626 : Word) = UInt16.ofNat 626)]
    have hval : decChunk039[2]! = 627 := rfl
    have hv : (627 : Word) = UInt16.ofNat 627 := rfl
    exact (g 626 (by decide) (by decide)).trans ((cell624 2 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 8) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (627 : Word) := by simp [hpc]
  have hmem : s.mem.get 18 - s.mem.get 8 = s.mem.get 18 - 48 := by
    simp [hK48]
  rw [hsub, hpc', hmem]

/-- JLEZ T S3 at pc 627. -/
theorem ndig_enc_jlez_627 {s : Machine}
    (hpc : s.pc = 627)
    (hcode : ∀ k : Nat, 627 ≤ k → k < 627+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 633 := by
  have hp : s.pc = UInt16.ofNat 627 :=
    hpc.trans (rfl : (627 : Word) = UInt16.ofNat 627)
  have g (k : Nat) (h1 : 627 ≤ k) (h2 : k < 627+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk039[3]! = 0 := rfl
    exact (g 627 (by decide) (by decide)).trans ((cell624 3 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (628 : Word) := by simp [hpc]
    rw [this, (rfl : (628 : Word) = UInt16.ofNat 628)]
    have hval : decChunk039[4]! = 18 := rfl
    exact (g 628 (by decide) (by decide)).trans ((cell624 4 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 633 := by
    have : s.pc + 2 = (629 : Word) := by simp [hpc]
    rw [this, (rfl : (629 : Word) = UInt16.ofNat 629)]
    have hval : decChunk039[5]! = 633 := rfl
    exact (g 629 (by decide) (by decide)).trans ((cell624 5 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP THREE at pc 630. -/
theorem ndig_enc_jmp_630 {s : Machine}
    (hpc : s.pc = 630)
    (hcode : ∀ k : Nat, 630 ≤ k → k < 630+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 774 := by
  have hp : s.pc = UInt16.ofNat 630 :=
    hpc.trans (rfl : (630 : Word) = UInt16.ofNat 630)
  have g (k : Nat) (h1 : 630 ≤ k) (h2 : k < 630+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk039[6]! = 0 := rfl
    exact (g 630 (by decide) (by decide)).trans ((cell624 6 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (631 : Word) := by simp [hpc]
    rw [this, (rfl : (631 : Word) = UInt16.ofNat 631)]
    have hval : decChunk039[7]! = 0 := rfl
    exact (g 631 (by decide) (by decide)).trans ((cell624 7 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 774 := by
    have : s.pc + 2 = (632 : Word) := by simp [hpc]
    rw [this, (rfl : (632 : Word) = UInt16.ofNat 632)]
    have hval : decChunk039[8]! = 774 := rfl
    exact (g 632 (by decide) (by decide)).trans ((cell624 8 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV Q3 T at S3 (pc 633), 4 steps to 645. -/
theorem ndig_mov_Q3_T {s : Machine}
    (hpc : s.pc = 633)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 633 ≤ k → k < 645 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 645 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 23 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 23 = s.mem.get 23 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 633 :=
    hpc.trans (rfl : (633 : Word) = UInt16.ofNat 633)
  have g (k : Nat) (h1 : 633 ≤ k) (h2 : k < 645) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (633 + off) :=
    word_pc_off 633 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk039[9]! = 18 := rfl
    exact (g 633 (by decide) (by decide)).trans ((cell624 9 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk039[10]! = 18 := rfl
    exact (g 634 (by decide) (by decide)).trans ((cell624 10 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk039[11]! = 636 := rfl
    have hv : (636 : Word) = UInt16.ofNat 636 := rfl
    exact (g 635 (by decide) (by decide)).trans ((cell624 11 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 23 := by
    rw [poff 3 (by decide)]
    have hval : decChunk039[12]! = 23 := rfl
    exact (g 636 (by decide) (by decide)).trans ((cell624 12 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk039[13]! = 0 := rfl
    exact (g 637 (by decide) (by decide)).trans ((cell624 13 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk039[14]! = 639 := rfl
    have hv : (639 : Word) = UInt16.ofNat 639 := rfl
    exact (g 638 (by decide) (by decide)).trans ((cell624 14 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk039[15]! = 0 := rfl
    exact (g 639 (by decide) (by decide)).trans ((cell624 15 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk040[0]! = 18 := rfl
    exact (g 640 (by decide) (by decide)).trans ((cell640 0 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk040[1]! = 642 := rfl
    have hv : (642 : Word) = UInt16.ofNat 642 := rfl
    exact (g 641 (by decide) (by decide)).trans ((cell640 1 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk040[2]! = 0 := rfl
    exact (g 642 (by decide) (by decide)).trans ((cell640 2 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk040[3]! = 0 := rfl
    exact (g 643 (by decide) (by decide)).trans ((cell640 3 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk040[4]! = 645 := rfl
    have hv : (645 : Word) = UInt16.ofNat 645 := rfl
    exact (g 644 (by decide) (by decide)).trans ((cell640 4 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 633 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 633 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 23) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 645 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (645 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 645 = (645 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- SUB K48 T at pc 645. -/
theorem ndig_sub_K48_T_645 {s : Machine}
    (hpc : s.pc = 645)
    (hh : s.halted = false)
    (hK48 : s.mem.get 8 = 48)
    (hcode : ∀ k : Nat, 645 ≤ k → k < 648 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - 48)
        pc := 648 } := by
  have hp : s.pc = UInt16.ofNat 645 :=
    hpc.trans (rfl : (645 : Word) = UInt16.ofNat 645)
  have g (k : Nat) (h1 : 645 ≤ k) (h2 : k < 648) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 8 := by
    rw [hp]
    have hval : decChunk040[5]! = 8 := rfl
    exact (g 645 (by decide) (by decide)).trans ((cell640 5 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (646 : Word) := by simp [hpc]
    rw [this, (rfl : (646 : Word) = UInt16.ofNat 646)]
    have hval : decChunk040[6]! = 18 := rfl
    exact (g 646 (by decide) (by decide)).trans ((cell640 6 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (647 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (648 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (647 : Word) = UInt16.ofNat 647)]
    have hval : decChunk040[7]! = 648 := rfl
    have hv : (648 : Word) = UInt16.ofNat 648 := rfl
    exact (g 647 (by decide) (by decide)).trans ((cell640 7 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 8) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (648 : Word) := by simp [hpc]
  have hmem : s.mem.get 18 - s.mem.get 8 = s.mem.get 18 - 48 := by
    simp [hK48]
  rw [hsub, hpc', hmem]

/-- JLEZ T S4 at pc 648. -/
theorem ndig_enc_jlez_648 {s : Machine}
    (hpc : s.pc = 648)
    (hcode : ∀ k : Nat, 648 ≤ k → k < 648+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 654 := by
  have hp : s.pc = UInt16.ofNat 648 :=
    hpc.trans (rfl : (648 : Word) = UInt16.ofNat 648)
  have g (k : Nat) (h1 : 648 ≤ k) (h2 : k < 648+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk040[8]! = 0 := rfl
    exact (g 648 (by decide) (by decide)).trans ((cell640 8 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (649 : Word) := by simp [hpc]
    rw [this, (rfl : (649 : Word) = UInt16.ofNat 649)]
    have hval : decChunk040[9]! = 18 := rfl
    exact (g 649 (by decide) (by decide)).trans ((cell640 9 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 654 := by
    have : s.pc + 2 = (650 : Word) := by simp [hpc]
    rw [this, (rfl : (650 : Word) = UInt16.ofNat 650)]
    have hval : decChunk040[10]! = 654 := rfl
    exact (g 650 (by decide) (by decide)).trans ((cell640 10 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP TWO at pc 651. -/
theorem ndig_enc_jmp_651 {s : Machine}
    (hpc : s.pc = 651)
    (hcode : ∀ k : Nat, 651 ≤ k → k < 651+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 819 := by
  have hp : s.pc = UInt16.ofNat 651 :=
    hpc.trans (rfl : (651 : Word) = UInt16.ofNat 651)
  have g (k : Nat) (h1 : 651 ≤ k) (h2 : k < 651+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk040[11]! = 0 := rfl
    exact (g 651 (by decide) (by decide)).trans ((cell640 11 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (652 : Word) := by simp [hpc]
    rw [this, (rfl : (652 : Word) = UInt16.ofNat 652)]
    have hval : decChunk040[12]! = 0 := rfl
    exact (g 652 (by decide) (by decide)).trans ((cell640 12 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 819 := by
    have : s.pc + 2 = (653 : Word) := by simp [hpc]
    rw [this, (rfl : (653 : Word) = UInt16.ofNat 653)]
    have hval : decChunk040[13]! = 819 := rfl
    exact (g 653 (by decide) (by decide)).trans ((cell640 13 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP ONE_DIG at S4 (pc 654). -/
theorem ndig_enc_jmp_654 {s : Machine}
    (hpc : s.pc = 654)
    (hcode : ∀ k : Nat, 654 ≤ k → k < 654+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 855 := by
  have hp : s.pc = UInt16.ofNat 654 :=
    hpc.trans (rfl : (654 : Word) = UInt16.ofNat 654)
  have g (k : Nat) (h1 : 654 ≤ k) (h2 : k < 654+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk040[14]! = 0 := rfl
    exact (g 654 (by decide) (by decide)).trans ((cell640 14 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (655 : Word) := by simp [hpc]
    rw [this, (rfl : (655 : Word) = UInt16.ofNat 655)]
    have hval : decChunk040[15]! = 0 := rfl
    exact (g 655 (by decide) (by decide)).trans ((cell640 15 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 855 := by
    have : s.pc + 2 = (656 : Word) := by simp [hpc]
    rw [this, (rfl : (656 : Word) = UInt16.ofNat 656)]
    have hval : decChunk041[0]! = 855 := rfl
    exact (g 656 (by decide) (by decide)).trans ((cell656 0 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV ONE TMP at FIVE (pc 657). -/
theorem ndig_five_mov_ONE_TMP {s : Machine}
    (hpc : s.pc = 657)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 657 ≤ k → k < 669 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 669 ∧
    s4.halted = false ∧
    s4.mem.get 31 = s.mem.get 3 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 3 = s.mem.get 3 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 657 :=
    hpc.trans (rfl : (657 : Word) = UInt16.ofNat 657)
  have g (k : Nat) (h1 : 657 ≤ k) (h2 : k < 669) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (657 + off) :=
    word_pc_off 657 off hp (by omega)
  have m0 : s.mem.get s.pc = 31 := by
    rw [hp]
    have hval : decChunk041[1]! = 31 := rfl
    exact (g 657 (by decide) (by decide)).trans ((cell656 1 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 31 := by
    rw [poff 1 (by decide)]
    have hval : decChunk041[2]! = 31 := rfl
    exact (g 658 (by decide) (by decide)).trans ((cell656 2 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk041[3]! = 660 := rfl
    have hv : (660 : Word) = UInt16.ofNat 660 := rfl
    exact (g 659 (by decide) (by decide)).trans ((cell656 3 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 3 := by
    rw [poff 3 (by decide)]
    have hval : decChunk041[4]! = 3 := rfl
    exact (g 660 (by decide) (by decide)).trans ((cell656 4 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk041[5]! = 0 := rfl
    exact (g 661 (by decide) (by decide)).trans ((cell656 5 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk041[6]! = 663 := rfl
    have hv : (663 : Word) = UInt16.ofNat 663 := rfl
    exact (g 662 (by decide) (by decide)).trans ((cell656 6 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk041[7]! = 0 := rfl
    exact (g 663 (by decide) (by decide)).trans ((cell656 7 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 31 := by
    rw [poff 7 (by decide)]
    have hval : decChunk041[8]! = 31 := rfl
    exact (g 664 (by decide) (by decide)).trans ((cell656 8 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk041[9]! = 666 := rfl
    have hv : (666 : Word) = UInt16.ofNat 666 := rfl
    exact (g 665 (by decide) (by decide)).trans ((cell656 9 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk041[10]! = 0 := rfl
    exact (g 666 (by decide) (by decide)).trans ((cell656 10 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk041[11]! = 0 := rfl
    exact (g 667 (by decide) (by decide)).trans ((cell656 11 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk041[12]! = 669 := rfl
    have hv : (669 : Word) = UInt16.ofNat 669 := rfl
    exact (g 668 (by decide) (by decide)).trans ((cell656 12 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 657 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 657 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 669 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (669 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 669 = (669 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- ADD ONE TMP at pc 669 (FIVE, increment 1). -/
theorem ndig_five_inc_TMP_1 {s : Machine}
    (hpc : s.pc = 669)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 669 ≤ k → k < 678 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 678 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 669 :=
    hpc.trans (rfl : (669 : Word) = UInt16.ofNat 669)
  have g (k : Nat) (h1 : 669 ≤ k) (h2 : k < 678) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (669 + off) :=
    word_pc_off 669 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk041[13]! = 3 := rfl
    exact (g 669 (by decide) (by decide)).trans ((cell656 13 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk041[14]! = 0 := rfl
    exact (g 670 (by decide) (by decide)).trans ((cell656 14 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk041[15]! = 672 := rfl
    have hv : (672 : Word) = UInt16.ofNat 672 := rfl
    exact (g 671 (by decide) (by decide)).trans ((cell656 15 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk042[0]! = 0 := rfl
    exact (g 672 (by decide) (by decide)).trans ((cell672 0 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk042[1]! = 31 := rfl
    exact (g 673 (by decide) (by decide)).trans ((cell672 1 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk042[2]! = 675 := rfl
    have hv : (675 : Word) = UInt16.ofNat 675 := rfl
    exact (g 674 (by decide) (by decide)).trans ((cell672 2 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk042[3]! = 0 := rfl
    exact (g 675 (by decide) (by decide)).trans ((cell672 3 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk042[4]! = 0 := rfl
    exact (g 676 (by decide) (by decide)).trans ((cell672 4 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk042[5]! = 678 := rfl
    have hv : (678 : Word) = UInt16.ofNat 678 := rfl
    exact (g 677 (by decide) (by decide)).trans ((cell672 5 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 669 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 669 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 678 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (678 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 678 = (678 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- ADD ONE TMP at pc 678 (FIVE, increment 2). -/
theorem ndig_five_inc_TMP_2 {s : Machine}
    (hpc : s.pc = 678)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 678 ≤ k → k < 687 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 687 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 678 :=
    hpc.trans (rfl : (678 : Word) = UInt16.ofNat 678)
  have g (k : Nat) (h1 : 678 ≤ k) (h2 : k < 687) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (678 + off) :=
    word_pc_off 678 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk042[6]! = 3 := rfl
    exact (g 678 (by decide) (by decide)).trans ((cell672 6 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk042[7]! = 0 := rfl
    exact (g 679 (by decide) (by decide)).trans ((cell672 7 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk042[8]! = 681 := rfl
    have hv : (681 : Word) = UInt16.ofNat 681 := rfl
    exact (g 680 (by decide) (by decide)).trans ((cell672 8 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk042[9]! = 0 := rfl
    exact (g 681 (by decide) (by decide)).trans ((cell672 9 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk042[10]! = 31 := rfl
    exact (g 682 (by decide) (by decide)).trans ((cell672 10 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk042[11]! = 684 := rfl
    have hv : (684 : Word) = UInt16.ofNat 684 := rfl
    exact (g 683 (by decide) (by decide)).trans ((cell672 11 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk042[12]! = 0 := rfl
    exact (g 684 (by decide) (by decide)).trans ((cell672 12 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk042[13]! = 0 := rfl
    exact (g 685 (by decide) (by decide)).trans ((cell672 13 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk042[14]! = 687 := rfl
    have hv : (687 : Word) = UInt16.ofNat 687 := rfl
    exact (g 686 (by decide) (by decide)).trans ((cell672 14 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 678 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 678 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 687 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (687 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 687 = (687 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- ADD ONE TMP at pc 687 (FIVE, increment 3). -/
theorem ndig_five_inc_TMP_3 {s : Machine}
    (hpc : s.pc = 687)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 687 ≤ k → k < 696 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 696 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 687 :=
    hpc.trans (rfl : (687 : Word) = UInt16.ofNat 687)
  have g (k : Nat) (h1 : 687 ≤ k) (h2 : k < 696) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (687 + off) :=
    word_pc_off 687 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk042[15]! = 3 := rfl
    exact (g 687 (by decide) (by decide)).trans ((cell672 15 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk043[0]! = 0 := rfl
    exact (g 688 (by decide) (by decide)).trans ((cell688 0 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk043[1]! = 690 := rfl
    have hv : (690 : Word) = UInt16.ofNat 690 := rfl
    exact (g 689 (by decide) (by decide)).trans ((cell688 1 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk043[2]! = 0 := rfl
    exact (g 690 (by decide) (by decide)).trans ((cell688 2 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk043[3]! = 31 := rfl
    exact (g 691 (by decide) (by decide)).trans ((cell688 3 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk043[4]! = 693 := rfl
    have hv : (693 : Word) = UInt16.ofNat 693 := rfl
    exact (g 692 (by decide) (by decide)).trans ((cell688 4 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk043[5]! = 0 := rfl
    exact (g 693 (by decide) (by decide)).trans ((cell688 5 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk043[6]! = 0 := rfl
    exact (g 694 (by decide) (by decide)).trans ((cell688 6 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk043[7]! = 696 := rfl
    have hv : (696 : Word) = UInt16.ofNat 696 := rfl
    exact (g 695 (by decide) (by decide)).trans ((cell688 7 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 687 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 687 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 696 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (696 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 696 = (696 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- ADD ONE TMP at pc 696 (FIVE, increment 4). -/
theorem ndig_five_inc_TMP_4 {s : Machine}
    (hpc : s.pc = 696)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 696 ≤ k → k < 705 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 705 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 696 :=
    hpc.trans (rfl : (696 : Word) = UInt16.ofNat 696)
  have g (k : Nat) (h1 : 696 ≤ k) (h2 : k < 705) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (696 + off) :=
    word_pc_off 696 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk043[8]! = 3 := rfl
    exact (g 696 (by decide) (by decide)).trans ((cell688 8 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk043[9]! = 0 := rfl
    exact (g 697 (by decide) (by decide)).trans ((cell688 9 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk043[10]! = 699 := rfl
    have hv : (699 : Word) = UInt16.ofNat 699 := rfl
    exact (g 698 (by decide) (by decide)).trans ((cell688 10 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk043[11]! = 0 := rfl
    exact (g 699 (by decide) (by decide)).trans ((cell688 11 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk043[12]! = 31 := rfl
    exact (g 700 (by decide) (by decide)).trans ((cell688 12 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk043[13]! = 702 := rfl
    have hv : (702 : Word) = UInt16.ofNat 702 := rfl
    exact (g 701 (by decide) (by decide)).trans ((cell688 13 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk043[14]! = 0 := rfl
    exact (g 702 (by decide) (by decide)).trans ((cell688 14 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk043[15]! = 0 := rfl
    exact (g 703 (by decide) (by decide)).trans ((cell688 15 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk044[0]! = 705 := rfl
    have hv : (705 : Word) = UInt16.ofNat 705 := rfl
    exact (g 704 (by decide) (by decide)).trans ((cell704 0 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 696 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 696 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 705 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (705 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 705 = (705 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- MOV TMP NDIG at pc 705 (FIVE). -/
theorem ndig_five_mov_TMP_NDIG {s : Machine}
    (hpc : s.pc = 705)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 705 ≤ k → k < 717 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 717 ∧
    s4.halted = false ∧
    s4.mem.get 25 = s.mem.get 31 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 31 = s.mem.get 31 ∧
    (∀ a, a ≠ 25 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 705 :=
    hpc.trans (rfl : (705 : Word) = UInt16.ofNat 705)
  have g (k : Nat) (h1 : 705 ≤ k) (h2 : k < 717) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (705 + off) :=
    word_pc_off 705 off hp (by omega)
  have m0 : s.mem.get s.pc = 25 := by
    rw [hp]
    have hval : decChunk044[1]! = 25 := rfl
    exact (g 705 (by decide) (by decide)).trans ((cell704 1 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 25 := by
    rw [poff 1 (by decide)]
    have hval : decChunk044[2]! = 25 := rfl
    exact (g 706 (by decide) (by decide)).trans ((cell704 2 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk044[3]! = 708 := rfl
    have hv : (708 : Word) = UInt16.ofNat 708 := rfl
    exact (g 707 (by decide) (by decide)).trans ((cell704 3 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 31 := by
    rw [poff 3 (by decide)]
    have hval : decChunk044[4]! = 31 := rfl
    exact (g 708 (by decide) (by decide)).trans ((cell704 4 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk044[5]! = 0 := rfl
    exact (g 709 (by decide) (by decide)).trans ((cell704 5 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk044[6]! = 711 := rfl
    have hv : (711 : Word) = UInt16.ofNat 711 := rfl
    exact (g 710 (by decide) (by decide)).trans ((cell704 6 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk044[7]! = 0 := rfl
    exact (g 711 (by decide) (by decide)).trans ((cell704 7 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 25 := by
    rw [poff 7 (by decide)]
    have hval : decChunk044[8]! = 25 := rfl
    exact (g 712 (by decide) (by decide)).trans ((cell704 8 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk044[9]! = 714 := rfl
    have hv : (714 : Word) = UInt16.ofNat 714 := rfl
    exact (g 713 (by decide) (by decide)).trans ((cell704 9 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk044[10]! = 0 := rfl
    exact (g 714 (by decide) (by decide)).trans ((cell704 10 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk044[11]! = 0 := rfl
    exact (g 715 (by decide) (by decide)).trans ((cell704 11 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk044[12]! = 717 := rfl
    have hv : (717 : Word) = UInt16.ofNat 717 := rfl
    exact (g 716 (by decide) (by decide)).trans ((cell704 12 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (25 : Word) := by
    intro i hi
    have : (25 : Word) = UInt16.ofNat 25 := rfl
    rw [this]
    exact pc_off_ne 705 i 25 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 705 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 31) (dst := 25)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 717 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (717 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 717 = (717 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP HAVE_DIG at pc 717 (FIVE). -/
theorem ndig_enc_jmp_717 {s : Machine}
    (hpc : s.pc = 717)
    (hcode : ∀ k : Nat, 717 ≤ k → k < 717+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 867 := by
  have hp : s.pc = UInt16.ofNat 717 :=
    hpc.trans (rfl : (717 : Word) = UInt16.ofNat 717)
  have g (k : Nat) (h1 : 717 ≤ k) (h2 : k < 717+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk044[13]! = 0 := rfl
    exact (g 717 (by decide) (by decide)).trans ((cell704 13 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (718 : Word) := by simp [hpc]
    rw [this, (rfl : (718 : Word) = UInt16.ofNat 718)]
    have hval : decChunk044[14]! = 0 := rfl
    exact (g 718 (by decide) (by decide)).trans ((cell704 14 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 867 := by
    have : s.pc + 2 = (719 : Word) := by simp [hpc]
    rw [this, (rfl : (719 : Word) = UInt16.ofNat 719)]
    have hval : decChunk044[15]! = 867 := rfl
    exact (g 719 (by decide) (by decide)).trans ((cell704 15 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV ONE TMP at FOUR (pc 720). -/
theorem ndig_four_mov_ONE_TMP {s : Machine}
    (hpc : s.pc = 720)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 720 ≤ k → k < 732 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 732 ∧
    s4.halted = false ∧
    s4.mem.get 31 = s.mem.get 3 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 3 = s.mem.get 3 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 720 :=
    hpc.trans (rfl : (720 : Word) = UInt16.ofNat 720)
  have g (k : Nat) (h1 : 720 ≤ k) (h2 : k < 732) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (720 + off) :=
    word_pc_off 720 off hp (by omega)
  have m0 : s.mem.get s.pc = 31 := by
    rw [hp]
    have hval : decChunk045[0]! = 31 := rfl
    exact (g 720 (by decide) (by decide)).trans ((cell720 0 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 31 := by
    rw [poff 1 (by decide)]
    have hval : decChunk045[1]! = 31 := rfl
    exact (g 721 (by decide) (by decide)).trans ((cell720 1 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk045[2]! = 723 := rfl
    have hv : (723 : Word) = UInt16.ofNat 723 := rfl
    exact (g 722 (by decide) (by decide)).trans ((cell720 2 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 3 := by
    rw [poff 3 (by decide)]
    have hval : decChunk045[3]! = 3 := rfl
    exact (g 723 (by decide) (by decide)).trans ((cell720 3 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk045[4]! = 0 := rfl
    exact (g 724 (by decide) (by decide)).trans ((cell720 4 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk045[5]! = 726 := rfl
    have hv : (726 : Word) = UInt16.ofNat 726 := rfl
    exact (g 725 (by decide) (by decide)).trans ((cell720 5 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk045[6]! = 0 := rfl
    exact (g 726 (by decide) (by decide)).trans ((cell720 6 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 31 := by
    rw [poff 7 (by decide)]
    have hval : decChunk045[7]! = 31 := rfl
    exact (g 727 (by decide) (by decide)).trans ((cell720 7 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk045[8]! = 729 := rfl
    have hv : (729 : Word) = UInt16.ofNat 729 := rfl
    exact (g 728 (by decide) (by decide)).trans ((cell720 8 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk045[9]! = 0 := rfl
    exact (g 729 (by decide) (by decide)).trans ((cell720 9 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk045[10]! = 0 := rfl
    exact (g 730 (by decide) (by decide)).trans ((cell720 10 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk045[11]! = 732 := rfl
    have hv : (732 : Word) = UInt16.ofNat 732 := rfl
    exact (g 731 (by decide) (by decide)).trans ((cell720 11 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 720 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 720 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 732 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (732 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 732 = (732 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- ADD ONE TMP at pc 732 (FOUR, increment 1). -/
theorem ndig_four_inc_TMP_1 {s : Machine}
    (hpc : s.pc = 732)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 732 ≤ k → k < 741 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 741 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 732 :=
    hpc.trans (rfl : (732 : Word) = UInt16.ofNat 732)
  have g (k : Nat) (h1 : 732 ≤ k) (h2 : k < 741) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (732 + off) :=
    word_pc_off 732 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk045[12]! = 3 := rfl
    exact (g 732 (by decide) (by decide)).trans ((cell720 12 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk045[13]! = 0 := rfl
    exact (g 733 (by decide) (by decide)).trans ((cell720 13 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk045[14]! = 735 := rfl
    have hv : (735 : Word) = UInt16.ofNat 735 := rfl
    exact (g 734 (by decide) (by decide)).trans ((cell720 14 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk045[15]! = 0 := rfl
    exact (g 735 (by decide) (by decide)).trans ((cell720 15 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk046[0]! = 31 := rfl
    exact (g 736 (by decide) (by decide)).trans ((cell736 0 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk046[1]! = 738 := rfl
    have hv : (738 : Word) = UInt16.ofNat 738 := rfl
    exact (g 737 (by decide) (by decide)).trans ((cell736 1 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk046[2]! = 0 := rfl
    exact (g 738 (by decide) (by decide)).trans ((cell736 2 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk046[3]! = 0 := rfl
    exact (g 739 (by decide) (by decide)).trans ((cell736 3 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk046[4]! = 741 := rfl
    have hv : (741 : Word) = UInt16.ofNat 741 := rfl
    exact (g 740 (by decide) (by decide)).trans ((cell736 4 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 732 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 732 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 741 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (741 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 741 = (741 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- ADD ONE TMP at pc 741 (FOUR, increment 2). -/
theorem ndig_four_inc_TMP_2 {s : Machine}
    (hpc : s.pc = 741)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 741 ≤ k → k < 750 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 750 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 741 :=
    hpc.trans (rfl : (741 : Word) = UInt16.ofNat 741)
  have g (k : Nat) (h1 : 741 ≤ k) (h2 : k < 750) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (741 + off) :=
    word_pc_off 741 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk046[5]! = 3 := rfl
    exact (g 741 (by decide) (by decide)).trans ((cell736 5 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk046[6]! = 0 := rfl
    exact (g 742 (by decide) (by decide)).trans ((cell736 6 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk046[7]! = 744 := rfl
    have hv : (744 : Word) = UInt16.ofNat 744 := rfl
    exact (g 743 (by decide) (by decide)).trans ((cell736 7 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk046[8]! = 0 := rfl
    exact (g 744 (by decide) (by decide)).trans ((cell736 8 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk046[9]! = 31 := rfl
    exact (g 745 (by decide) (by decide)).trans ((cell736 9 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk046[10]! = 747 := rfl
    have hv : (747 : Word) = UInt16.ofNat 747 := rfl
    exact (g 746 (by decide) (by decide)).trans ((cell736 10 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk046[11]! = 0 := rfl
    exact (g 747 (by decide) (by decide)).trans ((cell736 11 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk046[12]! = 0 := rfl
    exact (g 748 (by decide) (by decide)).trans ((cell736 12 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk046[13]! = 750 := rfl
    have hv : (750 : Word) = UInt16.ofNat 750 := rfl
    exact (g 749 (by decide) (by decide)).trans ((cell736 13 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 741 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 741 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 750 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (750 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 750 = (750 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- ADD ONE TMP at pc 750 (FOUR, increment 3). -/
theorem ndig_four_inc_TMP_3 {s : Machine}
    (hpc : s.pc = 750)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 750 ≤ k → k < 759 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 759 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 750 :=
    hpc.trans (rfl : (750 : Word) = UInt16.ofNat 750)
  have g (k : Nat) (h1 : 750 ≤ k) (h2 : k < 759) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (750 + off) :=
    word_pc_off 750 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk046[14]! = 3 := rfl
    exact (g 750 (by decide) (by decide)).trans ((cell736 14 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk046[15]! = 0 := rfl
    exact (g 751 (by decide) (by decide)).trans ((cell736 15 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk047[0]! = 753 := rfl
    have hv : (753 : Word) = UInt16.ofNat 753 := rfl
    exact (g 752 (by decide) (by decide)).trans ((cell752 0 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk047[1]! = 0 := rfl
    exact (g 753 (by decide) (by decide)).trans ((cell752 1 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk047[2]! = 31 := rfl
    exact (g 754 (by decide) (by decide)).trans ((cell752 2 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk047[3]! = 756 := rfl
    have hv : (756 : Word) = UInt16.ofNat 756 := rfl
    exact (g 755 (by decide) (by decide)).trans ((cell752 3 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk047[4]! = 0 := rfl
    exact (g 756 (by decide) (by decide)).trans ((cell752 4 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk047[5]! = 0 := rfl
    exact (g 757 (by decide) (by decide)).trans ((cell752 5 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk047[6]! = 759 := rfl
    have hv : (759 : Word) = UInt16.ofNat 759 := rfl
    exact (g 758 (by decide) (by decide)).trans ((cell752 6 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 750 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 750 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 759 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (759 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 759 = (759 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- MOV TMP NDIG at pc 759 (FOUR). -/
theorem ndig_four_mov_TMP_NDIG {s : Machine}
    (hpc : s.pc = 759)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 759 ≤ k → k < 771 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 771 ∧
    s4.halted = false ∧
    s4.mem.get 25 = s.mem.get 31 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 31 = s.mem.get 31 ∧
    (∀ a, a ≠ 25 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 759 :=
    hpc.trans (rfl : (759 : Word) = UInt16.ofNat 759)
  have g (k : Nat) (h1 : 759 ≤ k) (h2 : k < 771) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (759 + off) :=
    word_pc_off 759 off hp (by omega)
  have m0 : s.mem.get s.pc = 25 := by
    rw [hp]
    have hval : decChunk047[7]! = 25 := rfl
    exact (g 759 (by decide) (by decide)).trans ((cell752 7 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 25 := by
    rw [poff 1 (by decide)]
    have hval : decChunk047[8]! = 25 := rfl
    exact (g 760 (by decide) (by decide)).trans ((cell752 8 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk047[9]! = 762 := rfl
    have hv : (762 : Word) = UInt16.ofNat 762 := rfl
    exact (g 761 (by decide) (by decide)).trans ((cell752 9 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 31 := by
    rw [poff 3 (by decide)]
    have hval : decChunk047[10]! = 31 := rfl
    exact (g 762 (by decide) (by decide)).trans ((cell752 10 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk047[11]! = 0 := rfl
    exact (g 763 (by decide) (by decide)).trans ((cell752 11 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk047[12]! = 765 := rfl
    have hv : (765 : Word) = UInt16.ofNat 765 := rfl
    exact (g 764 (by decide) (by decide)).trans ((cell752 12 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk047[13]! = 0 := rfl
    exact (g 765 (by decide) (by decide)).trans ((cell752 13 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 25 := by
    rw [poff 7 (by decide)]
    have hval : decChunk047[14]! = 25 := rfl
    exact (g 766 (by decide) (by decide)).trans ((cell752 14 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk047[15]! = 768 := rfl
    have hv : (768 : Word) = UInt16.ofNat 768 := rfl
    exact (g 767 (by decide) (by decide)).trans ((cell752 15 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk048[0]! = 0 := rfl
    exact (g 768 (by decide) (by decide)).trans ((cell768 0 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk048[1]! = 0 := rfl
    exact (g 769 (by decide) (by decide)).trans ((cell768 1 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk048[2]! = 771 := rfl
    have hv : (771 : Word) = UInt16.ofNat 771 := rfl
    exact (g 770 (by decide) (by decide)).trans ((cell768 2 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (25 : Word) := by
    intro i hi
    have : (25 : Word) = UInt16.ofNat 25 := rfl
    rw [this]
    exact pc_off_ne 759 i 25 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 759 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 31) (dst := 25)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 771 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (771 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 771 = (771 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP HAVE_DIG at pc 771 (FOUR). -/
theorem ndig_enc_jmp_771 {s : Machine}
    (hpc : s.pc = 771)
    (hcode : ∀ k : Nat, 771 ≤ k → k < 771+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 867 := by
  have hp : s.pc = UInt16.ofNat 771 :=
    hpc.trans (rfl : (771 : Word) = UInt16.ofNat 771)
  have g (k : Nat) (h1 : 771 ≤ k) (h2 : k < 771+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk048[3]! = 0 := rfl
    exact (g 771 (by decide) (by decide)).trans ((cell768 3 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (772 : Word) := by simp [hpc]
    rw [this, (rfl : (772 : Word) = UInt16.ofNat 772)]
    have hval : decChunk048[4]! = 0 := rfl
    exact (g 772 (by decide) (by decide)).trans ((cell768 4 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 867 := by
    have : s.pc + 2 = (773 : Word) := by simp [hpc]
    rw [this, (rfl : (773 : Word) = UInt16.ofNat 773)]
    have hval : decChunk048[5]! = 867 := rfl
    exact (g 773 (by decide) (by decide)).trans ((cell768 5 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV ONE TMP at THREE (pc 774). -/
theorem ndig_three_mov_ONE_TMP {s : Machine}
    (hpc : s.pc = 774)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 774 ≤ k → k < 786 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 786 ∧
    s4.halted = false ∧
    s4.mem.get 31 = s.mem.get 3 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 3 = s.mem.get 3 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 774 :=
    hpc.trans (rfl : (774 : Word) = UInt16.ofNat 774)
  have g (k : Nat) (h1 : 774 ≤ k) (h2 : k < 786) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (774 + off) :=
    word_pc_off 774 off hp (by omega)
  have m0 : s.mem.get s.pc = 31 := by
    rw [hp]
    have hval : decChunk048[6]! = 31 := rfl
    exact (g 774 (by decide) (by decide)).trans ((cell768 6 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 31 := by
    rw [poff 1 (by decide)]
    have hval : decChunk048[7]! = 31 := rfl
    exact (g 775 (by decide) (by decide)).trans ((cell768 7 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk048[8]! = 777 := rfl
    have hv : (777 : Word) = UInt16.ofNat 777 := rfl
    exact (g 776 (by decide) (by decide)).trans ((cell768 8 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 3 := by
    rw [poff 3 (by decide)]
    have hval : decChunk048[9]! = 3 := rfl
    exact (g 777 (by decide) (by decide)).trans ((cell768 9 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk048[10]! = 0 := rfl
    exact (g 778 (by decide) (by decide)).trans ((cell768 10 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk048[11]! = 780 := rfl
    have hv : (780 : Word) = UInt16.ofNat 780 := rfl
    exact (g 779 (by decide) (by decide)).trans ((cell768 11 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk048[12]! = 0 := rfl
    exact (g 780 (by decide) (by decide)).trans ((cell768 12 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 31 := by
    rw [poff 7 (by decide)]
    have hval : decChunk048[13]! = 31 := rfl
    exact (g 781 (by decide) (by decide)).trans ((cell768 13 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk048[14]! = 783 := rfl
    have hv : (783 : Word) = UInt16.ofNat 783 := rfl
    exact (g 782 (by decide) (by decide)).trans ((cell768 14 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk048[15]! = 0 := rfl
    exact (g 783 (by decide) (by decide)).trans ((cell768 15 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk049[0]! = 0 := rfl
    exact (g 784 (by decide) (by decide)).trans ((cell784 0 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk049[1]! = 786 := rfl
    have hv : (786 : Word) = UInt16.ofNat 786 := rfl
    exact (g 785 (by decide) (by decide)).trans ((cell784 1 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 774 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 774 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 786 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (786 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 786 = (786 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- ADD ONE TMP at pc 786 (THREE, increment 1). -/
theorem ndig_three_inc_TMP_1 {s : Machine}
    (hpc : s.pc = 786)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 786 ≤ k → k < 795 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 795 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 786 :=
    hpc.trans (rfl : (786 : Word) = UInt16.ofNat 786)
  have g (k : Nat) (h1 : 786 ≤ k) (h2 : k < 795) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (786 + off) :=
    word_pc_off 786 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk049[2]! = 3 := rfl
    exact (g 786 (by decide) (by decide)).trans ((cell784 2 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk049[3]! = 0 := rfl
    exact (g 787 (by decide) (by decide)).trans ((cell784 3 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk049[4]! = 789 := rfl
    have hv : (789 : Word) = UInt16.ofNat 789 := rfl
    exact (g 788 (by decide) (by decide)).trans ((cell784 4 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk049[5]! = 0 := rfl
    exact (g 789 (by decide) (by decide)).trans ((cell784 5 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk049[6]! = 31 := rfl
    exact (g 790 (by decide) (by decide)).trans ((cell784 6 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk049[7]! = 792 := rfl
    have hv : (792 : Word) = UInt16.ofNat 792 := rfl
    exact (g 791 (by decide) (by decide)).trans ((cell784 7 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk049[8]! = 0 := rfl
    exact (g 792 (by decide) (by decide)).trans ((cell784 8 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk049[9]! = 0 := rfl
    exact (g 793 (by decide) (by decide)).trans ((cell784 9 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk049[10]! = 795 := rfl
    have hv : (795 : Word) = UInt16.ofNat 795 := rfl
    exact (g 794 (by decide) (by decide)).trans ((cell784 10 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 786 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 786 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 795 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (795 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 795 = (795 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- ADD ONE TMP at pc 795 (THREE, increment 2). -/
theorem ndig_three_inc_TMP_2 {s : Machine}
    (hpc : s.pc = 795)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 795 ≤ k → k < 804 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 804 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 795 :=
    hpc.trans (rfl : (795 : Word) = UInt16.ofNat 795)
  have g (k : Nat) (h1 : 795 ≤ k) (h2 : k < 804) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (795 + off) :=
    word_pc_off 795 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk049[11]! = 3 := rfl
    exact (g 795 (by decide) (by decide)).trans ((cell784 11 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk049[12]! = 0 := rfl
    exact (g 796 (by decide) (by decide)).trans ((cell784 12 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk049[13]! = 798 := rfl
    have hv : (798 : Word) = UInt16.ofNat 798 := rfl
    exact (g 797 (by decide) (by decide)).trans ((cell784 13 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk049[14]! = 0 := rfl
    exact (g 798 (by decide) (by decide)).trans ((cell784 14 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk049[15]! = 31 := rfl
    exact (g 799 (by decide) (by decide)).trans ((cell784 15 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk050[0]! = 801 := rfl
    have hv : (801 : Word) = UInt16.ofNat 801 := rfl
    exact (g 800 (by decide) (by decide)).trans ((cell800 0 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk050[1]! = 0 := rfl
    exact (g 801 (by decide) (by decide)).trans ((cell800 1 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk050[2]! = 0 := rfl
    exact (g 802 (by decide) (by decide)).trans ((cell800 2 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk050[3]! = 804 := rfl
    have hv : (804 : Word) = UInt16.ofNat 804 := rfl
    exact (g 803 (by decide) (by decide)).trans ((cell800 3 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 795 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 795 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 804 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (804 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 804 = (804 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- MOV TMP NDIG at pc 804 (THREE). -/
theorem ndig_three_mov_TMP_NDIG {s : Machine}
    (hpc : s.pc = 804)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 804 ≤ k → k < 816 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 816 ∧
    s4.halted = false ∧
    s4.mem.get 25 = s.mem.get 31 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 31 = s.mem.get 31 ∧
    (∀ a, a ≠ 25 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 804 :=
    hpc.trans (rfl : (804 : Word) = UInt16.ofNat 804)
  have g (k : Nat) (h1 : 804 ≤ k) (h2 : k < 816) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (804 + off) :=
    word_pc_off 804 off hp (by omega)
  have m0 : s.mem.get s.pc = 25 := by
    rw [hp]
    have hval : decChunk050[4]! = 25 := rfl
    exact (g 804 (by decide) (by decide)).trans ((cell800 4 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 25 := by
    rw [poff 1 (by decide)]
    have hval : decChunk050[5]! = 25 := rfl
    exact (g 805 (by decide) (by decide)).trans ((cell800 5 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk050[6]! = 807 := rfl
    have hv : (807 : Word) = UInt16.ofNat 807 := rfl
    exact (g 806 (by decide) (by decide)).trans ((cell800 6 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 31 := by
    rw [poff 3 (by decide)]
    have hval : decChunk050[7]! = 31 := rfl
    exact (g 807 (by decide) (by decide)).trans ((cell800 7 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk050[8]! = 0 := rfl
    exact (g 808 (by decide) (by decide)).trans ((cell800 8 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk050[9]! = 810 := rfl
    have hv : (810 : Word) = UInt16.ofNat 810 := rfl
    exact (g 809 (by decide) (by decide)).trans ((cell800 9 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk050[10]! = 0 := rfl
    exact (g 810 (by decide) (by decide)).trans ((cell800 10 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 25 := by
    rw [poff 7 (by decide)]
    have hval : decChunk050[11]! = 25 := rfl
    exact (g 811 (by decide) (by decide)).trans ((cell800 11 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk050[12]! = 813 := rfl
    have hv : (813 : Word) = UInt16.ofNat 813 := rfl
    exact (g 812 (by decide) (by decide)).trans ((cell800 12 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk050[13]! = 0 := rfl
    exact (g 813 (by decide) (by decide)).trans ((cell800 13 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk050[14]! = 0 := rfl
    exact (g 814 (by decide) (by decide)).trans ((cell800 14 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk050[15]! = 816 := rfl
    have hv : (816 : Word) = UInt16.ofNat 816 := rfl
    exact (g 815 (by decide) (by decide)).trans ((cell800 15 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (25 : Word) := by
    intro i hi
    have : (25 : Word) = UInt16.ofNat 25 := rfl
    rw [this]
    exact pc_off_ne 804 i 25 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 804 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 31) (dst := 25)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 816 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (816 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 816 = (816 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP HAVE_DIG at pc 816 (THREE). -/
theorem ndig_enc_jmp_816 {s : Machine}
    (hpc : s.pc = 816)
    (hcode : ∀ k : Nat, 816 ≤ k → k < 816+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 867 := by
  have hp : s.pc = UInt16.ofNat 816 :=
    hpc.trans (rfl : (816 : Word) = UInt16.ofNat 816)
  have g (k : Nat) (h1 : 816 ≤ k) (h2 : k < 816+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk051[0]! = 0 := rfl
    exact (g 816 (by decide) (by decide)).trans ((cell816 0 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (817 : Word) := by simp [hpc]
    rw [this, (rfl : (817 : Word) = UInt16.ofNat 817)]
    have hval : decChunk051[1]! = 0 := rfl
    exact (g 817 (by decide) (by decide)).trans ((cell816 1 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 867 := by
    have : s.pc + 2 = (818 : Word) := by simp [hpc]
    rw [this, (rfl : (818 : Word) = UInt16.ofNat 818)]
    have hval : decChunk051[2]! = 867 := rfl
    exact (g 818 (by decide) (by decide)).trans ((cell816 2 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV ONE TMP at TWO (pc 819). -/
theorem ndig_two_mov_ONE_TMP {s : Machine}
    (hpc : s.pc = 819)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 819 ≤ k → k < 831 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 831 ∧
    s4.halted = false ∧
    s4.mem.get 31 = s.mem.get 3 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 3 = s.mem.get 3 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 819 :=
    hpc.trans (rfl : (819 : Word) = UInt16.ofNat 819)
  have g (k : Nat) (h1 : 819 ≤ k) (h2 : k < 831) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (819 + off) :=
    word_pc_off 819 off hp (by omega)
  have m0 : s.mem.get s.pc = 31 := by
    rw [hp]
    have hval : decChunk051[3]! = 31 := rfl
    exact (g 819 (by decide) (by decide)).trans ((cell816 3 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 31 := by
    rw [poff 1 (by decide)]
    have hval : decChunk051[4]! = 31 := rfl
    exact (g 820 (by decide) (by decide)).trans ((cell816 4 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk051[5]! = 822 := rfl
    have hv : (822 : Word) = UInt16.ofNat 822 := rfl
    exact (g 821 (by decide) (by decide)).trans ((cell816 5 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 3 := by
    rw [poff 3 (by decide)]
    have hval : decChunk051[6]! = 3 := rfl
    exact (g 822 (by decide) (by decide)).trans ((cell816 6 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk051[7]! = 0 := rfl
    exact (g 823 (by decide) (by decide)).trans ((cell816 7 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk051[8]! = 825 := rfl
    have hv : (825 : Word) = UInt16.ofNat 825 := rfl
    exact (g 824 (by decide) (by decide)).trans ((cell816 8 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk051[9]! = 0 := rfl
    exact (g 825 (by decide) (by decide)).trans ((cell816 9 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 31 := by
    rw [poff 7 (by decide)]
    have hval : decChunk051[10]! = 31 := rfl
    exact (g 826 (by decide) (by decide)).trans ((cell816 10 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk051[11]! = 828 := rfl
    have hv : (828 : Word) = UInt16.ofNat 828 := rfl
    exact (g 827 (by decide) (by decide)).trans ((cell816 11 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk051[12]! = 0 := rfl
    exact (g 828 (by decide) (by decide)).trans ((cell816 12 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk051[13]! = 0 := rfl
    exact (g 829 (by decide) (by decide)).trans ((cell816 13 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk051[14]! = 831 := rfl
    have hv : (831 : Word) = UInt16.ofNat 831 := rfl
    exact (g 830 (by decide) (by decide)).trans ((cell816 14 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 819 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 819 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 831 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (831 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 831 = (831 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- ADD ONE TMP at pc 831 (TWO). -/
theorem ndig_two_inc_TMP_1 {s : Machine}
    (hpc : s.pc = 831)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 831 ≤ k → k < 840 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 840 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 831 :=
    hpc.trans (rfl : (831 : Word) = UInt16.ofNat 831)
  have g (k : Nat) (h1 : 831 ≤ k) (h2 : k < 840) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (831 + off) :=
    word_pc_off 831 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk051[15]! = 3 := rfl
    exact (g 831 (by decide) (by decide)).trans ((cell816 15 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk052[0]! = 0 := rfl
    exact (g 832 (by decide) (by decide)).trans ((cell832 0 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk052[1]! = 834 := rfl
    have hv : (834 : Word) = UInt16.ofNat 834 := rfl
    exact (g 833 (by decide) (by decide)).trans ((cell832 1 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk052[2]! = 0 := rfl
    exact (g 834 (by decide) (by decide)).trans ((cell832 2 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk052[3]! = 31 := rfl
    exact (g 835 (by decide) (by decide)).trans ((cell832 3 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk052[4]! = 837 := rfl
    have hv : (837 : Word) = UInt16.ofNat 837 := rfl
    exact (g 836 (by decide) (by decide)).trans ((cell832 4 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk052[5]! = 0 := rfl
    exact (g 837 (by decide) (by decide)).trans ((cell832 5 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk052[6]! = 0 := rfl
    exact (g 838 (by decide) (by decide)).trans ((cell832 6 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk052[7]! = 840 := rfl
    have hv : (840 : Word) = UInt16.ofNat 840 := rfl
    exact (g 839 (by decide) (by decide)).trans ((cell832 7 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 831 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 831 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 840 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (840 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 840 = (840 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- MOV TMP NDIG at pc 840 (TWO). -/
theorem ndig_two_mov_TMP_NDIG {s : Machine}
    (hpc : s.pc = 840)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 840 ≤ k → k < 852 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 852 ∧
    s4.halted = false ∧
    s4.mem.get 25 = s.mem.get 31 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 31 = s.mem.get 31 ∧
    (∀ a, a ≠ 25 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 840 :=
    hpc.trans (rfl : (840 : Word) = UInt16.ofNat 840)
  have g (k : Nat) (h1 : 840 ≤ k) (h2 : k < 852) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (840 + off) :=
    word_pc_off 840 off hp (by omega)
  have m0 : s.mem.get s.pc = 25 := by
    rw [hp]
    have hval : decChunk052[8]! = 25 := rfl
    exact (g 840 (by decide) (by decide)).trans ((cell832 8 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 25 := by
    rw [poff 1 (by decide)]
    have hval : decChunk052[9]! = 25 := rfl
    exact (g 841 (by decide) (by decide)).trans ((cell832 9 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk052[10]! = 843 := rfl
    have hv : (843 : Word) = UInt16.ofNat 843 := rfl
    exact (g 842 (by decide) (by decide)).trans ((cell832 10 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 31 := by
    rw [poff 3 (by decide)]
    have hval : decChunk052[11]! = 31 := rfl
    exact (g 843 (by decide) (by decide)).trans ((cell832 11 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk052[12]! = 0 := rfl
    exact (g 844 (by decide) (by decide)).trans ((cell832 12 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk052[13]! = 846 := rfl
    have hv : (846 : Word) = UInt16.ofNat 846 := rfl
    exact (g 845 (by decide) (by decide)).trans ((cell832 13 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk052[14]! = 0 := rfl
    exact (g 846 (by decide) (by decide)).trans ((cell832 14 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 25 := by
    rw [poff 7 (by decide)]
    have hval : decChunk052[15]! = 25 := rfl
    exact (g 847 (by decide) (by decide)).trans ((cell832 15 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk053[0]! = 849 := rfl
    have hv : (849 : Word) = UInt16.ofNat 849 := rfl
    exact (g 848 (by decide) (by decide)).trans ((cell848 0 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk053[1]! = 0 := rfl
    exact (g 849 (by decide) (by decide)).trans ((cell848 1 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk053[2]! = 0 := rfl
    exact (g 850 (by decide) (by decide)).trans ((cell848 2 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk053[3]! = 852 := rfl
    have hv : (852 : Word) = UInt16.ofNat 852 := rfl
    exact (g 851 (by decide) (by decide)).trans ((cell848 3 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (25 : Word) := by
    intro i hi
    have : (25 : Word) = UInt16.ofNat 25 := rfl
    rw [this]
    exact pc_off_ne 840 i 25 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 840 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 31) (dst := 25)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 852 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (852 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 852 = (852 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP HAVE_DIG at pc 852 (TWO). -/
theorem ndig_enc_jmp_852 {s : Machine}
    (hpc : s.pc = 852)
    (hcode : ∀ k : Nat, 852 ≤ k → k < 852+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 867 := by
  have hp : s.pc = UInt16.ofNat 852 :=
    hpc.trans (rfl : (852 : Word) = UInt16.ofNat 852)
  have g (k : Nat) (h1 : 852 ≤ k) (h2 : k < 852+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk053[4]! = 0 := rfl
    exact (g 852 (by decide) (by decide)).trans ((cell848 4 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (853 : Word) := by simp [hpc]
    rw [this, (rfl : (853 : Word) = UInt16.ofNat 853)]
    have hval : decChunk053[5]! = 0 := rfl
    exact (g 853 (by decide) (by decide)).trans ((cell848 5 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 867 := by
    have : s.pc + 2 = (854 : Word) := by simp [hpc]
    rw [this, (rfl : (854 : Word) = UInt16.ofNat 854)]
    have hval : decChunk053[6]! = 867 := rfl
    exact (g 854 (by decide) (by decide)).trans ((cell848 6 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV ONE NDIG at ONE_DIG (pc 855), 4 steps to HAVE_DIG. -/
theorem ndig_one_mov_ONE_NDIG {s : Machine}
    (hpc : s.pc = 855)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 855 ≤ k → k < 867 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 867 ∧
    s4.halted = false ∧
    s4.mem.get 25 = s.mem.get 3 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 3 = s.mem.get 3 ∧
    (∀ a, a ≠ 25 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 855 :=
    hpc.trans (rfl : (855 : Word) = UInt16.ofNat 855)
  have g (k : Nat) (h1 : 855 ≤ k) (h2 : k < 867) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (855 + off) :=
    word_pc_off 855 off hp (by omega)
  have m0 : s.mem.get s.pc = 25 := by
    rw [hp]
    have hval : decChunk053[7]! = 25 := rfl
    exact (g 855 (by decide) (by decide)).trans ((cell848 7 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 25 := by
    rw [poff 1 (by decide)]
    have hval : decChunk053[8]! = 25 := rfl
    exact (g 856 (by decide) (by decide)).trans ((cell848 8 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk053[9]! = 858 := rfl
    have hv : (858 : Word) = UInt16.ofNat 858 := rfl
    exact (g 857 (by decide) (by decide)).trans ((cell848 9 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 3 := by
    rw [poff 3 (by decide)]
    have hval : decChunk053[10]! = 3 := rfl
    exact (g 858 (by decide) (by decide)).trans ((cell848 10 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk053[11]! = 0 := rfl
    exact (g 859 (by decide) (by decide)).trans ((cell848 11 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk053[12]! = 861 := rfl
    have hv : (861 : Word) = UInt16.ofNat 861 := rfl
    exact (g 860 (by decide) (by decide)).trans ((cell848 12 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk053[13]! = 0 := rfl
    exact (g 861 (by decide) (by decide)).trans ((cell848 13 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 25 := by
    rw [poff 7 (by decide)]
    have hval : decChunk053[14]! = 25 := rfl
    exact (g 862 (by decide) (by decide)).trans ((cell848 14 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk053[15]! = 864 := rfl
    have hv : (864 : Word) = UInt16.ofNat 864 := rfl
    exact (g 863 (by decide) (by decide)).trans ((cell848 15 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk054[0]! = 0 := rfl
    exact (g 864 (by decide) (by decide)).trans ((cell864 0 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk054[1]! = 0 := rfl
    exact (g 865 (by decide) (by decide)).trans ((cell864 1 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk054[2]! = 867 := rfl
    have hv : (867 : Word) = UInt16.ofNat 867 := rfl
    exact (g 866 (by decide) (by decide)).trans ((cell864 2 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (25 : Word) := by
    intro i hi
    have : (25 : Word) = UInt16.ofNat 25 := rfl
    rw [this]
    exact pc_off_ne 855 i 25 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 855 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 3) (dst := 25)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 867 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (867 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 867 = (867 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-! ### ASCII-digit facts and code-range helpers -/

/-- After subtracting `K48` from an ASCII digit, the difference is the
digit's numeric value in `0..9`. -/
theorem ascii_digit_sub_toNat (q : Word)
    (hlo : 48 ≤ q.toNat) (hhi : q.toNat ≤ 57) :
    (q - (48 : Word)).toNat = q.toNat - 48 := by
  have h48 : (48 : Word).toNat = 48 := rfl
  exact word_sub_ge q 48 (by omega)

theorem ascii_digit_le0_true {q : Word} (h : q = 48) :
    le0 (q - 48) = true := by
  rw [h]
  have : (48 : Word) - 48 = 0 := rfl
  rw [this]
  exact le0_zero

theorem ascii_digit_le0_false {q : Word}
    (hlo : 48 ≤ q.toNat) (hhi : q.toNat ≤ 57) (hne : q ≠ 48) :
    le0 (q - 48) = false := by
  have htn := ascii_digit_sub_toNat q hlo hhi
  have hq48 : q.toNat ≠ 48 := by
    intro h
    have : q = UInt16.ofNat 48 := word_eq_of_toNat q 48 (by decide) h
    have h48 : (48 : Word) = UInt16.ofNat 48 := rfl
    exact hne (this.trans h48.symm)
  have hpos : 0 < (q - 48).toNat := by omega
  have hlt : (q - 48).toNat < 32768 := by omega
  exact le0_pos hpos hlt

/-- Instruction cells in the NDIG region are never a scratch/data register. -/
theorem ndig_code_ne_reg (k r : Nat)
    (hk0 : 570 ≤ k) (hk1 : k < 867) (hr : r < 32) :
    UInt16.ofNat k ≠ UInt16.ofNat r :=
  ofNat_ne k r (by omega) (by omega) (by omega)

/-- Shrink a preserved image-code hypothesis onto a sub-interval of
`[570, 867)`, after writes only to `T` / `TMP` / `NDIG` / `Z`. -/
theorem ndig_code_shrink {s s' : Machine} {lo hi : Nat}
    (hpres : ∀ a, a ≠ (18 : Word) → a ≠ (31 : Word) → a ≠ (25 : Word) → a ≠ 0 →
      s'.mem.get a = s.mem.get a)
    (hcode : ∀ k : Nat, 570 ≤ k → k < 867 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hlo : 570 ≤ lo) (hhi : hi ≤ 867) :
    ∀ k : Nat, lo ≤ k → k < hi →
      s'.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
  intro k h1 h2
  have hk0 : 570 ≤ k := by omega
  have hk1 : k < 867 := by omega
  have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact ndig_code_ne_reg k 18 hk0 hk1 (by decide)
  have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact ndig_code_ne_reg k 31 hk0 hk1 (by decide)
  have hne25 : UInt16.ofNat k ≠ (25 : Word) := by
    have : (25 : Word) = UInt16.ofNat 25 := rfl
    rw [this]
    exact ndig_code_ne_reg k 25 hk0 hk1 (by decide)
  have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact ndig_code_ne_reg k 0 hk0 hk1 (by decide)
  exact (hpres (UInt16.ofNat k) hne18 hne31 hne25 hne0).trans (hcode k hk0 hk1)

/-- Same shrink when only `T` (and possibly `Z`) has been written. -/
theorem ndig_code_shrink_T {s s' : Machine} {lo hi : Nat}
    (hpres : ∀ a, a ≠ (18 : Word) → a ≠ 0 → s'.mem.get a = s.mem.get a)
    (hcode : ∀ k : Nat, 570 ≤ k → k < 867 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hlo : 570 ≤ lo) (hhi : hi ≤ 867) :
    ∀ k : Nat, lo ≤ k → k < hi →
      s'.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
  ndig_code_shrink (s := s) (s' := s') (lo := lo) (hi := hi)
    (fun a ha18 _ha31 _ha25 ha0 => hpres a ha18 ha0) hcode hlo hhi

/-- Test `Q0` at pc 570: taken JLEZ when `Q0 = '0'`, 6 steps to 591. -/
theorem ndig_test_Q0_zero {s : Machine}
    (hpc : s.pc = 570)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hQ : s.mem.get 20 = 48)
    (hcode : ∀ k : Nat, 570 ≤ k → k < 588 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s6 := runN s 6
    s6.pc = 591 ∧
    s6.halted = false ∧
    s6.mem.get 0 = 0 ∧
    s6.mem.get 18 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a) := by
  intro s6
  have hm := ndig_mov_Q0_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 582 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 20 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hK4 : s4.mem.get 8 = 48 := (hpres4 8 (by decide) (by decide)).trans hK48
  have g4 : ∀ k : Nat, 582 ≤ k → k < 585 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have hsub := ndig_sub_K48_T_582 (s := s4) hs4pc hs4h hK4 g4
  have hs5eq : step s4 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - 48), pc := 585 } := hsub
  have hs5pc : (step s4).pc = 585 := by rw [hs5eq]
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - 48) (by decide)).trans hs4Z
  have hs5T : (step s4).mem.get 18 = 0 := by
    rw [hs5eq, Mem.get_set_eq, hs4T, hQ]
    exact (rfl : (48 : Word) - 48 = 0)
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - 48) ha18).trans (hpres4 a ha18 ha0)
  have g5 : ∀ k : Nat, 585 ≤ k → k < 588 →
      (step s4).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have henc := ndig_enc_jlez_585 (s := step s4) hs5pc g5
  have hpc5 : (step s4).pc.toNat < 32768 := by simp [hs5pc]
  have hjlez :=
    step_JLEZ (s := step s4) (x := 18) (dest := 591)
      hs5h hpc5 hs5Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : ((step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18) = true := by
    have : le0 ((step s4).mem.get 18) = true := by
      rw [hs5T]
      exact le0_zero
    simpa [le0] using this
  have hs6eq : step (step s4) = { step s4 with pc := 591 } := by
    have hif :
        (if (step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18
          then (591 : Word) else (step s4).pc + 3) = (591 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hrun : s6 = step (step s4) := by
    have h6 : runN s 6 = runN s4 2 := runN_add_eq s 4 2 6 (by decide)
    have h2 : runN s4 2 = step (step s4) :=
      runN_2_steps s4 hs4h (by simp [hs4pc]) hs5h (by simp [hs5pc])
    exact h6.trans h2
  have hs6pc : s6.pc = 591 := by rw [hrun, hs6eq]
  have hs6h : s6.halted = false := by rw [hrun, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by rw [hrun, hs6eq]; exact hs5Z
  have hs6T : s6.mem.get 18 = 0 := by rw [hrun, hs6eq]; exact hs5T
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hs6eq]
    exact hpres5 a ha18 ha0
  exact ⟨hs6pc, hs6h, hs6Z, hs6T, hpres6⟩

/-- Test `Q0` at pc 570: fall-through + JMP when `Q0` is a non-zero ASCII digit, 7 steps to 657. -/
theorem ndig_test_Q0_nz {s : Machine}
    (hpc : s.pc = 570)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hlo : 48 ≤ (s.mem.get 20).toNat)
    (hhi : (s.mem.get 20).toNat ≤ 57)
    (hne : s.mem.get 20 ≠ 48)
    (hcode : ∀ k : Nat, 570 ≤ k → k < 591 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s7 := runN s 7
    s7.pc = 657 ∧
    s7.halted = false ∧
    s7.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a) := by
  intro s7
  have hm := ndig_mov_Q0_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 582 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 20 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hK4 : s4.mem.get 8 = 48 := (hpres4 8 (by decide) (by decide)).trans hK48
  have g4 : ∀ k : Nat, 582 ≤ k → k < 585 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have hsub := ndig_sub_K48_T_582 (s := s4) hs4pc hs4h hK4 g4
  have hs5eq : step s4 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - 48), pc := 585 } := hsub
  have hs5pc : (step s4).pc = 585 := by rw [hs5eq]
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - 48) (by decide)).trans hs4Z
  have hs5T : (step s4).mem.get 18 = s.mem.get 20 - 48 := by
    rw [hs5eq, Mem.get_set_eq, hs4T]
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - 48) ha18).trans (hpres4 a ha18 ha0)
  have g5 : ∀ k : Nat, 585 ≤ k → k < 588 →
      (step s4).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have henc := ndig_enc_jlez_585 (s := step s4) hs5pc g5
  have hpc5 : (step s4).pc.toNat < 32768 := by simp [hs5pc]
  have hjlez :=
    step_JLEZ (s := step s4) (x := 18) (dest := 591)
      hs5h hpc5 hs5Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : ((step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18) = false := by
    have : le0 ((step s4).mem.get 18) = false := by
      rw [hs5T]
      exact ascii_digit_le0_false hlo hhi hne
    simpa [le0] using this
  have hs6eq : step (step s4) = { step s4 with pc := 588 } := by
    have hif :
        (if (step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18
          then (591 : Word) else (step s4).pc + 3) = (588 : Word) := by
      have hfall : (step s4).pc + 3 = (588 : Word) := by simp [hs5pc]
      simp [hle, hfall]
    rw [hjlez, hif]
  have hs6pc : (step (step s4)).pc = 588 := by rw [hs6eq]
  have hs6h : (step (step s4)).halted = false := by rw [hs6eq]; exact hs5h
  have hs6Z : (step (step s4)).mem.get 0 = 0 := by rw [hs6eq]; exact hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → (step (step s4)).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs6eq]
    exact hpres5 a ha18 ha0
  have g6 : ∀ k : Nat, 588 ≤ k → k < 591 →
      (step (step s4)).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have hencj := ndig_enc_jmp_588 (s := step (step s4)) hs6pc g6
  have hpc6 : (step (step s4)).pc.toNat < 32768 := by simp [hs6pc]
  have hjmp :=
    step_JMP (s := step (step s4)) (dest := 657)
      hs6h hpc6 hs6Z hencj.1 hencj.2.1 hencj.2.2
  have hrun : s7 = step (step (step s4)) := by
    have h7 : runN s 7 = runN s4 3 := runN_add_eq s 4 3 7 (by decide)
    have h3 : runN s4 3 = step (step (step s4)) :=
      runN_3_steps s4 hs4h (by simp [hs4pc]) hs5h (by simp [hs5pc])
        hs6h (by simp [hs6pc])
    exact h7.trans h3
  have hs7pc : s7.pc = 657 := by rw [hrun, hjmp]
  have hs7h : s7.halted = false := by rw [hrun, hjmp]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs6Z
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hjmp]
    exact hpres6 a ha18 ha0
  exact ⟨hs7pc, hs7h, hs7Z, hpres7⟩


/-- Test `Q1` at pc 591: taken JLEZ when `Q1 = '0'`, 6 steps to 612. -/
theorem ndig_test_Q1_zero {s : Machine}
    (hpc : s.pc = 591)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hQ : s.mem.get 21 = 48)
    (hcode : ∀ k : Nat, 591 ≤ k → k < 609 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s6 := runN s 6
    s6.pc = 612 ∧
    s6.halted = false ∧
    s6.mem.get 0 = 0 ∧
    s6.mem.get 18 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a) := by
  intro s6
  have hm := ndig_mov_Q1_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 603 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 21 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hK4 : s4.mem.get 8 = 48 := (hpres4 8 (by decide) (by decide)).trans hK48
  have g4 : ∀ k : Nat, 603 ≤ k → k < 606 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have hsub := ndig_sub_K48_T_603 (s := s4) hs4pc hs4h hK4 g4
  have hs5eq : step s4 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - 48), pc := 606 } := hsub
  have hs5pc : (step s4).pc = 606 := by rw [hs5eq]
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - 48) (by decide)).trans hs4Z
  have hs5T : (step s4).mem.get 18 = 0 := by
    rw [hs5eq, Mem.get_set_eq, hs4T, hQ]
    exact (rfl : (48 : Word) - 48 = 0)
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - 48) ha18).trans (hpres4 a ha18 ha0)
  have g5 : ∀ k : Nat, 606 ≤ k → k < 609 →
      (step s4).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have henc := ndig_enc_jlez_606 (s := step s4) hs5pc g5
  have hpc5 : (step s4).pc.toNat < 32768 := by simp [hs5pc]
  have hjlez :=
    step_JLEZ (s := step s4) (x := 18) (dest := 612)
      hs5h hpc5 hs5Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : ((step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18) = true := by
    have : le0 ((step s4).mem.get 18) = true := by
      rw [hs5T]
      exact le0_zero
    simpa [le0] using this
  have hs6eq : step (step s4) = { step s4 with pc := 612 } := by
    have hif :
        (if (step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18
          then (612 : Word) else (step s4).pc + 3) = (612 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hrun : s6 = step (step s4) := by
    have h6 : runN s 6 = runN s4 2 := runN_add_eq s 4 2 6 (by decide)
    have h2 : runN s4 2 = step (step s4) :=
      runN_2_steps s4 hs4h (by simp [hs4pc]) hs5h (by simp [hs5pc])
    exact h6.trans h2
  have hs6pc : s6.pc = 612 := by rw [hrun, hs6eq]
  have hs6h : s6.halted = false := by rw [hrun, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by rw [hrun, hs6eq]; exact hs5Z
  have hs6T : s6.mem.get 18 = 0 := by rw [hrun, hs6eq]; exact hs5T
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hs6eq]
    exact hpres5 a ha18 ha0
  exact ⟨hs6pc, hs6h, hs6Z, hs6T, hpres6⟩

/-- Test `Q1` at pc 591: fall-through + JMP when `Q1` is a non-zero ASCII digit, 7 steps to 720. -/
theorem ndig_test_Q1_nz {s : Machine}
    (hpc : s.pc = 591)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hlo : 48 ≤ (s.mem.get 21).toNat)
    (hhi : (s.mem.get 21).toNat ≤ 57)
    (hne : s.mem.get 21 ≠ 48)
    (hcode : ∀ k : Nat, 591 ≤ k → k < 612 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s7 := runN s 7
    s7.pc = 720 ∧
    s7.halted = false ∧
    s7.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a) := by
  intro s7
  have hm := ndig_mov_Q1_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 603 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 21 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hK4 : s4.mem.get 8 = 48 := (hpres4 8 (by decide) (by decide)).trans hK48
  have g4 : ∀ k : Nat, 603 ≤ k → k < 606 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have hsub := ndig_sub_K48_T_603 (s := s4) hs4pc hs4h hK4 g4
  have hs5eq : step s4 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - 48), pc := 606 } := hsub
  have hs5pc : (step s4).pc = 606 := by rw [hs5eq]
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - 48) (by decide)).trans hs4Z
  have hs5T : (step s4).mem.get 18 = s.mem.get 21 - 48 := by
    rw [hs5eq, Mem.get_set_eq, hs4T]
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - 48) ha18).trans (hpres4 a ha18 ha0)
  have g5 : ∀ k : Nat, 606 ≤ k → k < 609 →
      (step s4).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have henc := ndig_enc_jlez_606 (s := step s4) hs5pc g5
  have hpc5 : (step s4).pc.toNat < 32768 := by simp [hs5pc]
  have hjlez :=
    step_JLEZ (s := step s4) (x := 18) (dest := 612)
      hs5h hpc5 hs5Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : ((step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18) = false := by
    have : le0 ((step s4).mem.get 18) = false := by
      rw [hs5T]
      exact ascii_digit_le0_false hlo hhi hne
    simpa [le0] using this
  have hs6eq : step (step s4) = { step s4 with pc := 609 } := by
    have hif :
        (if (step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18
          then (612 : Word) else (step s4).pc + 3) = (609 : Word) := by
      have hfall : (step s4).pc + 3 = (609 : Word) := by simp [hs5pc]
      simp [hle, hfall]
    rw [hjlez, hif]
  have hs6pc : (step (step s4)).pc = 609 := by rw [hs6eq]
  have hs6h : (step (step s4)).halted = false := by rw [hs6eq]; exact hs5h
  have hs6Z : (step (step s4)).mem.get 0 = 0 := by rw [hs6eq]; exact hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → (step (step s4)).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs6eq]
    exact hpres5 a ha18 ha0
  have g6 : ∀ k : Nat, 609 ≤ k → k < 612 →
      (step (step s4)).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have hencj := ndig_enc_jmp_609 (s := step (step s4)) hs6pc g6
  have hpc6 : (step (step s4)).pc.toNat < 32768 := by simp [hs6pc]
  have hjmp :=
    step_JMP (s := step (step s4)) (dest := 720)
      hs6h hpc6 hs6Z hencj.1 hencj.2.1 hencj.2.2
  have hrun : s7 = step (step (step s4)) := by
    have h7 : runN s 7 = runN s4 3 := runN_add_eq s 4 3 7 (by decide)
    have h3 : runN s4 3 = step (step (step s4)) :=
      runN_3_steps s4 hs4h (by simp [hs4pc]) hs5h (by simp [hs5pc])
        hs6h (by simp [hs6pc])
    exact h7.trans h3
  have hs7pc : s7.pc = 720 := by rw [hrun, hjmp]
  have hs7h : s7.halted = false := by rw [hrun, hjmp]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs6Z
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hjmp]
    exact hpres6 a ha18 ha0
  exact ⟨hs7pc, hs7h, hs7Z, hpres7⟩


/-- Test `Q2` at pc 612: taken JLEZ when `Q2 = '0'`, 6 steps to 633. -/
theorem ndig_test_Q2_zero {s : Machine}
    (hpc : s.pc = 612)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hQ : s.mem.get 22 = 48)
    (hcode : ∀ k : Nat, 612 ≤ k → k < 630 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s6 := runN s 6
    s6.pc = 633 ∧
    s6.halted = false ∧
    s6.mem.get 0 = 0 ∧
    s6.mem.get 18 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a) := by
  intro s6
  have hm := ndig_mov_Q2_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 624 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 22 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hK4 : s4.mem.get 8 = 48 := (hpres4 8 (by decide) (by decide)).trans hK48
  have g4 : ∀ k : Nat, 624 ≤ k → k < 627 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have hsub := ndig_sub_K48_T_624 (s := s4) hs4pc hs4h hK4 g4
  have hs5eq : step s4 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - 48), pc := 627 } := hsub
  have hs5pc : (step s4).pc = 627 := by rw [hs5eq]
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - 48) (by decide)).trans hs4Z
  have hs5T : (step s4).mem.get 18 = 0 := by
    rw [hs5eq, Mem.get_set_eq, hs4T, hQ]
    exact (rfl : (48 : Word) - 48 = 0)
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - 48) ha18).trans (hpres4 a ha18 ha0)
  have g5 : ∀ k : Nat, 627 ≤ k → k < 630 →
      (step s4).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have henc := ndig_enc_jlez_627 (s := step s4) hs5pc g5
  have hpc5 : (step s4).pc.toNat < 32768 := by simp [hs5pc]
  have hjlez :=
    step_JLEZ (s := step s4) (x := 18) (dest := 633)
      hs5h hpc5 hs5Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : ((step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18) = true := by
    have : le0 ((step s4).mem.get 18) = true := by
      rw [hs5T]
      exact le0_zero
    simpa [le0] using this
  have hs6eq : step (step s4) = { step s4 with pc := 633 } := by
    have hif :
        (if (step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18
          then (633 : Word) else (step s4).pc + 3) = (633 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hrun : s6 = step (step s4) := by
    have h6 : runN s 6 = runN s4 2 := runN_add_eq s 4 2 6 (by decide)
    have h2 : runN s4 2 = step (step s4) :=
      runN_2_steps s4 hs4h (by simp [hs4pc]) hs5h (by simp [hs5pc])
    exact h6.trans h2
  have hs6pc : s6.pc = 633 := by rw [hrun, hs6eq]
  have hs6h : s6.halted = false := by rw [hrun, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by rw [hrun, hs6eq]; exact hs5Z
  have hs6T : s6.mem.get 18 = 0 := by rw [hrun, hs6eq]; exact hs5T
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hs6eq]
    exact hpres5 a ha18 ha0
  exact ⟨hs6pc, hs6h, hs6Z, hs6T, hpres6⟩

/-- Test `Q2` at pc 612: fall-through + JMP when `Q2` is a non-zero ASCII digit, 7 steps to 774. -/
theorem ndig_test_Q2_nz {s : Machine}
    (hpc : s.pc = 612)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hlo : 48 ≤ (s.mem.get 22).toNat)
    (hhi : (s.mem.get 22).toNat ≤ 57)
    (hne : s.mem.get 22 ≠ 48)
    (hcode : ∀ k : Nat, 612 ≤ k → k < 633 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s7 := runN s 7
    s7.pc = 774 ∧
    s7.halted = false ∧
    s7.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a) := by
  intro s7
  have hm := ndig_mov_Q2_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 624 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 22 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hK4 : s4.mem.get 8 = 48 := (hpres4 8 (by decide) (by decide)).trans hK48
  have g4 : ∀ k : Nat, 624 ≤ k → k < 627 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have hsub := ndig_sub_K48_T_624 (s := s4) hs4pc hs4h hK4 g4
  have hs5eq : step s4 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - 48), pc := 627 } := hsub
  have hs5pc : (step s4).pc = 627 := by rw [hs5eq]
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - 48) (by decide)).trans hs4Z
  have hs5T : (step s4).mem.get 18 = s.mem.get 22 - 48 := by
    rw [hs5eq, Mem.get_set_eq, hs4T]
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - 48) ha18).trans (hpres4 a ha18 ha0)
  have g5 : ∀ k : Nat, 627 ≤ k → k < 630 →
      (step s4).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have henc := ndig_enc_jlez_627 (s := step s4) hs5pc g5
  have hpc5 : (step s4).pc.toNat < 32768 := by simp [hs5pc]
  have hjlez :=
    step_JLEZ (s := step s4) (x := 18) (dest := 633)
      hs5h hpc5 hs5Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : ((step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18) = false := by
    have : le0 ((step s4).mem.get 18) = false := by
      rw [hs5T]
      exact ascii_digit_le0_false hlo hhi hne
    simpa [le0] using this
  have hs6eq : step (step s4) = { step s4 with pc := 630 } := by
    have hif :
        (if (step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18
          then (633 : Word) else (step s4).pc + 3) = (630 : Word) := by
      have hfall : (step s4).pc + 3 = (630 : Word) := by simp [hs5pc]
      simp [hle, hfall]
    rw [hjlez, hif]
  have hs6pc : (step (step s4)).pc = 630 := by rw [hs6eq]
  have hs6h : (step (step s4)).halted = false := by rw [hs6eq]; exact hs5h
  have hs6Z : (step (step s4)).mem.get 0 = 0 := by rw [hs6eq]; exact hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → (step (step s4)).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs6eq]
    exact hpres5 a ha18 ha0
  have g6 : ∀ k : Nat, 630 ≤ k → k < 633 →
      (step (step s4)).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have hencj := ndig_enc_jmp_630 (s := step (step s4)) hs6pc g6
  have hpc6 : (step (step s4)).pc.toNat < 32768 := by simp [hs6pc]
  have hjmp :=
    step_JMP (s := step (step s4)) (dest := 774)
      hs6h hpc6 hs6Z hencj.1 hencj.2.1 hencj.2.2
  have hrun : s7 = step (step (step s4)) := by
    have h7 : runN s 7 = runN s4 3 := runN_add_eq s 4 3 7 (by decide)
    have h3 : runN s4 3 = step (step (step s4)) :=
      runN_3_steps s4 hs4h (by simp [hs4pc]) hs5h (by simp [hs5pc])
        hs6h (by simp [hs6pc])
    exact h7.trans h3
  have hs7pc : s7.pc = 774 := by rw [hrun, hjmp]
  have hs7h : s7.halted = false := by rw [hrun, hjmp]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs6Z
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hjmp]
    exact hpres6 a ha18 ha0
  exact ⟨hs7pc, hs7h, hs7Z, hpres7⟩


/-- Test `Q3` at pc 633: taken JLEZ when `Q3 = '0'`, 6 steps to 654. -/
theorem ndig_test_Q3_zero {s : Machine}
    (hpc : s.pc = 633)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hQ : s.mem.get 23 = 48)
    (hcode : ∀ k : Nat, 633 ≤ k → k < 651 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s6 := runN s 6
    s6.pc = 654 ∧
    s6.halted = false ∧
    s6.mem.get 0 = 0 ∧
    s6.mem.get 18 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a) := by
  intro s6
  have hm := ndig_mov_Q3_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 645 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 23 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hK4 : s4.mem.get 8 = 48 := (hpres4 8 (by decide) (by decide)).trans hK48
  have g4 : ∀ k : Nat, 645 ≤ k → k < 648 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have hsub := ndig_sub_K48_T_645 (s := s4) hs4pc hs4h hK4 g4
  have hs5eq : step s4 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - 48), pc := 648 } := hsub
  have hs5pc : (step s4).pc = 648 := by rw [hs5eq]
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - 48) (by decide)).trans hs4Z
  have hs5T : (step s4).mem.get 18 = 0 := by
    rw [hs5eq, Mem.get_set_eq, hs4T, hQ]
    exact (rfl : (48 : Word) - 48 = 0)
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - 48) ha18).trans (hpres4 a ha18 ha0)
  have g5 : ∀ k : Nat, 648 ≤ k → k < 651 →
      (step s4).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have henc := ndig_enc_jlez_648 (s := step s4) hs5pc g5
  have hpc5 : (step s4).pc.toNat < 32768 := by simp [hs5pc]
  have hjlez :=
    step_JLEZ (s := step s4) (x := 18) (dest := 654)
      hs5h hpc5 hs5Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : ((step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18) = true := by
    have : le0 ((step s4).mem.get 18) = true := by
      rw [hs5T]
      exact le0_zero
    simpa [le0] using this
  have hs6eq : step (step s4) = { step s4 with pc := 654 } := by
    have hif :
        (if (step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18
          then (654 : Word) else (step s4).pc + 3) = (654 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hrun : s6 = step (step s4) := by
    have h6 : runN s 6 = runN s4 2 := runN_add_eq s 4 2 6 (by decide)
    have h2 : runN s4 2 = step (step s4) :=
      runN_2_steps s4 hs4h (by simp [hs4pc]) hs5h (by simp [hs5pc])
    exact h6.trans h2
  have hs6pc : s6.pc = 654 := by rw [hrun, hs6eq]
  have hs6h : s6.halted = false := by rw [hrun, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by rw [hrun, hs6eq]; exact hs5Z
  have hs6T : s6.mem.get 18 = 0 := by rw [hrun, hs6eq]; exact hs5T
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hs6eq]
    exact hpres5 a ha18 ha0
  exact ⟨hs6pc, hs6h, hs6Z, hs6T, hpres6⟩

/-- Test `Q3` at pc 633: fall-through + JMP when `Q3` is a non-zero ASCII digit, 7 steps to 819. -/
theorem ndig_test_Q3_nz {s : Machine}
    (hpc : s.pc = 633)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hlo : 48 ≤ (s.mem.get 23).toNat)
    (hhi : (s.mem.get 23).toNat ≤ 57)
    (hne : s.mem.get 23 ≠ 48)
    (hcode : ∀ k : Nat, 633 ≤ k → k < 654 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s7 := runN s 7
    s7.pc = 819 ∧
    s7.halted = false ∧
    s7.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a) := by
  intro s7
  have hm := ndig_mov_Q3_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 645 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 23 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hK4 : s4.mem.get 8 = 48 := (hpres4 8 (by decide) (by decide)).trans hK48
  have g4 : ∀ k : Nat, 645 ≤ k → k < 648 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have hsub := ndig_sub_K48_T_645 (s := s4) hs4pc hs4h hK4 g4
  have hs5eq : step s4 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - 48), pc := 648 } := hsub
  have hs5pc : (step s4).pc = 648 := by rw [hs5eq]
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - 48) (by decide)).trans hs4Z
  have hs5T : (step s4).mem.get 18 = s.mem.get 23 - 48 := by
    rw [hs5eq, Mem.get_set_eq, hs4T]
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - 48) ha18).trans (hpres4 a ha18 ha0)
  have g5 : ∀ k : Nat, 648 ≤ k → k < 651 →
      (step s4).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have henc := ndig_enc_jlez_648 (s := step s4) hs5pc g5
  have hpc5 : (step s4).pc.toNat < 32768 := by simp [hs5pc]
  have hjlez :=
    step_JLEZ (s := step s4) (x := 18) (dest := 654)
      hs5h hpc5 hs5Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : ((step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18) = false := by
    have : le0 ((step s4).mem.get 18) = false := by
      rw [hs5T]
      exact ascii_digit_le0_false hlo hhi hne
    simpa [le0] using this
  have hs6eq : step (step s4) = { step s4 with pc := 651 } := by
    have hif :
        (if (step s4).mem.get 18 = 0 || 0x8000 ≤ (step s4).mem.get 18
          then (654 : Word) else (step s4).pc + 3) = (651 : Word) := by
      have hfall : (step s4).pc + 3 = (651 : Word) := by simp [hs5pc]
      simp [hle, hfall]
    rw [hjlez, hif]
  have hs6pc : (step (step s4)).pc = 651 := by rw [hs6eq]
  have hs6h : (step (step s4)).halted = false := by rw [hs6eq]; exact hs5h
  have hs6Z : (step (step s4)).mem.get 0 = 0 := by rw [hs6eq]; exact hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → (step (step s4)).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs6eq]
    exact hpres5 a ha18 ha0
  have g6 : ∀ k : Nat, 651 ≤ k → k < 654 →
      (step (step s4)).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]
      exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) hne18 hne0).trans (hcode k (by omega) (by omega))
  have hencj := ndig_enc_jmp_651 (s := step (step s4)) hs6pc g6
  have hpc6 : (step (step s4)).pc.toNat < 32768 := by simp [hs6pc]
  have hjmp :=
    step_JMP (s := step (step s4)) (dest := 819)
      hs6h hpc6 hs6Z hencj.1 hencj.2.1 hencj.2.2
  have hrun : s7 = step (step (step s4)) := by
    have h7 : runN s 7 = runN s4 3 := runN_add_eq s 4 3 7 (by decide)
    have h3 : runN s4 3 = step (step (step s4)) :=
      runN_3_steps s4 hs4h (by simp [hs4pc]) hs5h (by simp [hs5pc])
        hs6h (by simp [hs6pc])
    exact h7.trans h3
  have hs7pc : s7.pc = 819 := by rw [hrun, hjmp]
  have hs7h : s7.halted = false := by rw [hrun, hjmp]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs6Z
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hjmp]
    exact hpres6 a ha18 ha0
  exact ⟨hs7pc, hs7h, hs7Z, hpres7⟩

/-- `S4` is only `JMP ONE_DIG` (Q4 is always included). 1 step, 654 → 855. -/
theorem ndig_s4_jmp {s : Machine}
    (hpc : s.pc = 654)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 654 ≤ k → k < 657 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s1 := runN s 1
    s1.pc = 855 ∧
    s1.halted = false ∧
    s1.mem.get 0 = 0 ∧
    (∀ a, s1.mem.get a = s.mem.get a) := by
  intro s1
  have henc := ndig_enc_jmp_654 hpc hcode
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hjmp := step_JMP (s := s) (dest := 855) hh hpc0 hZ henc.1 henc.2.1 henc.2.2
  have hrun : s1 = step s := runN_one s hh hpc0
  have hs1pc : s1.pc = 855 := by rw [hrun, hjmp]
  have hs1h : s1.halted = false := by rw [hrun, hjmp]; exact hh
  have hs1Z : s1.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hZ
  have hpres : ∀ a, s1.mem.get a = s.mem.get a := by
    intro a
    rw [hrun, hjmp]
  exact ⟨hs1pc, hs1h, hs1Z, hpres⟩

/-- `five` builder: set `NDIG = 5`, 21 steps from pc 657 to `HAVE_DIG`. -/
theorem ndig_build_five {s : Machine}
    (hpc : s.pc = 657)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 657 ≤ k → k < 717+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 21
    sN.pc = 867 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 25 = 5 ∧
    (∀ a, a ≠ 25 → a ≠ 31 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm0 := ndig_five_mov_ONE_TMP (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 669 := hm0.1
  have hs4h : s4.halted = false := hm0.2.1
  have hs4Tmp : s4.mem.get 31 = s.mem.get 3 := hm0.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm0.2.2.2.1
  have hpres4 := hm0.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hs4Tmp1 : s4.mem.get 31 = 1 := hs4Tmp.trans hONE
  have g4 : ∀ k : Nat, 669 ≤ k → k < 678 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hi1 := ndig_five_inc_TMP_1 (s := s4) hs4pc hs4h hs4Z hONE4 g4
  have hrun7 : runN s 7 = runN s4 3 :=
    runN_add_eq s 4 3 7 (by decide)
  let s7 := runN s 7
  have hs7pc : s7.pc = 678 := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.1
  have hs7h : s7.halted = false := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.2.1
  have hs7Tmp : s7.mem.get 31 = s4.mem.get 31 + 1 := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.2.2.1
  have hs7Z : s7.mem.get 0 = 0 := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.2.2.2.1
  have hpres7 : ∀ a, a ≠ 31 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    have : s7 = runN s4 3 := hrun7
    rw [this]
    exact (hi1.2.2.2.2 a ha31 ha0).trans (hpres4 a ha31 ha0)
  have hONE7 : s7.mem.get 3 = 1 :=
    (hpres7 3 (by decide) (by decide)).trans hONE
  have hs7TmpN : s7.mem.get 31 = 2 := by
    have h1 : s7.mem.get 31 = (1 : Word) + 1 := by
      exact hs7Tmp.trans (by rw [hs4Tmp1])
    exact h1.trans (rfl : (1 : Word) + 1 = 2)
  have g7 : ∀ k : Nat, 678 ≤ k → k < 687 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres7 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hi2 := ndig_five_inc_TMP_2 (s := s7) hs7pc hs7h hs7Z hONE7 g7
  have hrun10 : runN s 10 = runN s7 3 :=
    runN_add_eq s 7 3 10 (by decide)
  let s10 := runN s 10
  have hs10pc : s10.pc = 687 := by
    have : s10 = runN s7 3 := hrun10
    rw [this]; exact hi2.1
  have hs10h : s10.halted = false := by
    have : s10 = runN s7 3 := hrun10
    rw [this]; exact hi2.2.1
  have hs10Tmp : s10.mem.get 31 = s7.mem.get 31 + 1 := by
    have : s10 = runN s7 3 := hrun10
    rw [this]; exact hi2.2.2.1
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = runN s7 3 := hrun10
    rw [this]; exact hi2.2.2.2.1
  have hpres10 : ∀ a, a ≠ 31 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    have : s10 = runN s7 3 := hrun10
    rw [this]
    exact (hi2.2.2.2.2 a ha31 ha0).trans (hpres7 a ha31 ha0)
  have hONE10 : s10.mem.get 3 = 1 :=
    (hpres10 3 (by decide) (by decide)).trans hONE
  have hs10TmpN : s10.mem.get 31 = 3 := by
    have h1 : s10.mem.get 31 = (2 : Word) + 1 := by
      exact hs10Tmp.trans (by rw [hs7TmpN])
    exact h1.trans (rfl : (2 : Word) + 1 = 3)
  have g10 : ∀ k : Nat, 687 ≤ k → k < 696 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hi3 := ndig_five_inc_TMP_3 (s := s10) hs10pc hs10h hs10Z hONE10 g10
  have hrun13 : runN s 13 = runN s10 3 :=
    runN_add_eq s 10 3 13 (by decide)
  let s13 := runN s 13
  have hs13pc : s13.pc = 696 := by
    have : s13 = runN s10 3 := hrun13
    rw [this]; exact hi3.1
  have hs13h : s13.halted = false := by
    have : s13 = runN s10 3 := hrun13
    rw [this]; exact hi3.2.1
  have hs13Tmp : s13.mem.get 31 = s10.mem.get 31 + 1 := by
    have : s13 = runN s10 3 := hrun13
    rw [this]; exact hi3.2.2.1
  have hs13Z : s13.mem.get 0 = 0 := by
    have : s13 = runN s10 3 := hrun13
    rw [this]; exact hi3.2.2.2.1
  have hpres13 : ∀ a, a ≠ 31 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    have : s13 = runN s10 3 := hrun13
    rw [this]
    exact (hi3.2.2.2.2 a ha31 ha0).trans (hpres10 a ha31 ha0)
  have hONE13 : s13.mem.get 3 = 1 :=
    (hpres13 3 (by decide) (by decide)).trans hONE
  have hs13TmpN : s13.mem.get 31 = 4 := by
    have h1 : s13.mem.get 31 = (3 : Word) + 1 := by
      exact hs13Tmp.trans (by rw [hs10TmpN])
    exact h1.trans (rfl : (3 : Word) + 1 = 4)
  have g13 : ∀ k : Nat, 696 ≤ k → k < 705 →
      s13.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres13 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hi4 := ndig_five_inc_TMP_4 (s := s13) hs13pc hs13h hs13Z hONE13 g13
  have hrun16 : runN s 16 = runN s13 3 :=
    runN_add_eq s 13 3 16 (by decide)
  let s16 := runN s 16
  have hs16pc : s16.pc = 705 := by
    have : s16 = runN s13 3 := hrun16
    rw [this]; exact hi4.1
  have hs16h : s16.halted = false := by
    have : s16 = runN s13 3 := hrun16
    rw [this]; exact hi4.2.1
  have hs16Tmp : s16.mem.get 31 = s13.mem.get 31 + 1 := by
    have : s16 = runN s13 3 := hrun16
    rw [this]; exact hi4.2.2.1
  have hs16Z : s16.mem.get 0 = 0 := by
    have : s16 = runN s13 3 := hrun16
    rw [this]; exact hi4.2.2.2.1
  have hpres16 : ∀ a, a ≠ 31 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    have : s16 = runN s13 3 := hrun16
    rw [this]
    exact (hi4.2.2.2.2 a ha31 ha0).trans (hpres13 a ha31 ha0)
  have hONE16 : s16.mem.get 3 = 1 :=
    (hpres16 3 (by decide) (by decide)).trans hONE
  have hs16TmpN : s16.mem.get 31 = 5 := by
    have h1 : s16.mem.get 31 = (4 : Word) + 1 := by
      exact hs16Tmp.trans (by rw [hs13TmpN])
    exact h1.trans (rfl : (4 : Word) + 1 = 5)
  have g16 : ∀ k : Nat, 705 ≤ k → k < 717 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hmn := ndig_five_mov_TMP_NDIG (s := s16) hs16pc hs16h hs16Z g16
  have hrun20 : runN s 20 = runN s16 4 :=
    runN_add_eq s 16 4 20 (by decide)
  let s20 := runN s 20
  have hs20pc : s20.pc = 717 := by
    have : s20 = runN s16 4 := hrun20
    rw [this]; exact hmn.1
  have hs20h : s20.halted = false := by
    have : s20 = runN s16 4 := hrun20
    rw [this]; exact hmn.2.1
  have hs20Ndig : s20.mem.get 25 = s16.mem.get 31 := by
    have : s20 = runN s16 4 := hrun20
    rw [this]; exact hmn.2.2.1
  have hs20Z : s20.mem.get 0 = 0 := by
    have : s20 = runN s16 4 := hrun20
    rw [this]; exact hmn.2.2.2.1
  have hs20Tmp : s20.mem.get 31 = s16.mem.get 31 := by
    have : s20 = runN s16 4 := hrun20
    rw [this]; exact hmn.2.2.2.2.1
  have hpres20 : ∀ a, a ≠ 25 → a ≠ 31 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a ha25 ha31 ha0
    have : s20 = runN s16 4 := hrun20
    rw [this]
    exact (hmn.2.2.2.2.2 a ha25 ha0).trans (hpres16 a ha31 ha0)
  have hs20NdigN : s20.mem.get 25 = 5 := by
    exact hs20Ndig.trans hs16TmpN
  have g20 : ∀ k : Nat, 717 ≤ k → k < 717+3 →
      s20.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne25 : UInt16.ofNat k ≠ (25 : Word) := by
      have : (25 : Word) = UInt16.ofNat 25 := rfl
      rw [this]
      exact ofNat_ne k 25 (by omega) (by decide) (by omega)
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres20 (UInt16.ofNat k) hne25 hne31 hne0).trans (hcode k (by omega) (by omega))
  have henc := ndig_enc_jmp_717 (s := s20) hs20pc g20
  have hpcN : s20.pc.toNat < 32768 := by simp [hs20pc]
  have hjmp := step_JMP (s := s20) (dest := 867)
    hs20h hpcN hs20Z henc.1 henc.2.1 henc.2.2
  have hrunN : sN = step s20 := by
    have hsteps : runN s 21 = runN s20 1 :=
      runN_add_eq s 20 1 21 (by decide)
    exact hsteps.trans (runN_one s20 hs20h hpcN)
  have hsNpc : sN.pc = 867 := by rw [hrunN, hjmp]
  have hsNh : sN.halted = false := by rw [hrunN, hjmp]; exact hs20h
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrunN, hjmp]; exact hs20Z
  have hsNNdig : sN.mem.get 25 = 5 := by rw [hrunN, hjmp]; exact hs20NdigN
  have hpresN : ∀ a, a ≠ 25 → a ≠ 31 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a ha25 ha31 ha0
    rw [hrunN, hjmp]
    exact hpres20 a ha25 ha31 ha0
  exact ⟨hsNpc, hsNh, hsNZ, hsNNdig, hpresN⟩

/-- `four` builder: set `NDIG = 4`, 18 steps from pc 720 to `HAVE_DIG`. -/
theorem ndig_build_four {s : Machine}
    (hpc : s.pc = 720)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 720 ≤ k → k < 771+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 18
    sN.pc = 867 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 25 = 4 ∧
    (∀ a, a ≠ 25 → a ≠ 31 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm0 := ndig_four_mov_ONE_TMP (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 732 := hm0.1
  have hs4h : s4.halted = false := hm0.2.1
  have hs4Tmp : s4.mem.get 31 = s.mem.get 3 := hm0.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm0.2.2.2.1
  have hpres4 := hm0.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hs4Tmp1 : s4.mem.get 31 = 1 := hs4Tmp.trans hONE
  have g4 : ∀ k : Nat, 732 ≤ k → k < 741 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hi1 := ndig_four_inc_TMP_1 (s := s4) hs4pc hs4h hs4Z hONE4 g4
  have hrun7 : runN s 7 = runN s4 3 :=
    runN_add_eq s 4 3 7 (by decide)
  let s7 := runN s 7
  have hs7pc : s7.pc = 741 := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.1
  have hs7h : s7.halted = false := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.2.1
  have hs7Tmp : s7.mem.get 31 = s4.mem.get 31 + 1 := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.2.2.1
  have hs7Z : s7.mem.get 0 = 0 := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.2.2.2.1
  have hpres7 : ∀ a, a ≠ 31 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    have : s7 = runN s4 3 := hrun7
    rw [this]
    exact (hi1.2.2.2.2 a ha31 ha0).trans (hpres4 a ha31 ha0)
  have hONE7 : s7.mem.get 3 = 1 :=
    (hpres7 3 (by decide) (by decide)).trans hONE
  have hs7TmpN : s7.mem.get 31 = 2 := by
    have h1 : s7.mem.get 31 = (1 : Word) + 1 := by
      exact hs7Tmp.trans (by rw [hs4Tmp1])
    exact h1.trans (rfl : (1 : Word) + 1 = 2)
  have g7 : ∀ k : Nat, 741 ≤ k → k < 750 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres7 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hi2 := ndig_four_inc_TMP_2 (s := s7) hs7pc hs7h hs7Z hONE7 g7
  have hrun10 : runN s 10 = runN s7 3 :=
    runN_add_eq s 7 3 10 (by decide)
  let s10 := runN s 10
  have hs10pc : s10.pc = 750 := by
    have : s10 = runN s7 3 := hrun10
    rw [this]; exact hi2.1
  have hs10h : s10.halted = false := by
    have : s10 = runN s7 3 := hrun10
    rw [this]; exact hi2.2.1
  have hs10Tmp : s10.mem.get 31 = s7.mem.get 31 + 1 := by
    have : s10 = runN s7 3 := hrun10
    rw [this]; exact hi2.2.2.1
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = runN s7 3 := hrun10
    rw [this]; exact hi2.2.2.2.1
  have hpres10 : ∀ a, a ≠ 31 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    have : s10 = runN s7 3 := hrun10
    rw [this]
    exact (hi2.2.2.2.2 a ha31 ha0).trans (hpres7 a ha31 ha0)
  have hONE10 : s10.mem.get 3 = 1 :=
    (hpres10 3 (by decide) (by decide)).trans hONE
  have hs10TmpN : s10.mem.get 31 = 3 := by
    have h1 : s10.mem.get 31 = (2 : Word) + 1 := by
      exact hs10Tmp.trans (by rw [hs7TmpN])
    exact h1.trans (rfl : (2 : Word) + 1 = 3)
  have g10 : ∀ k : Nat, 750 ≤ k → k < 759 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hi3 := ndig_four_inc_TMP_3 (s := s10) hs10pc hs10h hs10Z hONE10 g10
  have hrun13 : runN s 13 = runN s10 3 :=
    runN_add_eq s 10 3 13 (by decide)
  let s13 := runN s 13
  have hs13pc : s13.pc = 759 := by
    have : s13 = runN s10 3 := hrun13
    rw [this]; exact hi3.1
  have hs13h : s13.halted = false := by
    have : s13 = runN s10 3 := hrun13
    rw [this]; exact hi3.2.1
  have hs13Tmp : s13.mem.get 31 = s10.mem.get 31 + 1 := by
    have : s13 = runN s10 3 := hrun13
    rw [this]; exact hi3.2.2.1
  have hs13Z : s13.mem.get 0 = 0 := by
    have : s13 = runN s10 3 := hrun13
    rw [this]; exact hi3.2.2.2.1
  have hpres13 : ∀ a, a ≠ 31 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    have : s13 = runN s10 3 := hrun13
    rw [this]
    exact (hi3.2.2.2.2 a ha31 ha0).trans (hpres10 a ha31 ha0)
  have hONE13 : s13.mem.get 3 = 1 :=
    (hpres13 3 (by decide) (by decide)).trans hONE
  have hs13TmpN : s13.mem.get 31 = 4 := by
    have h1 : s13.mem.get 31 = (3 : Word) + 1 := by
      exact hs13Tmp.trans (by rw [hs10TmpN])
    exact h1.trans (rfl : (3 : Word) + 1 = 4)
  have g13 : ∀ k : Nat, 759 ≤ k → k < 771 →
      s13.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres13 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hmn := ndig_four_mov_TMP_NDIG (s := s13) hs13pc hs13h hs13Z g13
  have hrun17 : runN s 17 = runN s13 4 :=
    runN_add_eq s 13 4 17 (by decide)
  let s17 := runN s 17
  have hs17pc : s17.pc = 771 := by
    have : s17 = runN s13 4 := hrun17
    rw [this]; exact hmn.1
  have hs17h : s17.halted = false := by
    have : s17 = runN s13 4 := hrun17
    rw [this]; exact hmn.2.1
  have hs17Ndig : s17.mem.get 25 = s13.mem.get 31 := by
    have : s17 = runN s13 4 := hrun17
    rw [this]; exact hmn.2.2.1
  have hs17Z : s17.mem.get 0 = 0 := by
    have : s17 = runN s13 4 := hrun17
    rw [this]; exact hmn.2.2.2.1
  have hs17Tmp : s17.mem.get 31 = s13.mem.get 31 := by
    have : s17 = runN s13 4 := hrun17
    rw [this]; exact hmn.2.2.2.2.1
  have hpres17 : ∀ a, a ≠ 25 → a ≠ 31 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha25 ha31 ha0
    have : s17 = runN s13 4 := hrun17
    rw [this]
    exact (hmn.2.2.2.2.2 a ha25 ha0).trans (hpres13 a ha31 ha0)
  have hs17NdigN : s17.mem.get 25 = 4 := by
    exact hs17Ndig.trans hs13TmpN
  have g17 : ∀ k : Nat, 771 ≤ k → k < 771+3 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne25 : UInt16.ofNat k ≠ (25 : Word) := by
      have : (25 : Word) = UInt16.ofNat 25 := rfl
      rw [this]
      exact ofNat_ne k 25 (by omega) (by decide) (by omega)
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) hne25 hne31 hne0).trans (hcode k (by omega) (by omega))
  have henc := ndig_enc_jmp_771 (s := s17) hs17pc g17
  have hpcN : s17.pc.toNat < 32768 := by simp [hs17pc]
  have hjmp := step_JMP (s := s17) (dest := 867)
    hs17h hpcN hs17Z henc.1 henc.2.1 henc.2.2
  have hrunN : sN = step s17 := by
    have hsteps : runN s 18 = runN s17 1 :=
      runN_add_eq s 17 1 18 (by decide)
    exact hsteps.trans (runN_one s17 hs17h hpcN)
  have hsNpc : sN.pc = 867 := by rw [hrunN, hjmp]
  have hsNh : sN.halted = false := by rw [hrunN, hjmp]; exact hs17h
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrunN, hjmp]; exact hs17Z
  have hsNNdig : sN.mem.get 25 = 4 := by rw [hrunN, hjmp]; exact hs17NdigN
  have hpresN : ∀ a, a ≠ 25 → a ≠ 31 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a ha25 ha31 ha0
    rw [hrunN, hjmp]
    exact hpres17 a ha25 ha31 ha0
  exact ⟨hsNpc, hsNh, hsNZ, hsNNdig, hpresN⟩

/-- `three` builder: set `NDIG = 3`, 15 steps from pc 774 to `HAVE_DIG`. -/
theorem ndig_build_three {s : Machine}
    (hpc : s.pc = 774)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 774 ≤ k → k < 816+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 15
    sN.pc = 867 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 25 = 3 ∧
    (∀ a, a ≠ 25 → a ≠ 31 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm0 := ndig_three_mov_ONE_TMP (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 786 := hm0.1
  have hs4h : s4.halted = false := hm0.2.1
  have hs4Tmp : s4.mem.get 31 = s.mem.get 3 := hm0.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm0.2.2.2.1
  have hpres4 := hm0.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hs4Tmp1 : s4.mem.get 31 = 1 := hs4Tmp.trans hONE
  have g4 : ∀ k : Nat, 786 ≤ k → k < 795 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hi1 := ndig_three_inc_TMP_1 (s := s4) hs4pc hs4h hs4Z hONE4 g4
  have hrun7 : runN s 7 = runN s4 3 :=
    runN_add_eq s 4 3 7 (by decide)
  let s7 := runN s 7
  have hs7pc : s7.pc = 795 := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.1
  have hs7h : s7.halted = false := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.2.1
  have hs7Tmp : s7.mem.get 31 = s4.mem.get 31 + 1 := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.2.2.1
  have hs7Z : s7.mem.get 0 = 0 := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.2.2.2.1
  have hpres7 : ∀ a, a ≠ 31 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    have : s7 = runN s4 3 := hrun7
    rw [this]
    exact (hi1.2.2.2.2 a ha31 ha0).trans (hpres4 a ha31 ha0)
  have hONE7 : s7.mem.get 3 = 1 :=
    (hpres7 3 (by decide) (by decide)).trans hONE
  have hs7TmpN : s7.mem.get 31 = 2 := by
    have h1 : s7.mem.get 31 = (1 : Word) + 1 := by
      exact hs7Tmp.trans (by rw [hs4Tmp1])
    exact h1.trans (rfl : (1 : Word) + 1 = 2)
  have g7 : ∀ k : Nat, 795 ≤ k → k < 804 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres7 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hi2 := ndig_three_inc_TMP_2 (s := s7) hs7pc hs7h hs7Z hONE7 g7
  have hrun10 : runN s 10 = runN s7 3 :=
    runN_add_eq s 7 3 10 (by decide)
  let s10 := runN s 10
  have hs10pc : s10.pc = 804 := by
    have : s10 = runN s7 3 := hrun10
    rw [this]; exact hi2.1
  have hs10h : s10.halted = false := by
    have : s10 = runN s7 3 := hrun10
    rw [this]; exact hi2.2.1
  have hs10Tmp : s10.mem.get 31 = s7.mem.get 31 + 1 := by
    have : s10 = runN s7 3 := hrun10
    rw [this]; exact hi2.2.2.1
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = runN s7 3 := hrun10
    rw [this]; exact hi2.2.2.2.1
  have hpres10 : ∀ a, a ≠ 31 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    have : s10 = runN s7 3 := hrun10
    rw [this]
    exact (hi2.2.2.2.2 a ha31 ha0).trans (hpres7 a ha31 ha0)
  have hONE10 : s10.mem.get 3 = 1 :=
    (hpres10 3 (by decide) (by decide)).trans hONE
  have hs10TmpN : s10.mem.get 31 = 3 := by
    have h1 : s10.mem.get 31 = (2 : Word) + 1 := by
      exact hs10Tmp.trans (by rw [hs7TmpN])
    exact h1.trans (rfl : (2 : Word) + 1 = 3)
  have g10 : ∀ k : Nat, 804 ≤ k → k < 816 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hmn := ndig_three_mov_TMP_NDIG (s := s10) hs10pc hs10h hs10Z g10
  have hrun14 : runN s 14 = runN s10 4 :=
    runN_add_eq s 10 4 14 (by decide)
  let s14 := runN s 14
  have hs14pc : s14.pc = 816 := by
    have : s14 = runN s10 4 := hrun14
    rw [this]; exact hmn.1
  have hs14h : s14.halted = false := by
    have : s14 = runN s10 4 := hrun14
    rw [this]; exact hmn.2.1
  have hs14Ndig : s14.mem.get 25 = s10.mem.get 31 := by
    have : s14 = runN s10 4 := hrun14
    rw [this]; exact hmn.2.2.1
  have hs14Z : s14.mem.get 0 = 0 := by
    have : s14 = runN s10 4 := hrun14
    rw [this]; exact hmn.2.2.2.1
  have hs14Tmp : s14.mem.get 31 = s10.mem.get 31 := by
    have : s14 = runN s10 4 := hrun14
    rw [this]; exact hmn.2.2.2.2.1
  have hpres14 : ∀ a, a ≠ 25 → a ≠ 31 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha25 ha31 ha0
    have : s14 = runN s10 4 := hrun14
    rw [this]
    exact (hmn.2.2.2.2.2 a ha25 ha0).trans (hpres10 a ha31 ha0)
  have hs14NdigN : s14.mem.get 25 = 3 := by
    exact hs14Ndig.trans hs10TmpN
  have g14 : ∀ k : Nat, 816 ≤ k → k < 816+3 →
      s14.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne25 : UInt16.ofNat k ≠ (25 : Word) := by
      have : (25 : Word) = UInt16.ofNat 25 := rfl
      rw [this]
      exact ofNat_ne k 25 (by omega) (by decide) (by omega)
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres14 (UInt16.ofNat k) hne25 hne31 hne0).trans (hcode k (by omega) (by omega))
  have henc := ndig_enc_jmp_816 (s := s14) hs14pc g14
  have hpcN : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hjmp := step_JMP (s := s14) (dest := 867)
    hs14h hpcN hs14Z henc.1 henc.2.1 henc.2.2
  have hrunN : sN = step s14 := by
    have hsteps : runN s 15 = runN s14 1 :=
      runN_add_eq s 14 1 15 (by decide)
    exact hsteps.trans (runN_one s14 hs14h hpcN)
  have hsNpc : sN.pc = 867 := by rw [hrunN, hjmp]
  have hsNh : sN.halted = false := by rw [hrunN, hjmp]; exact hs14h
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrunN, hjmp]; exact hs14Z
  have hsNNdig : sN.mem.get 25 = 3 := by rw [hrunN, hjmp]; exact hs14NdigN
  have hpresN : ∀ a, a ≠ 25 → a ≠ 31 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a ha25 ha31 ha0
    rw [hrunN, hjmp]
    exact hpres14 a ha25 ha31 ha0
  exact ⟨hsNpc, hsNh, hsNZ, hsNNdig, hpresN⟩

/-- `two` builder: set `NDIG = 2`, 12 steps from pc 819 to `HAVE_DIG`. -/
theorem ndig_build_two {s : Machine}
    (hpc : s.pc = 819)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 819 ≤ k → k < 852+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 12
    sN.pc = 867 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 25 = 2 ∧
    (∀ a, a ≠ 25 → a ≠ 31 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm0 := ndig_two_mov_ONE_TMP (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 831 := hm0.1
  have hs4h : s4.halted = false := hm0.2.1
  have hs4Tmp : s4.mem.get 31 = s.mem.get 3 := hm0.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm0.2.2.2.1
  have hpres4 := hm0.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hs4Tmp1 : s4.mem.get 31 = 1 := hs4Tmp.trans hONE
  have g4 : ∀ k : Nat, 831 ≤ k → k < 840 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hi1 := ndig_two_inc_TMP_1 (s := s4) hs4pc hs4h hs4Z hONE4 g4
  have hrun7 : runN s 7 = runN s4 3 :=
    runN_add_eq s 4 3 7 (by decide)
  let s7 := runN s 7
  have hs7pc : s7.pc = 840 := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.1
  have hs7h : s7.halted = false := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.2.1
  have hs7Tmp : s7.mem.get 31 = s4.mem.get 31 + 1 := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.2.2.1
  have hs7Z : s7.mem.get 0 = 0 := by
    have : s7 = runN s4 3 := hrun7
    rw [this]; exact hi1.2.2.2.1
  have hpres7 : ∀ a, a ≠ 31 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    have : s7 = runN s4 3 := hrun7
    rw [this]
    exact (hi1.2.2.2.2 a ha31 ha0).trans (hpres4 a ha31 ha0)
  have hONE7 : s7.mem.get 3 = 1 :=
    (hpres7 3 (by decide) (by decide)).trans hONE
  have hs7TmpN : s7.mem.get 31 = 2 := by
    have h1 : s7.mem.get 31 = (1 : Word) + 1 := by
      exact hs7Tmp.trans (by rw [hs4Tmp1])
    exact h1.trans (rfl : (1 : Word) + 1 = 2)
  have g7 : ∀ k : Nat, 840 ≤ k → k < 852 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres7 (UInt16.ofNat k) hne31 hne0).trans (hcode k (by omega) (by omega))
  have hmn := ndig_two_mov_TMP_NDIG (s := s7) hs7pc hs7h hs7Z g7
  have hrun11 : runN s 11 = runN s7 4 :=
    runN_add_eq s 7 4 11 (by decide)
  let s11 := runN s 11
  have hs11pc : s11.pc = 852 := by
    have : s11 = runN s7 4 := hrun11
    rw [this]; exact hmn.1
  have hs11h : s11.halted = false := by
    have : s11 = runN s7 4 := hrun11
    rw [this]; exact hmn.2.1
  have hs11Ndig : s11.mem.get 25 = s7.mem.get 31 := by
    have : s11 = runN s7 4 := hrun11
    rw [this]; exact hmn.2.2.1
  have hs11Z : s11.mem.get 0 = 0 := by
    have : s11 = runN s7 4 := hrun11
    rw [this]; exact hmn.2.2.2.1
  have hs11Tmp : s11.mem.get 31 = s7.mem.get 31 := by
    have : s11 = runN s7 4 := hrun11
    rw [this]; exact hmn.2.2.2.2.1
  have hpres11 : ∀ a, a ≠ 25 → a ≠ 31 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha25 ha31 ha0
    have : s11 = runN s7 4 := hrun11
    rw [this]
    exact (hmn.2.2.2.2.2 a ha25 ha0).trans (hpres7 a ha31 ha0)
  have hs11NdigN : s11.mem.get 25 = 2 := by
    exact hs11Ndig.trans hs7TmpN
  have g11 : ∀ k : Nat, 852 ≤ k → k < 852+3 →
      s11.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have hne25 : UInt16.ofNat k ≠ (25 : Word) := by
      have : (25 : Word) = UInt16.ofNat 25 := rfl
      rw [this]
      exact ofNat_ne k 25 (by omega) (by decide) (by omega)
    have hne31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]
      exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have hne0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]
      exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres11 (UInt16.ofNat k) hne25 hne31 hne0).trans (hcode k (by omega) (by omega))
  have henc := ndig_enc_jmp_852 (s := s11) hs11pc g11
  have hpcN : s11.pc.toNat < 32768 := by simp [hs11pc]
  have hjmp := step_JMP (s := s11) (dest := 867)
    hs11h hpcN hs11Z henc.1 henc.2.1 henc.2.2
  have hrunN : sN = step s11 := by
    have hsteps : runN s 12 = runN s11 1 :=
      runN_add_eq s 11 1 12 (by decide)
    exact hsteps.trans (runN_one s11 hs11h hpcN)
  have hsNpc : sN.pc = 867 := by rw [hrunN, hjmp]
  have hsNh : sN.halted = false := by rw [hrunN, hjmp]; exact hs11h
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrunN, hjmp]; exact hs11Z
  have hsNNdig : sN.mem.get 25 = 2 := by rw [hrunN, hjmp]; exact hs11NdigN
  have hpresN : ∀ a, a ≠ 25 → a ≠ 31 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a ha25 ha31 ha0
    rw [hrunN, hjmp]
    exact hpres11 a ha25 ha31 ha0
  exact ⟨hsNpc, hsNh, hsNZ, hsNNdig, hpresN⟩

/-- `ONE_DIG`: `MOV ONE NDIG`, 4 steps from pc 855 to `HAVE_DIG`, `NDIG = 1`. -/
theorem ndig_build_one {s : Machine}
    (hpc : s.pc = 855)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 855 ≤ k → k < 867 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 867 ∧
    s4.halted = false ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 25 = 1 ∧
    (∀ a, a ≠ 25 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hm := ndig_one_mov_ONE_NDIG (s := s) hpc hh hZ hcode
  have hs4pc : s4.pc = 867 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4N : s4.mem.get 25 = s.mem.get 3 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres := hm.2.2.2.2.2
  have hs4N1 : s4.mem.get 25 = 1 := hs4N.trans hONE
  exact ⟨hs4pc, hs4h, hs4Z, hs4N1, hpres⟩

/-! ### Full leading-zero arms: pc 570 → HAVE_DIG (867) -/

/-- `NDIG = 5` when `Q0` is a non-zero ASCII digit. 28 steps, 570 → 867. -/
theorem ndig_five {s : Machine}
    (hpc : s.pc = 570)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hlo : 48 ≤ (s.mem.get 20).toNat)
    (hhi : (s.mem.get 20).toNat ≤ 57)
    (hne : s.mem.get 20 ≠ 48)
    (hcode : ∀ k : Nat, 570 ≤ k → k < 867 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s28 := runN s 28
    s28.pc = 867 ∧
    s28.halted = false ∧
    s28.mem.get 0 = 0 ∧
    s28.mem.get 25 = 5 ∧
    (∀ a, a ≠ 18 → a ≠ 25 → a ≠ 31 → a ≠ 0 → s28.mem.get a = s.mem.get a) := by
  intro s28
  have ht := ndig_test_Q0_nz (s := s) hpc hh hZ hK48 hlo hhi hne
    (fun k h1 h2 => hcode k h1 (by omega))
  let s7 := runN s 7
  have hs7pc : s7.pc = 657 := ht.1
  have hs7h : s7.halted = false := ht.2.1
  have hs7Z : s7.mem.get 0 = 0 := ht.2.2.1
  have hpres7 := ht.2.2.2
  have hONE7 : s7.mem.get 3 = 1 := (hpres7 3 (by decide) (by decide)).trans hONE
  have g7 := ndig_code_shrink_T (s := s) (s' := s7) (lo := 657) (hi := 720)
    hpres7 hcode (by decide) (by decide)
  have hb := ndig_build_five (s := s7) hs7pc hs7h hs7Z hONE7 g7
  have hrun : s28 = runN s7 21 := runN_add_eq s 7 21 28 (by decide)
  have hs28pc : s28.pc = 867 := by rw [hrun]; exact hb.1
  have hs28h : s28.halted = false := by rw [hrun]; exact hb.2.1
  have hs28Z : s28.mem.get 0 = 0 := by rw [hrun]; exact hb.2.2.1
  have hs28N : s28.mem.get 25 = 5 := by rw [hrun]; exact hb.2.2.2.1
  have hpres : ∀ a, a ≠ 18 → a ≠ 25 → a ≠ 31 → a ≠ 0 → s28.mem.get a = s.mem.get a := by
    intro a ha18 ha25 ha31 ha0
    rw [hrun]
    exact (hb.2.2.2.2 a ha25 ha31 ha0).trans (hpres7 a ha18 ha0)
  exact ⟨hs28pc, hs28h, hs28Z, hs28N, hpres⟩

/-- `NDIG = 4` when `Q0 = '0'` and `Q1` is a non-zero ASCII digit. 31 steps. -/
theorem ndig_four {s : Machine}
    (hpc : s.pc = 570)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hQ0 : s.mem.get 20 = 48)
    (hlo : 48 ≤ (s.mem.get 21).toNat)
    (hhi : (s.mem.get 21).toNat ≤ 57)
    (hne : s.mem.get 21 ≠ 48)
    (hcode : ∀ k : Nat, 570 ≤ k → k < 867 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s31 := runN s 31
    s31.pc = 867 ∧
    s31.halted = false ∧
    s31.mem.get 0 = 0 ∧
    s31.mem.get 25 = 4 ∧
    (∀ a, a ≠ 18 → a ≠ 25 → a ≠ 31 → a ≠ 0 → s31.mem.get a = s.mem.get a) := by
  intro s31
  have ht0 := ndig_test_Q0_zero (s := s) hpc hh hZ hK48 hQ0
    (fun k h1 h2 => hcode k h1 (by omega))
  let s6 := runN s 6
  have hs6pc : s6.pc = 591 := ht0.1
  have hs6h : s6.halted = false := ht0.2.1
  have hs6Z : s6.mem.get 0 = 0 := ht0.2.2.1
  have hpres6 := ht0.2.2.2.2
  have hK6 : s6.mem.get 8 = 48 := (hpres6 8 (by decide) (by decide)).trans hK48
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have hQ1_6 : s6.mem.get 21 = s.mem.get 21 := hpres6 21 (by decide) (by decide)
  have hlo6 : 48 ≤ (s6.mem.get 21).toNat := by rw [hQ1_6]; exact hlo
  have hhi6 : (s6.mem.get 21).toNat ≤ 57 := by rw [hQ1_6]; exact hhi
  have hne6 : s6.mem.get 21 ≠ 48 := by rw [hQ1_6]; exact hne
  have g6 := ndig_code_shrink_T (s := s) (s' := s6) (lo := 591) (hi := 612)
    hpres6 hcode (by decide) (by decide)
  have ht1 := ndig_test_Q1_nz (s := s6) hs6pc hs6h hs6Z hK6 hlo6 hhi6 hne6 g6
  have hrun13 : runN s 13 = runN s6 7 := runN_add_eq s 6 7 13 (by decide)
  let s13 := runN s 13
  have hs13pc : s13.pc = 720 := by
    have : s13 = runN s6 7 := hrun13
    rw [this]; exact ht1.1
  have hs13h : s13.halted = false := by
    have : s13 = runN s6 7 := hrun13
    rw [this]; exact ht1.2.1
  have hs13Z : s13.mem.get 0 = 0 := by
    have : s13 = runN s6 7 := hrun13
    rw [this]; exact ht1.2.2.1
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s13 = runN s6 7 := hrun13
    rw [this]
    exact (ht1.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hONE13 : s13.mem.get 3 = 1 := (hpres13 3 (by decide) (by decide)).trans hONE
  have g13 := ndig_code_shrink_T (s := s) (s' := s13) (lo := 720) (hi := 774)
    hpres13 hcode (by decide) (by decide)
  have hb := ndig_build_four (s := s13) hs13pc hs13h hs13Z hONE13 g13
  have hrun : s31 = runN s13 18 := runN_add_eq s 13 18 31 (by decide)
  have hs31pc : s31.pc = 867 := by rw [hrun]; exact hb.1
  have hs31h : s31.halted = false := by rw [hrun]; exact hb.2.1
  have hs31Z : s31.mem.get 0 = 0 := by rw [hrun]; exact hb.2.2.1
  have hs31N : s31.mem.get 25 = 4 := by rw [hrun]; exact hb.2.2.2.1
  have hpres : ∀ a, a ≠ 18 → a ≠ 25 → a ≠ 31 → a ≠ 0 → s31.mem.get a = s.mem.get a := by
    intro a ha18 ha25 ha31 ha0
    rw [hrun]
    exact (hb.2.2.2.2 a ha25 ha31 ha0).trans (hpres13 a ha18 ha0)
  exact ⟨hs31pc, hs31h, hs31Z, hs31N, hpres⟩

/-- `NDIG = 3` when `Q0 = Q1 = '0'` and `Q2` is a non-zero ASCII digit. 34 steps. -/
theorem ndig_three {s : Machine}
    (hpc : s.pc = 570)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hQ0 : s.mem.get 20 = 48)
    (hQ1 : s.mem.get 21 = 48)
    (hlo : 48 ≤ (s.mem.get 22).toNat)
    (hhi : (s.mem.get 22).toNat ≤ 57)
    (hne : s.mem.get 22 ≠ 48)
    (hcode : ∀ k : Nat, 570 ≤ k → k < 867 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s34 := runN s 34
    s34.pc = 867 ∧
    s34.halted = false ∧
    s34.mem.get 0 = 0 ∧
    s34.mem.get 25 = 3 ∧
    (∀ a, a ≠ 18 → a ≠ 25 → a ≠ 31 → a ≠ 0 → s34.mem.get a = s.mem.get a) := by
  intro s34
  have ht0 := ndig_test_Q0_zero (s := s) hpc hh hZ hK48 hQ0
    (fun k h1 h2 => hcode k h1 (by omega))
  let s6 := runN s 6
  have hs6pc : s6.pc = 591 := ht0.1
  have hs6h : s6.halted = false := ht0.2.1
  have hs6Z : s6.mem.get 0 = 0 := ht0.2.2.1
  have hpres6 := ht0.2.2.2.2
  have hK6 : s6.mem.get 8 = 48 := (hpres6 8 (by decide) (by decide)).trans hK48
  have hQ1_6 : s6.mem.get 21 = 48 := (hpres6 21 (by decide) (by decide)).trans hQ1
  have g6 := ndig_code_shrink_T (s := s) (s' := s6) (lo := 591) (hi := 609)
    hpres6 hcode (by decide) (by decide)
  have ht1 := ndig_test_Q1_zero (s := s6) hs6pc hs6h hs6Z hK6 hQ1_6 g6
  have hrun12 : runN s 12 = runN s6 6 := runN_add_eq s 6 6 12 (by decide)
  let s12 := runN s 12
  have hs12pc : s12.pc = 612 := by
    have : s12 = runN s6 6 := hrun12
    rw [this]; exact ht1.1
  have hs12h : s12.halted = false := by
    have : s12 = runN s6 6 := hrun12
    rw [this]; exact ht1.2.1
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = runN s6 6 := hrun12
    rw [this]; exact ht1.2.2.1
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = runN s6 6 := hrun12
    rw [this]
    exact (ht1.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hK12 : s12.mem.get 8 = 48 := (hpres12 8 (by decide) (by decide)).trans hK48
  have hQ2_12 : s12.mem.get 22 = s.mem.get 22 := hpres12 22 (by decide) (by decide)
  have hlo12 : 48 ≤ (s12.mem.get 22).toNat := by rw [hQ2_12]; exact hlo
  have hhi12 : (s12.mem.get 22).toNat ≤ 57 := by rw [hQ2_12]; exact hhi
  have hne12 : s12.mem.get 22 ≠ 48 := by rw [hQ2_12]; exact hne
  have g12 := ndig_code_shrink_T (s := s) (s' := s12) (lo := 612) (hi := 633)
    hpres12 hcode (by decide) (by decide)
  have ht2 := ndig_test_Q2_nz (s := s12) hs12pc hs12h hs12Z hK12 hlo12 hhi12 hne12 g12
  have hrun19 : runN s 19 = runN s12 7 := runN_add_eq s 12 7 19 (by decide)
  let s19 := runN s 19
  have hs19pc : s19.pc = 774 := by
    have : s19 = runN s12 7 := hrun19
    rw [this]; exact ht2.1
  have hs19h : s19.halted = false := by
    have : s19 = runN s12 7 := hrun19
    rw [this]; exact ht2.2.1
  have hs19Z : s19.mem.get 0 = 0 := by
    have : s19 = runN s12 7 := hrun19
    rw [this]; exact ht2.2.2.1
  have hpres19 : ∀ a, a ≠ 18 → a ≠ 0 → s19.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s19 = runN s12 7 := hrun19
    rw [this]
    exact (ht2.2.2.2 a ha18 ha0).trans (hpres12 a ha18 ha0)
  have hONE19 : s19.mem.get 3 = 1 := (hpres19 3 (by decide) (by decide)).trans hONE
  have g19 := ndig_code_shrink_T (s := s) (s' := s19) (lo := 774) (hi := 819)
    hpres19 hcode (by decide) (by decide)
  have hb := ndig_build_three (s := s19) hs19pc hs19h hs19Z hONE19 g19
  have hrun : s34 = runN s19 15 := runN_add_eq s 19 15 34 (by decide)
  have hs34pc : s34.pc = 867 := by rw [hrun]; exact hb.1
  have hs34h : s34.halted = false := by rw [hrun]; exact hb.2.1
  have hs34Z : s34.mem.get 0 = 0 := by rw [hrun]; exact hb.2.2.1
  have hs34N : s34.mem.get 25 = 3 := by rw [hrun]; exact hb.2.2.2.1
  have hpres : ∀ a, a ≠ 18 → a ≠ 25 → a ≠ 31 → a ≠ 0 → s34.mem.get a = s.mem.get a := by
    intro a ha18 ha25 ha31 ha0
    rw [hrun]
    exact (hb.2.2.2.2 a ha25 ha31 ha0).trans (hpres19 a ha18 ha0)
  exact ⟨hs34pc, hs34h, hs34Z, hs34N, hpres⟩

/-- `NDIG = 2` when `Q0 = Q1 = Q2 = '0'` and `Q3` is a non-zero ASCII digit. 37 steps. -/
theorem ndig_two {s : Machine}
    (hpc : s.pc = 570)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hQ0 : s.mem.get 20 = 48)
    (hQ1 : s.mem.get 21 = 48)
    (hQ2 : s.mem.get 22 = 48)
    (hlo : 48 ≤ (s.mem.get 23).toNat)
    (hhi : (s.mem.get 23).toNat ≤ 57)
    (hne : s.mem.get 23 ≠ 48)
    (hcode : ∀ k : Nat, 570 ≤ k → k < 867 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s37 := runN s 37
    s37.pc = 867 ∧
    s37.halted = false ∧
    s37.mem.get 0 = 0 ∧
    s37.mem.get 25 = 2 ∧
    (∀ a, a ≠ 18 → a ≠ 25 → a ≠ 31 → a ≠ 0 → s37.mem.get a = s.mem.get a) := by
  intro s37
  have ht0 := ndig_test_Q0_zero (s := s) hpc hh hZ hK48 hQ0
    (fun k h1 h2 => hcode k h1 (by omega))
  let s6 := runN s 6
  have hs6pc : s6.pc = 591 := ht0.1
  have hs6h : s6.halted = false := ht0.2.1
  have hs6Z : s6.mem.get 0 = 0 := ht0.2.2.1
  have hpres6 := ht0.2.2.2.2
  have hK6 : s6.mem.get 8 = 48 := (hpres6 8 (by decide) (by decide)).trans hK48
  have hQ1_6 : s6.mem.get 21 = 48 := (hpres6 21 (by decide) (by decide)).trans hQ1
  have g6 := ndig_code_shrink_T (s := s) (s' := s6) (lo := 591) (hi := 609)
    hpres6 hcode (by decide) (by decide)
  have ht1 := ndig_test_Q1_zero (s := s6) hs6pc hs6h hs6Z hK6 hQ1_6 g6
  have hrun12 : runN s 12 = runN s6 6 := runN_add_eq s 6 6 12 (by decide)
  let s12 := runN s 12
  have hs12pc : s12.pc = 612 := by
    have : s12 = runN s6 6 := hrun12
    rw [this]; exact ht1.1
  have hs12h : s12.halted = false := by
    have : s12 = runN s6 6 := hrun12
    rw [this]; exact ht1.2.1
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = runN s6 6 := hrun12
    rw [this]; exact ht1.2.2.1
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = runN s6 6 := hrun12
    rw [this]
    exact (ht1.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hK12 : s12.mem.get 8 = 48 := (hpres12 8 (by decide) (by decide)).trans hK48
  have hQ2_12 : s12.mem.get 22 = 48 := (hpres12 22 (by decide) (by decide)).trans hQ2
  have g12 := ndig_code_shrink_T (s := s) (s' := s12) (lo := 612) (hi := 630)
    hpres12 hcode (by decide) (by decide)
  have ht2 := ndig_test_Q2_zero (s := s12) hs12pc hs12h hs12Z hK12 hQ2_12 g12
  have hrun18 : runN s 18 = runN s12 6 := runN_add_eq s 12 6 18 (by decide)
  let s18 := runN s 18
  have hs18pc : s18.pc = 633 := by
    have : s18 = runN s12 6 := hrun18
    rw [this]; exact ht2.1
  have hs18h : s18.halted = false := by
    have : s18 = runN s12 6 := hrun18
    rw [this]; exact ht2.2.1
  have hs18Z : s18.mem.get 0 = 0 := by
    have : s18 = runN s12 6 := hrun18
    rw [this]; exact ht2.2.2.1
  have hpres18 : ∀ a, a ≠ 18 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s18 = runN s12 6 := hrun18
    rw [this]
    exact (ht2.2.2.2.2 a ha18 ha0).trans (hpres12 a ha18 ha0)
  have hK18 : s18.mem.get 8 = 48 := (hpres18 8 (by decide) (by decide)).trans hK48
  have hQ3_18 : s18.mem.get 23 = s.mem.get 23 := hpres18 23 (by decide) (by decide)
  have hlo18 : 48 ≤ (s18.mem.get 23).toNat := by rw [hQ3_18]; exact hlo
  have hhi18 : (s18.mem.get 23).toNat ≤ 57 := by rw [hQ3_18]; exact hhi
  have hne18 : s18.mem.get 23 ≠ 48 := by rw [hQ3_18]; exact hne
  have g18 := ndig_code_shrink_T (s := s) (s' := s18) (lo := 633) (hi := 654)
    hpres18 hcode (by decide) (by decide)
  have ht3 := ndig_test_Q3_nz (s := s18) hs18pc hs18h hs18Z hK18 hlo18 hhi18 hne18 g18
  have hrun25 : runN s 25 = runN s18 7 := runN_add_eq s 18 7 25 (by decide)
  let s25 := runN s 25
  have hs25pc : s25.pc = 819 := by
    have : s25 = runN s18 7 := hrun25
    rw [this]; exact ht3.1
  have hs25h : s25.halted = false := by
    have : s25 = runN s18 7 := hrun25
    rw [this]; exact ht3.2.1
  have hs25Z : s25.mem.get 0 = 0 := by
    have : s25 = runN s18 7 := hrun25
    rw [this]; exact ht3.2.2.1
  have hpres25 : ∀ a, a ≠ 18 → a ≠ 0 → s25.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s25 = runN s18 7 := hrun25
    rw [this]
    exact (ht3.2.2.2 a ha18 ha0).trans (hpres18 a ha18 ha0)
  have hONE25 : s25.mem.get 3 = 1 := (hpres25 3 (by decide) (by decide)).trans hONE
  have g25 := ndig_code_shrink_T (s := s) (s' := s25) (lo := 819) (hi := 855)
    hpres25 hcode (by decide) (by decide)
  have hb := ndig_build_two (s := s25) hs25pc hs25h hs25Z hONE25 g25
  have hrun : s37 = runN s25 12 := runN_add_eq s 25 12 37 (by decide)
  have hs37pc : s37.pc = 867 := by rw [hrun]; exact hb.1
  have hs37h : s37.halted = false := by rw [hrun]; exact hb.2.1
  have hs37Z : s37.mem.get 0 = 0 := by rw [hrun]; exact hb.2.2.1
  have hs37N : s37.mem.get 25 = 2 := by rw [hrun]; exact hb.2.2.2.1
  have hpres : ∀ a, a ≠ 18 → a ≠ 25 → a ≠ 31 → a ≠ 0 → s37.mem.get a = s.mem.get a := by
    intro a ha18 ha25 ha31 ha0
    rw [hrun]
    exact (hb.2.2.2.2 a ha25 ha31 ha0).trans (hpres25 a ha18 ha0)
  exact ⟨hs37pc, hs37h, hs37Z, hs37N, hpres⟩

/-- `NDIG = 1` when `Q0 = Q1 = Q2 = Q3 = '0'`. 29 steps, 570 → 867. -/
theorem ndig_one {s : Machine}
    (hpc : s.pc = 570)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hQ0 : s.mem.get 20 = 48)
    (hQ1 : s.mem.get 21 = 48)
    (hQ2 : s.mem.get 22 = 48)
    (hQ3 : s.mem.get 23 = 48)
    (hcode : ∀ k : Nat, 570 ≤ k → k < 867 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s29 := runN s 29
    s29.pc = 867 ∧
    s29.halted = false ∧
    s29.mem.get 0 = 0 ∧
    s29.mem.get 25 = 1 ∧
    (∀ a, a ≠ 18 → a ≠ 25 → a ≠ 0 → s29.mem.get a = s.mem.get a) := by
  intro s29
  have ht0 := ndig_test_Q0_zero (s := s) hpc hh hZ hK48 hQ0
    (fun k h1 h2 => hcode k h1 (by omega))
  let s6 := runN s 6
  have hs6pc : s6.pc = 591 := ht0.1
  have hs6h : s6.halted = false := ht0.2.1
  have hs6Z : s6.mem.get 0 = 0 := ht0.2.2.1
  have hpres6 := ht0.2.2.2.2
  have hK6 : s6.mem.get 8 = 48 := (hpres6 8 (by decide) (by decide)).trans hK48
  have hQ1_6 : s6.mem.get 21 = 48 := (hpres6 21 (by decide) (by decide)).trans hQ1
  have g6 := ndig_code_shrink_T (s := s) (s' := s6) (lo := 591) (hi := 609)
    hpres6 hcode (by decide) (by decide)
  have ht1 := ndig_test_Q1_zero (s := s6) hs6pc hs6h hs6Z hK6 hQ1_6 g6
  have hrun12 : runN s 12 = runN s6 6 := runN_add_eq s 6 6 12 (by decide)
  let s12 := runN s 12
  have hs12pc : s12.pc = 612 := by
    have : s12 = runN s6 6 := hrun12
    rw [this]; exact ht1.1
  have hs12h : s12.halted = false := by
    have : s12 = runN s6 6 := hrun12
    rw [this]; exact ht1.2.1
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = runN s6 6 := hrun12
    rw [this]; exact ht1.2.2.1
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = runN s6 6 := hrun12
    rw [this]
    exact (ht1.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hK12 : s12.mem.get 8 = 48 := (hpres12 8 (by decide) (by decide)).trans hK48
  have hQ2_12 : s12.mem.get 22 = 48 := (hpres12 22 (by decide) (by decide)).trans hQ2
  have g12 := ndig_code_shrink_T (s := s) (s' := s12) (lo := 612) (hi := 630)
    hpres12 hcode (by decide) (by decide)
  have ht2 := ndig_test_Q2_zero (s := s12) hs12pc hs12h hs12Z hK12 hQ2_12 g12
  have hrun18 : runN s 18 = runN s12 6 := runN_add_eq s 12 6 18 (by decide)
  let s18 := runN s 18
  have hs18pc : s18.pc = 633 := by
    have : s18 = runN s12 6 := hrun18
    rw [this]; exact ht2.1
  have hs18h : s18.halted = false := by
    have : s18 = runN s12 6 := hrun18
    rw [this]; exact ht2.2.1
  have hs18Z : s18.mem.get 0 = 0 := by
    have : s18 = runN s12 6 := hrun18
    rw [this]; exact ht2.2.2.1
  have hpres18 : ∀ a, a ≠ 18 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s18 = runN s12 6 := hrun18
    rw [this]
    exact (ht2.2.2.2.2 a ha18 ha0).trans (hpres12 a ha18 ha0)
  have hK18 : s18.mem.get 8 = 48 := (hpres18 8 (by decide) (by decide)).trans hK48
  have hQ3_18 : s18.mem.get 23 = 48 := (hpres18 23 (by decide) (by decide)).trans hQ3
  have g18 := ndig_code_shrink_T (s := s) (s' := s18) (lo := 633) (hi := 651)
    hpres18 hcode (by decide) (by decide)
  have ht3 := ndig_test_Q3_zero (s := s18) hs18pc hs18h hs18Z hK18 hQ3_18 g18
  have hrun24 : runN s 24 = runN s18 6 := runN_add_eq s 18 6 24 (by decide)
  let s24 := runN s 24
  have hs24pc : s24.pc = 654 := by
    have : s24 = runN s18 6 := hrun24
    rw [this]; exact ht3.1
  have hs24h : s24.halted = false := by
    have : s24 = runN s18 6 := hrun24
    rw [this]; exact ht3.2.1
  have hs24Z : s24.mem.get 0 = 0 := by
    have : s24 = runN s18 6 := hrun24
    rw [this]; exact ht3.2.2.1
  have hpres24 : ∀ a, a ≠ 18 → a ≠ 0 → s24.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s24 = runN s18 6 := hrun24
    rw [this]
    exact (ht3.2.2.2.2 a ha18 ha0).trans (hpres18 a ha18 ha0)
  have g24 := ndig_code_shrink_T (s := s) (s' := s24) (lo := 654) (hi := 657)
    hpres24 hcode (by decide) (by decide)
  have hj := ndig_s4_jmp (s := s24) hs24pc hs24h hs24Z g24
  have hrun25 : runN s 25 = runN s24 1 := runN_add_eq s 24 1 25 (by decide)
  let s25 := runN s 25
  have hs25pc : s25.pc = 855 := by
    have : s25 = runN s24 1 := hrun25
    rw [this]; exact hj.1
  have hs25h : s25.halted = false := by
    have : s25 = runN s24 1 := hrun25
    rw [this]; exact hj.2.1
  have hs25Z : s25.mem.get 0 = 0 := by
    have : s25 = runN s24 1 := hrun25
    rw [this]; exact hj.2.2.1
  have hpres25 : ∀ a, a ≠ 18 → a ≠ 0 → s25.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s25 = runN s24 1 := hrun25
    rw [this]
    exact (hj.2.2.2 a).trans (hpres24 a ha18 ha0)
  have hONE25 : s25.mem.get 3 = 1 := (hpres25 3 (by decide) (by decide)).trans hONE
  have g25 := ndig_code_shrink_T (s := s) (s' := s25) (lo := 855) (hi := 867)
    hpres25 hcode (by decide) (by decide)
  have hb := ndig_build_one (s := s25) hs25pc hs25h hs25Z hONE25 g25
  have hrun : s29 = runN s25 4 := runN_add_eq s 25 4 29 (by decide)
  have hs29pc : s29.pc = 867 := by rw [hrun]; exact hb.1
  have hs29h : s29.halted = false := by rw [hrun]; exact hb.2.1
  have hs29Z : s29.mem.get 0 = 0 := by rw [hrun]; exact hb.2.2.1
  have hs29N : s29.mem.get 25 = 1 := by rw [hrun]; exact hb.2.2.2.1
  have hpres : ∀ a, a ≠ 18 → a ≠ 25 → a ≠ 0 → s29.mem.get a = s.mem.get a := by
    intro a ha18 ha25 ha0
    rw [hrun]
    exact (hb.2.2.2.2 a ha25 ha0).trans (hpres25 a ha18 ha0)
  exact ⟨hs29pc, hs29h, hs29Z, hs29N, hpres⟩

end IntFmt
