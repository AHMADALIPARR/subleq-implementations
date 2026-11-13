/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

ASCII conversion of the five place quotients at `P3_DONE`.
Block lemmas, not end-to-end correctness.
-/

import IntFmt.PlaceCore
import IntFmt.DecChunksA

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000


private theorem cell512 (off : Nat) (h : off < 16) :
    intfmtImage[512 + off]! = decChunk032[off]! :=
  extract_chunk 512 decChunk032 image_chunk032 off h (by decide)


private theorem cell528 (off : Nat) (h : off < 16) :
    intfmtImage[528 + off]! = decChunk033[off]! :=
  extract_chunk 528 decChunk033 image_chunk033 off h (by decide)


private theorem cell544 (off : Nat) (h : off < 16) :
    intfmtImage[544 + off]! = decChunk034[off]! :=
  extract_chunk 544 decChunk034 image_chunk034 off h (by decide)


private theorem cell560 (off : Nat) (h : off < 16) :
    intfmtImage[560 + off]! = decChunk035[off]! :=
  extract_chunk 560 decChunk035 image_chunk035 off h (by decide)


/-- `MOV N Q4` at `P3_DONE` (pc 513), 4 steps, exit pc 525. -/
theorem ascii_mov_N_Q4 {s : Machine}
    (hpc : s.pc = 513)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 513 ≤ k → k < 525 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 525 ∧
    s4.halted = false ∧
    s4.mem.get 24 = s.mem.get 17 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 17 = s.mem.get 17 ∧
    (∀ a, a ≠ 24 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 513 :=
    hpc.trans (rfl : (513 : Word) = UInt16.ofNat 513)
  have g (k : Nat) (h1 : 513 ≤ k) (h2 : k < 525) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (513 + off) :=
    word_pc_off 513 off hp (by omega)
  have m0 : s.mem.get s.pc = 24 := by
    rw [hp]
    have hval : decChunk032[1]! = 24 := rfl
    exact (g 513 (by decide) (by decide)).trans ((cell512 1 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 24 := by
    rw [poff 1 (by decide)]
    have hval : decChunk032[2]! = 24 := rfl
    exact (g 514 (by decide) (by decide)).trans ((cell512 2 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk032[3]! = 516 := rfl
    have hv : (516 : Word) = UInt16.ofNat 516 := rfl
    exact (g 515 (by decide) (by decide)).trans ((cell512 3 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 17 := by
    rw [poff 3 (by decide)]
    have hval : decChunk032[4]! = 17 := rfl
    exact (g 516 (by decide) (by decide)).trans ((cell512 4 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk032[5]! = 0 := rfl
    exact (g 517 (by decide) (by decide)).trans ((cell512 5 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk032[6]! = 519 := rfl
    have hv : (519 : Word) = UInt16.ofNat 519 := rfl
    exact (g 518 (by decide) (by decide)).trans ((cell512 6 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk032[7]! = 0 := rfl
    exact (g 519 (by decide) (by decide)).trans ((cell512 7 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 24 := by
    rw [poff 7 (by decide)]
    have hval : decChunk032[8]! = 24 := rfl
    exact (g 520 (by decide) (by decide)).trans ((cell512 8 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk032[9]! = 522 := rfl
    have hv : (522 : Word) = UInt16.ofNat 522 := rfl
    exact (g 521 (by decide) (by decide)).trans ((cell512 9 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk032[10]! = 0 := rfl
    exact (g 522 (by decide) (by decide)).trans ((cell512 10 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk032[11]! = 0 := rfl
    exact (g 523 (by decide) (by decide)).trans ((cell512 11 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk032[12]! = 525 := rfl
    have hv : (525 : Word) = UInt16.ofNat 525 := rfl
    exact (g 524 (by decide) (by decide)).trans ((cell512 12 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (24 : Word) := by
    intro i hi
    have : (24 : Word) = UInt16.ofNat 24 := rfl
    rw [this]
    exact pc_off_ne 513 i 24 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 513 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 17) (dst := 24)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 525 := by
    have hadd : s.pc + UInt16.ofNat 12 = (525 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 525 = (525 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- `ADD K48 Q0` at pc 525, 3 steps, exit pc 534. -/
theorem ascii_add_K48_Q0 {s : Machine}
    (hpc : s.pc = 525)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hcode : ∀ k : Nat, 525 ≤ k → k < 534 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 534 ∧
    s3.halted = false ∧
    s3.mem.get 20 = s.mem.get 20 + 48 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 20 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 525 :=
    hpc.trans (rfl : (525 : Word) = UInt16.ofNat 525)
  have g (k : Nat) (h1 : 525 ≤ k) (h2 : k < 534) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (525 + off) :=
    word_pc_off 525 off hp (by omega)
  have i0 : s.mem.get s.pc = 8 := by
    rw [hp]
    have hval : decChunk032[13]! = 8 := rfl
    exact (g 525 (by decide) (by decide)).trans ((cell512 13 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk032[14]! = 0 := rfl
    exact (g 526 (by decide) (by decide)).trans ((cell512 14 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk032[15]! = 528 := rfl
    have hv : (528 : Word) = UInt16.ofNat 528 := rfl
    exact (g 527 (by decide) (by decide)).trans ((cell512 15 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk033[0]! = 0 := rfl
    exact (g 528 (by decide) (by decide)).trans ((cell528 0 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 20 := by
    rw [poff 4 (by decide)]
    have hval : decChunk033[1]! = 20 := rfl
    exact (g 529 (by decide) (by decide)).trans ((cell528 1 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk033[2]! = 531 := rfl
    have hv : (531 : Word) = UInt16.ofNat 531 := rfl
    exact (g 530 (by decide) (by decide)).trans ((cell528 2 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk033[3]! = 0 := rfl
    exact (g 531 (by decide) (by decide)).trans ((cell528 3 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk033[4]! = 0 := rfl
    exact (g 532 (by decide) (by decide)).trans ((cell528 4 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk033[5]! = 534 := rfl
    have hv : (534 : Word) = UInt16.ofNat 534 := rfl
    exact (g 533 (by decide) (by decide)).trans ((cell528 5 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (20 : Word) := by
    intro i hi
    have : (20 : Word) = UInt16.ofNat 20 := rfl
    rw [this]
    exact pc_off_ne 525 i 20 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 525 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 8) (dst := 20)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 534 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (534 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 534 = (534 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 20 = s.mem.get 20 + 48 := by
    have : s.mem.get 20 + s.mem.get 8 = s.mem.get 20 + 48 := by
      rw [hK48]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- `ADD K48 Q1` at pc 534, 3 steps, exit pc 543. -/
theorem ascii_add_K48_Q1 {s : Machine}
    (hpc : s.pc = 534)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hcode : ∀ k : Nat, 534 ≤ k → k < 543 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 543 ∧
    s3.halted = false ∧
    s3.mem.get 21 = s.mem.get 21 + 48 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 21 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 534 :=
    hpc.trans (rfl : (534 : Word) = UInt16.ofNat 534)
  have g (k : Nat) (h1 : 534 ≤ k) (h2 : k < 543) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (534 + off) :=
    word_pc_off 534 off hp (by omega)
  have i0 : s.mem.get s.pc = 8 := by
    rw [hp]
    have hval : decChunk033[6]! = 8 := rfl
    exact (g 534 (by decide) (by decide)).trans ((cell528 6 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk033[7]! = 0 := rfl
    exact (g 535 (by decide) (by decide)).trans ((cell528 7 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk033[8]! = 537 := rfl
    have hv : (537 : Word) = UInt16.ofNat 537 := rfl
    exact (g 536 (by decide) (by decide)).trans ((cell528 8 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk033[9]! = 0 := rfl
    exact (g 537 (by decide) (by decide)).trans ((cell528 9 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 21 := by
    rw [poff 4 (by decide)]
    have hval : decChunk033[10]! = 21 := rfl
    exact (g 538 (by decide) (by decide)).trans ((cell528 10 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk033[11]! = 540 := rfl
    have hv : (540 : Word) = UInt16.ofNat 540 := rfl
    exact (g 539 (by decide) (by decide)).trans ((cell528 11 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk033[12]! = 0 := rfl
    exact (g 540 (by decide) (by decide)).trans ((cell528 12 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk033[13]! = 0 := rfl
    exact (g 541 (by decide) (by decide)).trans ((cell528 13 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk033[14]! = 543 := rfl
    have hv : (543 : Word) = UInt16.ofNat 543 := rfl
    exact (g 542 (by decide) (by decide)).trans ((cell528 14 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (21 : Word) := by
    intro i hi
    have : (21 : Word) = UInt16.ofNat 21 := rfl
    rw [this]
    exact pc_off_ne 534 i 21 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 534 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 8) (dst := 21)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 543 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (543 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 543 = (543 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 21 = s.mem.get 21 + 48 := by
    have : s.mem.get 21 + s.mem.get 8 = s.mem.get 21 + 48 := by
      rw [hK48]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- `ADD K48 Q2` at pc 543, 3 steps, exit pc 552. -/
theorem ascii_add_K48_Q2 {s : Machine}
    (hpc : s.pc = 543)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hcode : ∀ k : Nat, 543 ≤ k → k < 552 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 552 ∧
    s3.halted = false ∧
    s3.mem.get 22 = s.mem.get 22 + 48 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 22 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 543 :=
    hpc.trans (rfl : (543 : Word) = UInt16.ofNat 543)
  have g (k : Nat) (h1 : 543 ≤ k) (h2 : k < 552) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (543 + off) :=
    word_pc_off 543 off hp (by omega)
  have i0 : s.mem.get s.pc = 8 := by
    rw [hp]
    have hval : decChunk033[15]! = 8 := rfl
    exact (g 543 (by decide) (by decide)).trans ((cell528 15 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk034[0]! = 0 := rfl
    exact (g 544 (by decide) (by decide)).trans ((cell544 0 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk034[1]! = 546 := rfl
    have hv : (546 : Word) = UInt16.ofNat 546 := rfl
    exact (g 545 (by decide) (by decide)).trans ((cell544 1 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk034[2]! = 0 := rfl
    exact (g 546 (by decide) (by decide)).trans ((cell544 2 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 22 := by
    rw [poff 4 (by decide)]
    have hval : decChunk034[3]! = 22 := rfl
    exact (g 547 (by decide) (by decide)).trans ((cell544 3 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk034[4]! = 549 := rfl
    have hv : (549 : Word) = UInt16.ofNat 549 := rfl
    exact (g 548 (by decide) (by decide)).trans ((cell544 4 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk034[5]! = 0 := rfl
    exact (g 549 (by decide) (by decide)).trans ((cell544 5 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk034[6]! = 0 := rfl
    exact (g 550 (by decide) (by decide)).trans ((cell544 6 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk034[7]! = 552 := rfl
    have hv : (552 : Word) = UInt16.ofNat 552 := rfl
    exact (g 551 (by decide) (by decide)).trans ((cell544 7 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (22 : Word) := by
    intro i hi
    have : (22 : Word) = UInt16.ofNat 22 := rfl
    rw [this]
    exact pc_off_ne 543 i 22 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 543 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 8) (dst := 22)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 552 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (552 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 552 = (552 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 22 = s.mem.get 22 + 48 := by
    have : s.mem.get 22 + s.mem.get 8 = s.mem.get 22 + 48 := by
      rw [hK48]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- `ADD K48 Q3` at pc 552, 3 steps, exit pc 561. -/
theorem ascii_add_K48_Q3 {s : Machine}
    (hpc : s.pc = 552)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hcode : ∀ k : Nat, 552 ≤ k → k < 561 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 561 ∧
    s3.halted = false ∧
    s3.mem.get 23 = s.mem.get 23 + 48 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 23 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 552 :=
    hpc.trans (rfl : (552 : Word) = UInt16.ofNat 552)
  have g (k : Nat) (h1 : 552 ≤ k) (h2 : k < 561) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (552 + off) :=
    word_pc_off 552 off hp (by omega)
  have i0 : s.mem.get s.pc = 8 := by
    rw [hp]
    have hval : decChunk034[8]! = 8 := rfl
    exact (g 552 (by decide) (by decide)).trans ((cell544 8 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk034[9]! = 0 := rfl
    exact (g 553 (by decide) (by decide)).trans ((cell544 9 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk034[10]! = 555 := rfl
    have hv : (555 : Word) = UInt16.ofNat 555 := rfl
    exact (g 554 (by decide) (by decide)).trans ((cell544 10 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk034[11]! = 0 := rfl
    exact (g 555 (by decide) (by decide)).trans ((cell544 11 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 23 := by
    rw [poff 4 (by decide)]
    have hval : decChunk034[12]! = 23 := rfl
    exact (g 556 (by decide) (by decide)).trans ((cell544 12 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk034[13]! = 558 := rfl
    have hv : (558 : Word) = UInt16.ofNat 558 := rfl
    exact (g 557 (by decide) (by decide)).trans ((cell544 13 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk034[14]! = 0 := rfl
    exact (g 558 (by decide) (by decide)).trans ((cell544 14 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk034[15]! = 0 := rfl
    exact (g 559 (by decide) (by decide)).trans ((cell544 15 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk035[0]! = 561 := rfl
    have hv : (561 : Word) = UInt16.ofNat 561 := rfl
    exact (g 560 (by decide) (by decide)).trans ((cell560 0 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (23 : Word) := by
    intro i hi
    have : (23 : Word) = UInt16.ofNat 23 := rfl
    rw [this]
    exact pc_off_ne 552 i 23 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 552 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 8) (dst := 23)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 561 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (561 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 561 = (561 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 23 = s.mem.get 23 + 48 := by
    have : s.mem.get 23 + s.mem.get 8 = s.mem.get 23 + 48 := by
      rw [hK48]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- `ADD K48 Q4` at pc 561, 3 steps, exit pc 570. -/
theorem ascii_add_K48_Q4 {s : Machine}
    (hpc : s.pc = 561)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hcode : ∀ k : Nat, 561 ≤ k → k < 570 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 570 ∧
    s3.halted = false ∧
    s3.mem.get 24 = s.mem.get 24 + 48 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 24 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 561 :=
    hpc.trans (rfl : (561 : Word) = UInt16.ofNat 561)
  have g (k : Nat) (h1 : 561 ≤ k) (h2 : k < 570) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (561 + off) :=
    word_pc_off 561 off hp (by omega)
  have i0 : s.mem.get s.pc = 8 := by
    rw [hp]
    have hval : decChunk035[1]! = 8 := rfl
    exact (g 561 (by decide) (by decide)).trans ((cell560 1 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk035[2]! = 0 := rfl
    exact (g 562 (by decide) (by decide)).trans ((cell560 2 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk035[3]! = 564 := rfl
    have hv : (564 : Word) = UInt16.ofNat 564 := rfl
    exact (g 563 (by decide) (by decide)).trans ((cell560 3 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk035[4]! = 0 := rfl
    exact (g 564 (by decide) (by decide)).trans ((cell560 4 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 24 := by
    rw [poff 4 (by decide)]
    have hval : decChunk035[5]! = 24 := rfl
    exact (g 565 (by decide) (by decide)).trans ((cell560 5 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk035[6]! = 567 := rfl
    have hv : (567 : Word) = UInt16.ofNat 567 := rfl
    exact (g 566 (by decide) (by decide)).trans ((cell560 6 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk035[7]! = 0 := rfl
    exact (g 567 (by decide) (by decide)).trans ((cell560 7 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk035[8]! = 0 := rfl
    exact (g 568 (by decide) (by decide)).trans ((cell560 8 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk035[9]! = 570 := rfl
    have hv : (570 : Word) = UInt16.ofNat 570 := rfl
    exact (g 569 (by decide) (by decide)).trans ((cell560 9 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (24 : Word) := by
    intro i hi
    have : (24 : Word) = UInt16.ofNat 24 := rfl
    rw [this]
    exact pc_off_ne 561 i 24 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 561 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 8) (dst := 24)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 570 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (570 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 570 = (570 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 24 = s.mem.get 24 + 48 := by
    have : s.mem.get 24 + s.mem.get 8 = s.mem.get 24 + 48 := by
      rw [hK48]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩


/-- From `P3_DONE`, store the ones digit in `Q4` and add `'0'` (48) to
`Q0`..`Q4` in 19 steps, arriving at pc 570. -/
theorem ascii_convert {s : Machine}
    (hpc : s.pc = 513)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK48 : s.mem.get 8 = 48)
    (hcode : ∀ k : Nat, 513 ≤ k → k < 570 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s19 := runN s 19
    s19.pc = 570 ∧
    s19.halted = false ∧
    s19.mem.get 0 = 0 ∧
    s19.mem.get 24 = s.mem.get 17 + 48 ∧
    s19.mem.get 20 = s.mem.get 20 + 48 ∧
    s19.mem.get 21 = s.mem.get 21 + 48 ∧
    s19.mem.get 22 = s.mem.get 22 + 48 ∧
    s19.mem.get 23 = s.mem.get 23 + 48 ∧
    s19.mem.get 17 = s.mem.get 17 ∧
    (∀ a, a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 0 →
      s19.mem.get a = s.mem.get a) := by
  intro s19
  have hmov :=
    ascii_mov_N_Q4 (s := s) hpc hh hZ (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 525 := hmov.1
  have hs4h := hmov.2.1
  have hQ44 : s4.mem.get 24 = s.mem.get 17 := hmov.2.2.1
  have hZ4 := hmov.2.2.2.1
  have hN4 : s4.mem.get 17 = s.mem.get 17 := hmov.2.2.2.2.1
  have hpres4 := hmov.2.2.2.2.2
  have hK4 : s4.mem.get 8 = 48 := (hpres4 8 (by decide) (by decide)).trans hK48
  have g4 (k : Nat) (h1 : 525 ≤ k) (h2 : k < 570) :
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres4 (UInt16.ofNat k) (ofNat_ne k 24 (by omega) (by decide) (by omega))
      (ofNat_ne k 0 (by omega) (by decide) (by omega))).trans (hcode k (by omega) h2)
  have ha0 :=
    ascii_add_K48_Q0 (s := s4) hs4pc hs4h hZ4 hK4 (fun k h1 h2 => g4 k h1 (by omega))
  let s7 := runN s4 3
  have hs7pc : s7.pc = 534 := ha0.1
  have hs7h := ha0.2.1
  have hQ07 : s7.mem.get 20 = s.mem.get 20 + 48 := by
    have : s4.mem.get 20 = s.mem.get 20 := hpres4 20 (by decide) (by decide)
    exact ha0.2.2.1.trans (by rw [this])
  have hZ7 := ha0.2.2.2.1
  have hpres7 : ∀ a, a ≠ 20 → a ≠ 24 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha20 ha24 haZ
    exact (ha0.2.2.2.2 a ha20 haZ).trans (hpres4 a ha24 haZ)
  have hK7 : s7.mem.get 8 = 48 := (hpres7 8 (by decide) (by decide) (by decide)).trans hK48
  have hQ47 : s7.mem.get 24 = s.mem.get 17 :=
    (ha0.2.2.2.2 24 (by decide) (by decide)).trans hQ44
  have g7 (k : Nat) (h1 : 534 ≤ k) (h2 : k < 570) :
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres7 (UInt16.ofNat k) (ofNat_ne k 20 (by omega) (by decide) (by omega))
      (ofNat_ne k 24 (by omega) (by decide) (by omega))
      (ofNat_ne k 0 (by omega) (by decide) (by omega))).trans (hcode k (by omega) h2)
  have ha1 :=
    ascii_add_K48_Q1 (s := s7) hs7pc hs7h hZ7 hK7 (fun k h1 h2 => g7 k h1 (by omega))
  let s10 := runN s7 3
  have hs10pc : s10.pc = 543 := ha1.1
  have hs10h := ha1.2.1
  have hQ110 : s10.mem.get 21 = s.mem.get 21 + 48 := by
    have : s7.mem.get 21 = s.mem.get 21 := hpres7 21 (by decide) (by decide) (by decide)
    exact ha1.2.2.1.trans (by rw [this])
  have hZ10 := ha1.2.2.2.1
  have hpres10 : ∀ a, a ≠ 21 → a ≠ 20 → a ≠ 24 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha21 ha20 ha24 haZ
    exact (ha1.2.2.2.2 a ha21 haZ).trans (hpres7 a ha20 ha24 haZ)
  have hK10 : s10.mem.get 8 = 48 :=
    (hpres10 8 (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hQ010 : s10.mem.get 20 = s.mem.get 20 + 48 :=
    (ha1.2.2.2.2 20 (by decide) (by decide)).trans hQ07
  have hQ410 : s10.mem.get 24 = s.mem.get 17 :=
    (ha1.2.2.2.2 24 (by decide) (by decide)).trans hQ47
  have g10 (k : Nat) (h1 : 543 ≤ k) (h2 : k < 570) :
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres10 (UInt16.ofNat k) (ofNat_ne k 21 (by omega) (by decide) (by omega))
      (ofNat_ne k 20 (by omega) (by decide) (by omega))
      (ofNat_ne k 24 (by omega) (by decide) (by omega))
      (ofNat_ne k 0 (by omega) (by decide) (by omega))).trans (hcode k (by omega) h2)
  have ha2 :=
    ascii_add_K48_Q2 (s := s10) hs10pc hs10h hZ10 hK10 (fun k h1 h2 => g10 k h1 (by omega))
  let s13 := runN s10 3
  have hs13pc : s13.pc = 552 := ha2.1
  have hs13h := ha2.2.1
  have hQ213 : s13.mem.get 22 = s.mem.get 22 + 48 := by
    have : s10.mem.get 22 = s.mem.get 22 :=
      hpres10 22 (by decide) (by decide) (by decide) (by decide)
    exact ha2.2.2.1.trans (by rw [this])
  have hZ13 := ha2.2.2.2.1
  have hpres13 : ∀ a, a ≠ 22 → a ≠ 21 → a ≠ 20 → a ≠ 24 → a ≠ 0 →
      s13.mem.get a = s.mem.get a := by
    intro a ha22 ha21 ha20 ha24 haZ
    exact (ha2.2.2.2.2 a ha22 haZ).trans (hpres10 a ha21 ha20 ha24 haZ)
  have hK13 : s13.mem.get 8 = 48 :=
    (hpres13 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hQ013 : s13.mem.get 20 = s.mem.get 20 + 48 :=
    (ha2.2.2.2.2 20 (by decide) (by decide)).trans hQ010
  have hQ113 : s13.mem.get 21 = s.mem.get 21 + 48 :=
    (ha2.2.2.2.2 21 (by decide) (by decide)).trans hQ110
  have hQ413 : s13.mem.get 24 = s.mem.get 17 :=
    (ha2.2.2.2.2 24 (by decide) (by decide)).trans hQ410
  have g13 (k : Nat) (h1 : 552 ≤ k) (h2 : k < 570) :
      s13.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres13 (UInt16.ofNat k) (ofNat_ne k 22 (by omega) (by decide) (by omega))
      (ofNat_ne k 21 (by omega) (by decide) (by omega))
      (ofNat_ne k 20 (by omega) (by decide) (by omega))
      (ofNat_ne k 24 (by omega) (by decide) (by omega))
      (ofNat_ne k 0 (by omega) (by decide) (by omega))).trans (hcode k (by omega) h2)
  have ha3 :=
    ascii_add_K48_Q3 (s := s13) hs13pc hs13h hZ13 hK13 (fun k h1 h2 => g13 k h1 (by omega))
  let s16 := runN s13 3
  have hs16pc : s16.pc = 561 := ha3.1
  have hs16h := ha3.2.1
  have hQ316 : s16.mem.get 23 = s.mem.get 23 + 48 := by
    have : s13.mem.get 23 = s.mem.get 23 :=
      hpres13 23 (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ha3.2.2.1.trans (by rw [this])
  have hZ16 := ha3.2.2.2.1
  have hpres16 : ∀ a, a ≠ 23 → a ≠ 22 → a ≠ 21 → a ≠ 20 → a ≠ 24 → a ≠ 0 →
      s16.mem.get a = s.mem.get a := by
    intro a ha23 ha22 ha21 ha20 ha24 haZ
    exact (ha3.2.2.2.2 a ha23 haZ).trans (hpres13 a ha22 ha21 ha20 ha24 haZ)
  have hK16 : s16.mem.get 8 = 48 :=
    (hpres16 8 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hK48
  have hQ016 : s16.mem.get 20 = s.mem.get 20 + 48 :=
    (ha3.2.2.2.2 20 (by decide) (by decide)).trans hQ013
  have hQ116 : s16.mem.get 21 = s.mem.get 21 + 48 :=
    (ha3.2.2.2.2 21 (by decide) (by decide)).trans hQ113
  have hQ216 : s16.mem.get 22 = s.mem.get 22 + 48 :=
    (ha3.2.2.2.2 22 (by decide) (by decide)).trans hQ213
  have hQ416 : s16.mem.get 24 = s.mem.get 17 :=
    (ha3.2.2.2.2 24 (by decide) (by decide)).trans hQ413
  have g16 (k : Nat) (h1 : 561 ≤ k) (h2 : k < 570) :
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres16 (UInt16.ofNat k) (ofNat_ne k 23 (by omega) (by decide) (by omega))
      (ofNat_ne k 22 (by omega) (by decide) (by omega))
      (ofNat_ne k 21 (by omega) (by decide) (by omega))
      (ofNat_ne k 20 (by omega) (by decide) (by omega))
      (ofNat_ne k 24 (by omega) (by decide) (by omega))
      (ofNat_ne k 0 (by omega) (by decide) (by omega))).trans (hcode k (by omega) h2)
  have ha4 :=
    ascii_add_K48_Q4 (s := s16) hs16pc hs16h hZ16 hK16 g16
  have hrun : s19 = runN s16 3 := by
    have h19 : runN s 19 = runN s4 15 := runN_add_eq s 4 15 19 (by decide)
    have h15 : runN s4 15 = runN s7 12 := runN_add_eq s4 3 12 15 (by decide)
    have h12 : runN s7 12 = runN s10 9 := runN_add_eq s7 3 9 12 (by decide)
    have h9 : runN s10 9 = runN s13 6 := runN_add_eq s10 3 6 9 (by decide)
    have h6 : runN s13 6 = runN s16 3 := runN_add_eq s13 3 3 6 (by decide)
    exact h19.trans (h15.trans (h12.trans (h9.trans h6)))
  have hs19pc : s19.pc = 570 := by rw [hrun]; exact ha4.1
  have hs19h : s19.halted = false := by rw [hrun]; exact ha4.2.1
  have hs19Z : s19.mem.get 0 = 0 := by rw [hrun]; exact ha4.2.2.2.1
  have hs19Q4 : s19.mem.get 24 = s.mem.get 17 + 48 := by
    rw [hrun]
    exact ha4.2.2.1.trans (by rw [hQ416])
  have hs19Q0 : s19.mem.get 20 = s.mem.get 20 + 48 := by
    rw [hrun]
    exact (ha4.2.2.2.2 20 (by decide) (by decide)).trans hQ016
  have hs19Q1 : s19.mem.get 21 = s.mem.get 21 + 48 := by
    rw [hrun]
    exact (ha4.2.2.2.2 21 (by decide) (by decide)).trans hQ116
  have hs19Q2 : s19.mem.get 22 = s.mem.get 22 + 48 := by
    rw [hrun]
    exact (ha4.2.2.2.2 22 (by decide) (by decide)).trans hQ216
  have hs19Q3 : s19.mem.get 23 = s.mem.get 23 + 48 := by
    rw [hrun]
    exact (ha4.2.2.2.2 23 (by decide) (by decide)).trans hQ316
  have hs19N : s19.mem.get 17 = s.mem.get 17 := by
    rw [hrun]
    exact (ha4.2.2.2.2 17 (by decide) (by decide)).trans
      (hpres16 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hpres : ∀ a, a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 0 →
      s19.mem.get a = s.mem.get a := by
    intro a ha24 ha20 ha21 ha22 ha23 haZ
    rw [hrun]
    exact (ha4.2.2.2.2 a ha24 haZ).trans
      (hpres16 a ha23 ha22 ha21 ha20 ha24 haZ)
  exact ⟨hs19pc, hs19h, hs19Z, hs19Q4, hs19Q0, hs19Q1, hs19Q2, hs19Q3, hs19N, hpres⟩


end IntFmt
