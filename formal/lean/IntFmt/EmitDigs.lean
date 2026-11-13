/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

`EMIT_DIGS` / `DIG_LOOP` block lemmas on the assembled image.
Not end-to-end correctness.
-/

import IntFmt.PadLoop

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000


private theorem cell1568 (off : Nat) (h : off < 16) :
    intfmtImage[1568 + off]! = decChunk098[off]! :=
  extract_chunk 1568 decChunk098 image_chunk098 off h (by decide)


private theorem cell1584 (off : Nat) (h : off < 16) :
    intfmtImage[1584 + off]! = decChunk099[off]! :=
  extract_chunk 1584 decChunk099 image_chunk099 off h (by decide)


private theorem cell1600 (off : Nat) (h : off < 16) :
    intfmtImage[1600 + off]! = decChunk100[off]! :=
  extract_chunk 1600 decChunk100 image_chunk100 off h (by decide)


private theorem cell1616 (off : Nat) (h : off < 16) :
    intfmtImage[1616 + off]! = decChunk101[off]! :=
  extract_chunk 1616 decChunk101 image_chunk101 off h (by decide)


private theorem cell1632 (off : Nat) (h : off < 16) :
    intfmtImage[1632 + off]! = decChunk102[off]! :=
  extract_chunk 1632 decChunk102 image_chunk102 off h (by decide)


private theorem cell1648 (off : Nat) (h : off < 16) :
    intfmtImage[1648 + off]! = decChunk103[off]! :=
  extract_chunk 1648 decChunk103 image_chunk103 off h (by decide)


private theorem cell1664 (off : Nat) (h : off < 16) :
    intfmtImage[1664 + off]! = decChunk104[off]! :=
  extract_chunk 1664 decChunk104 image_chunk104 off h (by decide)


private theorem cell1680 (off : Nat) (h : off < 16) :
    intfmtImage[1680 + off]! = decChunk105[off]! :=
  extract_chunk 1680 decChunk105 image_chunk105 off h (by decide)


private theorem cell1696 (off : Nat) (h : off < 16) :
    intfmtImage[1696 + off]! = decChunk106[off]! :=
  extract_chunk 1696 decChunk106 image_chunk106 off h (by decide)


private theorem cell1712 (off : Nat) (h : off < 16) :
    intfmtImage[1712 + off]! = decChunk107[off]! :=
  extract_chunk 1712 decChunk107 image_chunk107 off h (by decide)


private theorem cell1728 (off : Nat) (h : off < 16) :
    intfmtImage[1728 + off]! = decChunk108[off]! :=
  extract_chunk 1728 decChunk108 image_chunk108 off h (by decide)


private theorem cell1744 (off : Nat) (h : off < 16) :
    intfmtImage[1744 + off]! = decChunk109[off]! :=
  extract_chunk 1744 decChunk109 image_chunk109 off h (by decide)


private theorem cell1760 (off : Nat) (h : off < 16) :
    intfmtImage[1760 + off]! = decChunk110[off]! :=
  extract_chunk 1760 decChunk110 image_chunk110 off h (by decide)


private theorem cell1776 (off : Nat) (h : off < 16) :
    intfmtImage[1776 + off]! = decChunk111[off]! :=
  extract_chunk 1776 decChunk111 image_chunk111 off h (by decide)


private theorem cell1792 (off : Nat) (h : off < 16) :
    intfmtImage[1792 + off]! = decChunk112[off]! :=
  extract_chunk 1792 decChunk112 image_chunk112 off h (by decide)


private theorem cell1808 (off : Nat) (h : off < 16) :
    intfmtImage[1808 + off]! = decChunk113[off]! :=
  extract_chunk 1808 decChunk113 image_chunk113 off h (by decide)


private theorem cell1824 (off : Nat) (h : off < 16) :
    intfmtImage[1824 + off]! = decChunk114[off]! :=
  extract_chunk 1824 decChunk114 image_chunk114 off h (by decide)


private theorem cell1840 (off : Nat) (h : off < 16) :
    intfmtImage[1840 + off]! = decChunk115[off]! :=
  extract_chunk 1840 decChunk115 image_chunk115 off h (by decide)


private theorem cell1856 (off : Nat) (h : off < 16) :
    intfmtImage[1856 + off]! = decChunk116[off]! :=
  extract_chunk 1856 decChunk116 image_chunk116 off h (by decide)


private theorem cell1872 (off : Nat) (h : off < 16) :
    intfmtImage[1872 + off]! = decChunk117[off]! :=
  extract_chunk 1872 decChunk117 image_chunk117 off h (by decide)


private theorem cell1888 (off : Nat) (h : off < 16) :
    intfmtImage[1888 + off]! = decChunk118[off]! :=
  extract_chunk 1888 decChunk118 image_chunk118 off h (by decide)


private theorem cell1904 (off : Nat) (h : off < 16) :
    intfmtImage[1904 + off]! = decChunk119[off]! :=
  extract_chunk 1904 decChunk119 image_chunk119 off h (by decide)

/-- MOV ONE TMP at EMIT_DIGS (pc 1575). -/
theorem ed_mov_ONE_TMP_1575 {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1575 ≤ k → k < 1587 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1587 ∧
    s4.halted = false ∧
    s4.mem.get 31 = s.mem.get 3 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 3 = s.mem.get 3 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1575 :=
    hpc.trans (rfl : (1575 : Word) = UInt16.ofNat 1575)
  have g (k : Nat) (h1 : 1575 ≤ k) (h2 : k < 1587) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1575 + off) :=
    word_pc_off 1575 off hp (by omega)
  have m0 : s.mem.get s.pc = 31 := by
    rw [hp]
    have hval : decChunk098[7]! = 31 := rfl
    exact (g 1575 (by decide) (by decide)).trans ((cell1568 7 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 31 := by
    rw [poff 1 (by decide)]
    have hval : decChunk098[8]! = 31 := rfl
    exact (g 1576 (by decide) (by decide)).trans ((cell1568 8 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk098[9]! = 1578 := rfl
    have hv : (1578 : Word) = UInt16.ofNat 1578 := rfl
    exact (g 1577 (by decide) (by decide)).trans ((cell1568 9 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 3 := by
    rw [poff 3 (by decide)]
    have hval : decChunk098[10]! = 3 := rfl
    exact (g 1578 (by decide) (by decide)).trans ((cell1568 10 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk098[11]! = 0 := rfl
    exact (g 1579 (by decide) (by decide)).trans ((cell1568 11 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk098[12]! = 1581 := rfl
    have hv : (1581 : Word) = UInt16.ofNat 1581 := rfl
    exact (g 1580 (by decide) (by decide)).trans ((cell1568 12 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk098[13]! = 0 := rfl
    exact (g 1581 (by decide) (by decide)).trans ((cell1568 13 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 31 := by
    rw [poff 7 (by decide)]
    have hval : decChunk098[14]! = 31 := rfl
    exact (g 1582 (by decide) (by decide)).trans ((cell1568 14 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk098[15]! = 1584 := rfl
    have hv : (1584 : Word) = UInt16.ofNat 1584 := rfl
    exact (g 1583 (by decide) (by decide)).trans ((cell1568 15 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk099[0]! = 0 := rfl
    exact (g 1584 (by decide) (by decide)).trans ((cell1584 0 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk099[1]! = 0 := rfl
    exact (g 1585 (by decide) (by decide)).trans ((cell1584 1 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk099[2]! = 1587 := rfl
    have hv : (1587 : Word) = UInt16.ofNat 1587 := rfl
    exact (g 1586 (by decide) (by decide)).trans ((cell1584 2 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 1575 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1575 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1587 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1587 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1587 = (1587 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- ADD ONE TMP at pc 1587 (TMP becomes 2). -/
theorem ed_add_ONE_TMP_1587 {s : Machine}
    (hpc : s.pc = 1587)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1587 ≤ k → k < 1596 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1596 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1587 :=
    hpc.trans (rfl : (1587 : Word) = UInt16.ofNat 1587)
  have g (k : Nat) (h1 : 1587 ≤ k) (h2 : k < 1596) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1587 + off) :=
    word_pc_off 1587 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk099[3]! = 3 := rfl
    exact (g 1587 (by decide) (by decide)).trans ((cell1584 3 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk099[4]! = 0 := rfl
    exact (g 1588 (by decide) (by decide)).trans ((cell1584 4 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk099[5]! = 1590 := rfl
    have hv : (1590 : Word) = UInt16.ofNat 1590 := rfl
    exact (g 1589 (by decide) (by decide)).trans ((cell1584 5 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk099[6]! = 0 := rfl
    exact (g 1590 (by decide) (by decide)).trans ((cell1584 6 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk099[7]! = 31 := rfl
    exact (g 1591 (by decide) (by decide)).trans ((cell1584 7 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk099[8]! = 1593 := rfl
    have hv : (1593 : Word) = UInt16.ofNat 1593 := rfl
    exact (g 1592 (by decide) (by decide)).trans ((cell1584 8 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk099[9]! = 0 := rfl
    exact (g 1593 (by decide) (by decide)).trans ((cell1584 9 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk099[10]! = 0 := rfl
    exact (g 1594 (by decide) (by decide)).trans ((cell1584 10 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk099[11]! = 1596 := rfl
    have hv : (1596 : Word) = UInt16.ofNat 1596 := rfl
    exact (g 1595 (by decide) (by decide)).trans ((cell1584 11 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 1587 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1587 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1596 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1596 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1596 = (1596 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- ADD ONE TMP at pc 1596 (TMP becomes 3). -/
theorem ed_add_ONE_TMP_1596 {s : Machine}
    (hpc : s.pc = 1596)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1596 ≤ k → k < 1605 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1605 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1596 :=
    hpc.trans (rfl : (1596 : Word) = UInt16.ofNat 1596)
  have g (k : Nat) (h1 : 1596 ≤ k) (h2 : k < 1605) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1596 + off) :=
    word_pc_off 1596 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk099[12]! = 3 := rfl
    exact (g 1596 (by decide) (by decide)).trans ((cell1584 12 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk099[13]! = 0 := rfl
    exact (g 1597 (by decide) (by decide)).trans ((cell1584 13 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk099[14]! = 1599 := rfl
    have hv : (1599 : Word) = UInt16.ofNat 1599 := rfl
    exact (g 1598 (by decide) (by decide)).trans ((cell1584 14 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk099[15]! = 0 := rfl
    exact (g 1599 (by decide) (by decide)).trans ((cell1584 15 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk100[0]! = 31 := rfl
    exact (g 1600 (by decide) (by decide)).trans ((cell1600 0 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk100[1]! = 1602 := rfl
    have hv : (1602 : Word) = UInt16.ofNat 1602 := rfl
    exact (g 1601 (by decide) (by decide)).trans ((cell1600 1 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk100[2]! = 0 := rfl
    exact (g 1602 (by decide) (by decide)).trans ((cell1600 2 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk100[3]! = 0 := rfl
    exact (g 1603 (by decide) (by decide)).trans ((cell1600 3 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk100[4]! = 1605 := rfl
    have hv : (1605 : Word) = UInt16.ofNat 1605 := rfl
    exact (g 1604 (by decide) (by decide)).trans ((cell1600 4 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 1596 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1596 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1605 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1605 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1605 = (1605 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- ADD ONE TMP at pc 1605 (TMP becomes 4). -/
theorem ed_add_ONE_TMP_1605 {s : Machine}
    (hpc : s.pc = 1605)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1605 ≤ k → k < 1614 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1614 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1605 :=
    hpc.trans (rfl : (1605 : Word) = UInt16.ofNat 1605)
  have g (k : Nat) (h1 : 1605 ≤ k) (h2 : k < 1614) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1605 + off) :=
    word_pc_off 1605 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk100[5]! = 3 := rfl
    exact (g 1605 (by decide) (by decide)).trans ((cell1600 5 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk100[6]! = 0 := rfl
    exact (g 1606 (by decide) (by decide)).trans ((cell1600 6 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk100[7]! = 1608 := rfl
    have hv : (1608 : Word) = UInt16.ofNat 1608 := rfl
    exact (g 1607 (by decide) (by decide)).trans ((cell1600 7 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk100[8]! = 0 := rfl
    exact (g 1608 (by decide) (by decide)).trans ((cell1600 8 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk100[9]! = 31 := rfl
    exact (g 1609 (by decide) (by decide)).trans ((cell1600 9 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk100[10]! = 1611 := rfl
    have hv : (1611 : Word) = UInt16.ofNat 1611 := rfl
    exact (g 1610 (by decide) (by decide)).trans ((cell1600 10 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk100[11]! = 0 := rfl
    exact (g 1611 (by decide) (by decide)).trans ((cell1600 11 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk100[12]! = 0 := rfl
    exact (g 1612 (by decide) (by decide)).trans ((cell1600 12 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk100[13]! = 1614 := rfl
    have hv : (1614 : Word) = UInt16.ofNat 1614 := rfl
    exact (g 1613 (by decide) (by decide)).trans ((cell1600 13 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 1605 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1605 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1614 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1614 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1614 = (1614 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- ADD ONE TMP at pc 1614 (TMP becomes 5). -/
theorem ed_add_ONE_TMP_1614 {s : Machine}
    (hpc : s.pc = 1614)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1614 ≤ k → k < 1623 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1623 ∧
    s3.halted = false ∧
    s3.mem.get 31 = s.mem.get 31 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 31 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1614 :=
    hpc.trans (rfl : (1614 : Word) = UInt16.ofNat 1614)
  have g (k : Nat) (h1 : 1614 ≤ k) (h2 : k < 1623) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1614 + off) :=
    word_pc_off 1614 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk100[14]! = 3 := rfl
    exact (g 1614 (by decide) (by decide)).trans ((cell1600 14 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk100[15]! = 0 := rfl
    exact (g 1615 (by decide) (by decide)).trans ((cell1600 15 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk101[0]! = 1617 := rfl
    have hv : (1617 : Word) = UInt16.ofNat 1617 := rfl
    exact (g 1616 (by decide) (by decide)).trans ((cell1616 0 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk101[1]! = 0 := rfl
    exact (g 1617 (by decide) (by decide)).trans ((cell1616 1 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 31 := by
    rw [poff 4 (by decide)]
    have hval : decChunk101[2]! = 31 := rfl
    exact (g 1618 (by decide) (by decide)).trans ((cell1616 2 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk101[3]! = 1620 := rfl
    have hv : (1620 : Word) = UInt16.ofNat 1620 := rfl
    exact (g 1619 (by decide) (by decide)).trans ((cell1616 3 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk101[4]! = 0 := rfl
    exact (g 1620 (by decide) (by decide)).trans ((cell1616 4 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk101[5]! = 0 := rfl
    exact (g 1621 (by decide) (by decide)).trans ((cell1616 5 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk101[6]! = 1623 := rfl
    have hv : (1623 : Word) = UInt16.ofNat 1623 := rfl
    exact (g 1622 (by decide) (by decide)).trans ((cell1616 6 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (31 : Word) := by
    intro i hi
    have : (31 : Word) = UInt16.ofNat 31 := rfl
    rw [this]
    exact pc_off_ne 1614 i 31 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1614 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 31)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1623 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1623 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1623 = (1623 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 31 = s.mem.get 31 + 1 := by
    have : s.mem.get 31 + s.mem.get 3 = s.mem.get 31 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- SUB NDIG TMP at pc 1623. -/
theorem ed_sub_NDIG_TMP_1623 {s : Machine}
    (hpc : s.pc = 1623)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1623 ≤ k → k < 1626 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 31 (s.mem.get 31 - s.mem.get 25)
        pc := 1626 } := by
  have hp : s.pc = UInt16.ofNat 1623 :=
    hpc.trans (rfl : (1623 : Word) = UInt16.ofNat 1623)
  have g (k : Nat) (h1 : 1623 ≤ k) (h2 : k < 1626) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 25 := by
    rw [hp]
    have hval : decChunk101[7]! = 25 := rfl
    exact (g 1623 (by decide) (by decide)).trans ((cell1616 7 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 31 := by
    have : s.pc + 1 = (1624 : Word) := by simp [hpc]
    rw [this, (rfl : (1624 : Word) = UInt16.ofNat 1624)]
    have hval : decChunk101[8]! = 31 := rfl
    exact (g 1624 (by decide) (by decide)).trans ((cell1616 8 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1625 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1626 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1625 : Word) = UInt16.ofNat 1625)]
    have hval : decChunk101[9]! = 1626 := rfl
    have hv : (1626 : Word) = UInt16.ofNat 1626 := rfl
    exact (g 1625 (by decide) (by decide)).trans ((cell1616 9 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 25) (b := 31) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1626 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- MOV TMP SK at pc 1626. -/
theorem ed_mov_TMP_SK_1626 {s : Machine}
    (hpc : s.pc = 1626)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1626 ≤ k → k < 1638 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1638 ∧
    s4.halted = false ∧
    s4.mem.get 2320 = s.mem.get 31 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 31 = s.mem.get 31 ∧
    (∀ a, a ≠ 2320 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1626 :=
    hpc.trans (rfl : (1626 : Word) = UInt16.ofNat 1626)
  have g (k : Nat) (h1 : 1626 ≤ k) (h2 : k < 1638) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1626 + off) :=
    word_pc_off 1626 off hp (by omega)
  have m0 : s.mem.get s.pc = 2320 := by
    rw [hp]
    have hval : decChunk101[10]! = 2320 := rfl
    exact (g 1626 (by decide) (by decide)).trans ((cell1616 10 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 2320 := by
    rw [poff 1 (by decide)]
    have hval : decChunk101[11]! = 2320 := rfl
    exact (g 1627 (by decide) (by decide)).trans ((cell1616 11 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk101[12]! = 1629 := rfl
    have hv : (1629 : Word) = UInt16.ofNat 1629 := rfl
    exact (g 1628 (by decide) (by decide)).trans ((cell1616 12 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 31 := by
    rw [poff 3 (by decide)]
    have hval : decChunk101[13]! = 31 := rfl
    exact (g 1629 (by decide) (by decide)).trans ((cell1616 13 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk101[14]! = 0 := rfl
    exact (g 1630 (by decide) (by decide)).trans ((cell1616 14 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk101[15]! = 1632 := rfl
    have hv : (1632 : Word) = UInt16.ofNat 1632 := rfl
    exact (g 1631 (by decide) (by decide)).trans ((cell1616 15 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk102[0]! = 0 := rfl
    exact (g 1632 (by decide) (by decide)).trans ((cell1632 0 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 2320 := by
    rw [poff 7 (by decide)]
    have hval : decChunk102[1]! = 2320 := rfl
    exact (g 1633 (by decide) (by decide)).trans ((cell1632 1 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk102[2]! = 1635 := rfl
    have hv : (1635 : Word) = UInt16.ofNat 1635 := rfl
    exact (g 1634 (by decide) (by decide)).trans ((cell1632 2 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk102[3]! = 0 := rfl
    exact (g 1635 (by decide) (by decide)).trans ((cell1632 3 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk102[4]! = 0 := rfl
    exact (g 1636 (by decide) (by decide)).trans ((cell1632 4 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk102[5]! = 1638 := rfl
    have hv : (1638 : Word) = UInt16.ofNat 1638 := rfl
    exact (g 1637 (by decide) (by decide)).trans ((cell1632 5 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (2320 : Word) := by
    intro i hi
    have : (2320 : Word) = UInt16.ofNat 2320 := rfl
    rw [this]
    exact pc_off_ne 1626 i 2320 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1626 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 31) (dst := 2320)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1638 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1638 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1638 = (1638 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩


/-- ZERO DI at pc 1638. -/
theorem ed_zero_DI_1638 {s : Machine}
    (hpc : s.pc = 1638)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1638 ≤ k → k < 1641 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s = { s with mem := s.mem.set 2321 0, pc := 1641 } := by
  have hp : s.pc = UInt16.ofNat 1638 :=
    hpc.trans (rfl : (1638 : Word) = UInt16.ofNat 1638)
  have g (k : Nat) (h1 : 1638 ≤ k) (h2 : k < 1641) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 2321 := by
    rw [hp]
    have hval : decChunk102[6]! = 2321 := rfl
    exact (g 1638 (by decide) (by decide)).trans ((cell1632 6 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 2321 := by
    have : s.pc + 1 = (1639 : Word) := by simp [hpc]
    rw [this, (rfl : (1639 : Word) = UInt16.ofNat 1639)]
    have hval : decChunk102[7]! = 2321 := rfl
    exact (g 1639 (by decide) (by decide)).trans ((cell1632 7 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1640 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1641 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1640 : Word) = UInt16.ofNat 1640)]
    have hval : decChunk102[8]! = 1641 := rfl
    have hv : (1641 : Word) = UInt16.ofNat 1641 := rfl
    exact (g 1640 (by decide) (by decide)).trans ((cell1632 8 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hz :=
    step_ZERO (s := s) (x := 2321) hh hpc0 ha hb hc (by decide)
  have hpc' : s.pc + 3 = (1641 : Word) := by simp [hpc]
  rw [hz, hpc']

/-- MOV DI T at DIG_LOOP (pc 1641). -/
theorem ed_mov_DI_T_1641 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1641 ≤ k → k < 1653 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1653 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 2321 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 2321 = s.mem.get 2321 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1641 :=
    hpc.trans (rfl : (1641 : Word) = UInt16.ofNat 1641)
  have g (k : Nat) (h1 : 1641 ≤ k) (h2 : k < 1653) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1641 + off) :=
    word_pc_off 1641 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk102[9]! = 18 := rfl
    exact (g 1641 (by decide) (by decide)).trans ((cell1632 9 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk102[10]! = 18 := rfl
    exact (g 1642 (by decide) (by decide)).trans ((cell1632 10 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk102[11]! = 1644 := rfl
    have hv : (1644 : Word) = UInt16.ofNat 1644 := rfl
    exact (g 1643 (by decide) (by decide)).trans ((cell1632 11 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 2321 := by
    rw [poff 3 (by decide)]
    have hval : decChunk102[12]! = 2321 := rfl
    exact (g 1644 (by decide) (by decide)).trans ((cell1632 12 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk102[13]! = 0 := rfl
    exact (g 1645 (by decide) (by decide)).trans ((cell1632 13 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk102[14]! = 1647 := rfl
    have hv : (1647 : Word) = UInt16.ofNat 1647 := rfl
    exact (g 1646 (by decide) (by decide)).trans ((cell1632 14 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk102[15]! = 0 := rfl
    exact (g 1647 (by decide) (by decide)).trans ((cell1632 15 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk103[0]! = 18 := rfl
    exact (g 1648 (by decide) (by decide)).trans ((cell1648 0 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk103[1]! = 1650 := rfl
    have hv : (1650 : Word) = UInt16.ofNat 1650 := rfl
    exact (g 1649 (by decide) (by decide)).trans ((cell1648 1 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk103[2]! = 0 := rfl
    exact (g 1650 (by decide) (by decide)).trans ((cell1648 2 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk103[3]! = 0 := rfl
    exact (g 1651 (by decide) (by decide)).trans ((cell1648 3 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk103[4]! = 1653 := rfl
    have hv : (1653 : Word) = UInt16.ofNat 1653 := rfl
    exact (g 1652 (by decide) (by decide)).trans ((cell1648 4 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1641 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1641 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 2321) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1653 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1653 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1653 = (1653 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- SUB K5 T at pc 1653. -/
theorem ed_sub_K5_T_1653 {s : Machine}
    (hpc : s.pc = 1653)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1653 ≤ k → k < 1656 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 2322)
        pc := 1656 } := by
  have hp : s.pc = UInt16.ofNat 1653 :=
    hpc.trans (rfl : (1653 : Word) = UInt16.ofNat 1653)
  have g (k : Nat) (h1 : 1653 ≤ k) (h2 : k < 1656) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 2322 := by
    rw [hp]
    have hval : decChunk103[5]! = 2322 := rfl
    exact (g 1653 (by decide) (by decide)).trans ((cell1648 5 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1654 : Word) := by simp [hpc]
    rw [this, (rfl : (1654 : Word) = UInt16.ofNat 1654)]
    have hval : decChunk103[6]! = 18 := rfl
    exact (g 1654 (by decide) (by decide)).trans ((cell1648 6 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1655 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1656 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1655 : Word) = UInt16.ofNat 1655)]
    have hval : decChunk103[7]! = 1656 := rfl
    have hv : (1656 : Word) = UInt16.ofNat 1656 := rfl
    exact (g 1655 (by decide) (by decide)).trans ((cell1648 7 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 2322) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1656 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T DIG_EQ5 at pc 1656. -/
theorem ed_enc_jlez_1656 {s : Machine}
    (hpc : s.pc = 1656)
    (hcode : ∀ k : Nat, 1656 ≤ k → k < 1656+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1662 := by
  have hp : s.pc = UInt16.ofNat 1656 :=
    hpc.trans (rfl : (1656 : Word) = UInt16.ofNat 1656)
  have g (k : Nat) (h1 : 1656 ≤ k) (h2 : k < 1656+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk103[8]! = 0 := rfl
    exact (g 1656 (by decide) (by decide)).trans ((cell1648 8 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1657 : Word) := by simp [hpc]
    rw [this, (rfl : (1657 : Word) = UInt16.ofNat 1657)]
    have hval : decChunk103[9]! = 18 := rfl
    exact (g 1657 (by decide) (by decide)).trans ((cell1648 9 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1662 := by
    have : s.pc + 2 = (1658 : Word) := by simp [hpc]
    rw [this, (rfl : (1658 : Word) = UInt16.ofNat 1658)]
    have hval : decChunk103[10]! = 1662 := rfl
    exact (g 1658 (by decide) (by decide)).trans ((cell1648 10 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP DIG_BODY at pc 1659. -/
theorem ed_enc_jmp_1659 {s : Machine}
    (hpc : s.pc = 1659)
    (hcode : ∀ k : Nat, 1659 ≤ k → k < 1659+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1677 := by
  have hp : s.pc = UInt16.ofNat 1659 :=
    hpc.trans (rfl : (1659 : Word) = UInt16.ofNat 1659)
  have g (k : Nat) (h1 : 1659 ≤ k) (h2 : k < 1659+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk103[11]! = 0 := rfl
    exact (g 1659 (by decide) (by decide)).trans ((cell1648 11 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1660 : Word) := by simp [hpc]
    rw [this, (rfl : (1660 : Word) = UInt16.ofNat 1660)]
    have hval : decChunk103[12]! = 0 := rfl
    exact (g 1660 (by decide) (by decide)).trans ((cell1648 12 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1677 := by
    have : s.pc + 2 = (1661 : Word) := by simp [hpc]
    rw [this, (rfl : (1661 : Word) = UInt16.ofNat 1661)]
    have hval : decChunk103[13]! = 1677 := rfl
    exact (g 1661 (by decide) (by decide)).trans ((cell1648 13 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- INC T at DIG_EQ5 (pc 1662). -/
theorem ed_inc_T_1662 {s : Machine}
    (hpc : s.pc = 1662)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1662 ≤ k → k < 1671 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1671 ∧
    s3.halted = false ∧
    s3.mem.get 18 = s.mem.get 18 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1662 :=
    hpc.trans (rfl : (1662 : Word) = UInt16.ofNat 1662)
  have g (k : Nat) (h1 : 1662 ≤ k) (h2 : k < 1671) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1662 + off) :=
    word_pc_off 1662 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk103[14]! = 3 := rfl
    exact (g 1662 (by decide) (by decide)).trans ((cell1648 14 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk103[15]! = 0 := rfl
    exact (g 1663 (by decide) (by decide)).trans ((cell1648 15 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk104[0]! = 1665 := rfl
    have hv : (1665 : Word) = UInt16.ofNat 1665 := rfl
    exact (g 1664 (by decide) (by decide)).trans ((cell1664 0 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk104[1]! = 0 := rfl
    exact (g 1665 (by decide) (by decide)).trans ((cell1664 1 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 18 := by
    rw [poff 4 (by decide)]
    have hval : decChunk104[2]! = 18 := rfl
    exact (g 1666 (by decide) (by decide)).trans ((cell1664 2 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk104[3]! = 1668 := rfl
    have hv : (1668 : Word) = UInt16.ofNat 1668 := rfl
    exact (g 1667 (by decide) (by decide)).trans ((cell1664 3 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk104[4]! = 0 := rfl
    exact (g 1668 (by decide) (by decide)).trans ((cell1664 4 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk104[5]! = 0 := rfl
    exact (g 1669 (by decide) (by decide)).trans ((cell1664 5 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk104[6]! = 1671 := rfl
    have hv : (1671 : Word) = UInt16.ofNat 1671 := rfl
    exact (g 1670 (by decide) (by decide)).trans ((cell1664 6 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1662 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1662 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1671 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1671 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1671 = (1671 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 18 = s.mem.get 18 + 1 := by
    have : s.mem.get 18 + s.mem.get 3 = s.mem.get 18 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- JLEZ T DIG_BODY at pc 1671. -/
theorem ed_enc_jlez_1671 {s : Machine}
    (hpc : s.pc = 1671)
    (hcode : ∀ k : Nat, 1671 ≤ k → k < 1671+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1677 := by
  have hp : s.pc = UInt16.ofNat 1671 :=
    hpc.trans (rfl : (1671 : Word) = UInt16.ofNat 1671)
  have g (k : Nat) (h1 : 1671 ≤ k) (h2 : k < 1671+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk104[7]! = 0 := rfl
    exact (g 1671 (by decide) (by decide)).trans ((cell1664 7 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1672 : Word) := by simp [hpc]
    rw [this, (rfl : (1672 : Word) = UInt16.ofNat 1672)]
    have hval : decChunk104[8]! = 18 := rfl
    exact (g 1672 (by decide) (by decide)).trans ((cell1664 8 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1677 := by
    have : s.pc + 2 = (1673 : Word) := by simp [hpc]
    rw [this, (rfl : (1673 : Word) = UInt16.ofNat 1673)]
    have hval : decChunk104[9]! = 1677 := rfl
    exact (g 1673 (by decide) (by decide)).trans ((cell1664 9 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP AFTER_DIGS at pc 1674. -/
theorem ed_enc_jmp_1674 {s : Machine}
    (hpc : s.pc = 1674)
    (hcode : ∀ k : Nat, 1674 ≤ k → k < 1674+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1905 := by
  have hp : s.pc = UInt16.ofNat 1674 :=
    hpc.trans (rfl : (1674 : Word) = UInt16.ofNat 1674)
  have g (k : Nat) (h1 : 1674 ≤ k) (h2 : k < 1674+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk104[10]! = 0 := rfl
    exact (g 1674 (by decide) (by decide)).trans ((cell1664 10 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1675 : Word) := by simp [hpc]
    rw [this, (rfl : (1675 : Word) = UInt16.ofNat 1675)]
    have hval : decChunk104[11]! = 0 := rfl
    exact (g 1675 (by decide) (by decide)).trans ((cell1664 11 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1905 := by
    have : s.pc + 2 = (1676 : Word) := by simp [hpc]
    rw [this, (rfl : (1676 : Word) = UInt16.ofNat 1676)]
    have hval : decChunk104[12]! = 1905 := rfl
    exact (g 1676 (by decide) (by decide)).trans ((cell1664 12 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV DI T at DIG_BODY (pc 1677). -/
theorem ed_mov_DI_T_1677 {s : Machine}
    (hpc : s.pc = 1677)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1677 ≤ k → k < 1689 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1689 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 2321 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 2321 = s.mem.get 2321 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1677 :=
    hpc.trans (rfl : (1677 : Word) = UInt16.ofNat 1677)
  have g (k : Nat) (h1 : 1677 ≤ k) (h2 : k < 1689) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1677 + off) :=
    word_pc_off 1677 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk104[13]! = 18 := rfl
    exact (g 1677 (by decide) (by decide)).trans ((cell1664 13 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk104[14]! = 18 := rfl
    exact (g 1678 (by decide) (by decide)).trans ((cell1664 14 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk104[15]! = 1680 := rfl
    have hv : (1680 : Word) = UInt16.ofNat 1680 := rfl
    exact (g 1679 (by decide) (by decide)).trans ((cell1664 15 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 2321 := by
    rw [poff 3 (by decide)]
    have hval : decChunk105[0]! = 2321 := rfl
    exact (g 1680 (by decide) (by decide)).trans ((cell1680 0 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk105[1]! = 0 := rfl
    exact (g 1681 (by decide) (by decide)).trans ((cell1680 1 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk105[2]! = 1683 := rfl
    have hv : (1683 : Word) = UInt16.ofNat 1683 := rfl
    exact (g 1682 (by decide) (by decide)).trans ((cell1680 2 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk105[3]! = 0 := rfl
    exact (g 1683 (by decide) (by decide)).trans ((cell1680 3 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk105[4]! = 18 := rfl
    exact (g 1684 (by decide) (by decide)).trans ((cell1680 4 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk105[5]! = 1686 := rfl
    have hv : (1686 : Word) = UInt16.ofNat 1686 := rfl
    exact (g 1685 (by decide) (by decide)).trans ((cell1680 5 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk105[6]! = 0 := rfl
    exact (g 1686 (by decide) (by decide)).trans ((cell1680 6 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk105[7]! = 0 := rfl
    exact (g 1687 (by decide) (by decide)).trans ((cell1680 7 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk105[8]! = 1689 := rfl
    have hv : (1689 : Word) = UInt16.ofNat 1689 := rfl
    exact (g 1688 (by decide) (by decide)).trans ((cell1680 8 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1677 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1677 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 2321) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1689 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1689 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1689 = (1689 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- SUB SK T at pc 1689. -/
theorem ed_sub_SK_T_1689 {s : Machine}
    (hpc : s.pc = 1689)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1689 ≤ k → k < 1692 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 2320)
        pc := 1692 } := by
  have hp : s.pc = UInt16.ofNat 1689 :=
    hpc.trans (rfl : (1689 : Word) = UInt16.ofNat 1689)
  have g (k : Nat) (h1 : 1689 ≤ k) (h2 : k < 1692) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 2320 := by
    rw [hp]
    have hval : decChunk105[9]! = 2320 := rfl
    exact (g 1689 (by decide) (by decide)).trans ((cell1680 9 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1690 : Word) := by simp [hpc]
    rw [this, (rfl : (1690 : Word) = UInt16.ofNat 1690)]
    have hval : decChunk105[10]! = 18 := rfl
    exact (g 1690 (by decide) (by decide)).trans ((cell1680 10 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1691 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1692 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1691 : Word) = UInt16.ofNat 1691)]
    have hval : decChunk105[11]! = 1692 := rfl
    have hv : (1692 : Word) = UInt16.ofNat 1692 := rfl
    exact (g 1691 (by decide) (by decide)).trans ((cell1680 11 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 2320) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1692 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T MAYBE_SKIP at pc 1692. -/
theorem ed_enc_jlez_1692 {s : Machine}
    (hpc : s.pc = 1692)
    (hcode : ∀ k : Nat, 1692 ≤ k → k < 1692+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1698 := by
  have hp : s.pc = UInt16.ofNat 1692 :=
    hpc.trans (rfl : (1692 : Word) = UInt16.ofNat 1692)
  have g (k : Nat) (h1 : 1692 ≤ k) (h2 : k < 1692+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk105[12]! = 0 := rfl
    exact (g 1692 (by decide) (by decide)).trans ((cell1680 12 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1693 : Word) := by simp [hpc]
    rw [this, (rfl : (1693 : Word) = UInt16.ofNat 1693)]
    have hval : decChunk105[13]! = 18 := rfl
    exact (g 1693 (by decide) (by decide)).trans ((cell1680 13 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1698 := by
    have : s.pc + 2 = (1694 : Word) := by simp [hpc]
    rw [this, (rfl : (1694 : Word) = UInt16.ofNat 1694)]
    have hval : decChunk105[14]! = 1698 := rfl
    exact (g 1694 (by decide) (by decide)).trans ((cell1680 14 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP TAKE_DIG at pc 1695. -/
theorem ed_enc_jmp_1695 {s : Machine}
    (hpc : s.pc = 1695)
    (hcode : ∀ k : Nat, 1695 ≤ k → k < 1695+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1716 := by
  have hp : s.pc = UInt16.ofNat 1695 :=
    hpc.trans (rfl : (1695 : Word) = UInt16.ofNat 1695)
  have g (k : Nat) (h1 : 1695 ≤ k) (h2 : k < 1695+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk105[15]! = 0 := rfl
    exact (g 1695 (by decide) (by decide)).trans ((cell1680 15 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1696 : Word) := by simp [hpc]
    rw [this, (rfl : (1696 : Word) = UInt16.ofNat 1696)]
    have hval : decChunk106[0]! = 0 := rfl
    exact (g 1696 (by decide) (by decide)).trans ((cell1696 0 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1716 := by
    have : s.pc + 2 = (1697 : Word) := by simp [hpc]
    rw [this, (rfl : (1697 : Word) = UInt16.ofNat 1697)]
    have hval : decChunk106[1]! = 1716 := rfl
    exact (g 1697 (by decide) (by decide)).trans ((cell1696 1 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- INC T at MAYBE_SKIP (pc 1698). -/
theorem ed_inc_T_1698 {s : Machine}
    (hpc : s.pc = 1698)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1698 ≤ k → k < 1707 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1707 ∧
    s3.halted = false ∧
    s3.mem.get 18 = s.mem.get 18 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1698 :=
    hpc.trans (rfl : (1698 : Word) = UInt16.ofNat 1698)
  have g (k : Nat) (h1 : 1698 ≤ k) (h2 : k < 1707) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1698 + off) :=
    word_pc_off 1698 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk106[2]! = 3 := rfl
    exact (g 1698 (by decide) (by decide)).trans ((cell1696 2 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk106[3]! = 0 := rfl
    exact (g 1699 (by decide) (by decide)).trans ((cell1696 3 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk106[4]! = 1701 := rfl
    have hv : (1701 : Word) = UInt16.ofNat 1701 := rfl
    exact (g 1700 (by decide) (by decide)).trans ((cell1696 4 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk106[5]! = 0 := rfl
    exact (g 1701 (by decide) (by decide)).trans ((cell1696 5 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 18 := by
    rw [poff 4 (by decide)]
    have hval : decChunk106[6]! = 18 := rfl
    exact (g 1702 (by decide) (by decide)).trans ((cell1696 6 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk106[7]! = 1704 := rfl
    have hv : (1704 : Word) = UInt16.ofNat 1704 := rfl
    exact (g 1703 (by decide) (by decide)).trans ((cell1696 7 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk106[8]! = 0 := rfl
    exact (g 1704 (by decide) (by decide)).trans ((cell1696 8 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk106[9]! = 0 := rfl
    exact (g 1705 (by decide) (by decide)).trans ((cell1696 9 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk106[10]! = 1707 := rfl
    have hv : (1707 : Word) = UInt16.ofNat 1707 := rfl
    exact (g 1706 (by decide) (by decide)).trans ((cell1696 10 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1698 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1698 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1707 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1707 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1707 = (1707 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 18 = s.mem.get 18 + 1 := by
    have : s.mem.get 18 + s.mem.get 3 = s.mem.get 18 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- JLEZ T SKIP_DIG at pc 1707. -/
theorem ed_enc_jlez_1707 {s : Machine}
    (hpc : s.pc = 1707)
    (hcode : ∀ k : Nat, 1707 ≤ k → k < 1707+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1713 := by
  have hp : s.pc = UInt16.ofNat 1707 :=
    hpc.trans (rfl : (1707 : Word) = UInt16.ofNat 1707)
  have g (k : Nat) (h1 : 1707 ≤ k) (h2 : k < 1707+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk106[11]! = 0 := rfl
    exact (g 1707 (by decide) (by decide)).trans ((cell1696 11 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1708 : Word) := by simp [hpc]
    rw [this, (rfl : (1708 : Word) = UInt16.ofNat 1708)]
    have hval : decChunk106[12]! = 18 := rfl
    exact (g 1708 (by decide) (by decide)).trans ((cell1696 12 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1713 := by
    have : s.pc + 2 = (1709 : Word) := by simp [hpc]
    rw [this, (rfl : (1709 : Word) = UInt16.ofNat 1709)]
    have hval : decChunk106[13]! = 1713 := rfl
    exact (g 1709 (by decide) (by decide)).trans ((cell1696 13 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP TAKE_DIG at pc 1710. -/
theorem ed_enc_jmp_1710 {s : Machine}
    (hpc : s.pc = 1710)
    (hcode : ∀ k : Nat, 1710 ≤ k → k < 1710+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1716 := by
  have hp : s.pc = UInt16.ofNat 1710 :=
    hpc.trans (rfl : (1710 : Word) = UInt16.ofNat 1710)
  have g (k : Nat) (h1 : 1710 ≤ k) (h2 : k < 1710+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk106[14]! = 0 := rfl
    exact (g 1710 (by decide) (by decide)).trans ((cell1696 14 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1711 : Word) := by simp [hpc]
    rw [this, (rfl : (1711 : Word) = UInt16.ofNat 1711)]
    have hval : decChunk106[15]! = 0 := rfl
    exact (g 1711 (by decide) (by decide)).trans ((cell1696 15 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1716 := by
    have : s.pc + 2 = (1712 : Word) := by simp [hpc]
    rw [this, (rfl : (1712 : Word) = UInt16.ofNat 1712)]
    have hval : decChunk107[0]! = 1716 := rfl
    exact (g 1712 (by decide) (by decide)).trans ((cell1712 0 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP DIG_NEXT at SKIP_DIG (pc 1713). -/
theorem ed_enc_jmp_1713 {s : Machine}
    (hpc : s.pc = 1713)
    (hcode : ∀ k : Nat, 1713 ≤ k → k < 1713+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1893 := by
  have hp : s.pc = UInt16.ofNat 1713 :=
    hpc.trans (rfl : (1713 : Word) = UInt16.ofNat 1713)
  have g (k : Nat) (h1 : 1713 ≤ k) (h2 : k < 1713+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk107[1]! = 0 := rfl
    exact (g 1713 (by decide) (by decide)).trans ((cell1712 1 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1714 : Word) := by simp [hpc]
    rw [this, (rfl : (1714 : Word) = UInt16.ofNat 1714)]
    have hval : decChunk107[2]! = 0 := rfl
    exact (g 1714 (by decide) (by decide)).trans ((cell1712 2 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1893 := by
    have : s.pc + 2 = (1715 : Word) := by simp [hpc]
    rw [this, (rfl : (1715 : Word) = UInt16.ofNat 1715)]
    have hval : decChunk107[3]! = 1893 := rfl
    exact (g 1715 (by decide) (by decide)).trans ((cell1712 3 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV DI T at TAKE_DIG (pc 1716). -/
theorem ed_mov_DI_T_1716 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1716 ≤ k → k < 1728 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1728 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 2321 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 2321 = s.mem.get 2321 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1716 :=
    hpc.trans (rfl : (1716 : Word) = UInt16.ofNat 1716)
  have g (k : Nat) (h1 : 1716 ≤ k) (h2 : k < 1728) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1716 + off) :=
    word_pc_off 1716 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk107[4]! = 18 := rfl
    exact (g 1716 (by decide) (by decide)).trans ((cell1712 4 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk107[5]! = 18 := rfl
    exact (g 1717 (by decide) (by decide)).trans ((cell1712 5 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk107[6]! = 1719 := rfl
    have hv : (1719 : Word) = UInt16.ofNat 1719 := rfl
    exact (g 1718 (by decide) (by decide)).trans ((cell1712 6 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 2321 := by
    rw [poff 3 (by decide)]
    have hval : decChunk107[7]! = 2321 := rfl
    exact (g 1719 (by decide) (by decide)).trans ((cell1712 7 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk107[8]! = 0 := rfl
    exact (g 1720 (by decide) (by decide)).trans ((cell1712 8 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk107[9]! = 1722 := rfl
    have hv : (1722 : Word) = UInt16.ofNat 1722 := rfl
    exact (g 1721 (by decide) (by decide)).trans ((cell1712 9 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk107[10]! = 0 := rfl
    exact (g 1722 (by decide) (by decide)).trans ((cell1712 10 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk107[11]! = 18 := rfl
    exact (g 1723 (by decide) (by decide)).trans ((cell1712 11 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk107[12]! = 1725 := rfl
    have hv : (1725 : Word) = UInt16.ofNat 1725 := rfl
    exact (g 1724 (by decide) (by decide)).trans ((cell1712 12 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk107[13]! = 0 := rfl
    exact (g 1725 (by decide) (by decide)).trans ((cell1712 13 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk107[14]! = 0 := rfl
    exact (g 1726 (by decide) (by decide)).trans ((cell1712 14 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk107[15]! = 1728 := rfl
    have hv : (1728 : Word) = UInt16.ofNat 1728 := rfl
    exact (g 1727 (by decide) (by decide)).trans ((cell1712 15 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1716 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1716 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 2321) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1728 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1728 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1728 = (1728 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JLEZ T TQ0 at pc 1728. -/
theorem ed_enc_jlez_1728 {s : Machine}
    (hpc : s.pc = 1728)
    (hcode : ∀ k : Nat, 1728 ≤ k → k < 1728+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1752 := by
  have hp : s.pc = UInt16.ofNat 1728 :=
    hpc.trans (rfl : (1728 : Word) = UInt16.ofNat 1728)
  have g (k : Nat) (h1 : 1728 ≤ k) (h2 : k < 1728+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk108[0]! = 0 := rfl
    exact (g 1728 (by decide) (by decide)).trans ((cell1728 0 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1729 : Word) := by simp [hpc]
    rw [this, (rfl : (1729 : Word) = UInt16.ofNat 1729)]
    have hval : decChunk108[1]! = 18 := rfl
    exact (g 1729 (by decide) (by decide)).trans ((cell1728 1 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1752 := by
    have : s.pc + 2 = (1730 : Word) := by simp [hpc]
    rw [this, (rfl : (1730 : Word) = UInt16.ofNat 1730)]
    have hval : decChunk108[2]! = 1752 := rfl
    exact (g 1730 (by decide) (by decide)).trans ((cell1728 2 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1731. -/
theorem ed_dec_T_1731 {s : Machine}
    (hpc : s.pc = 1731)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1731 ≤ k → k < 1734 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1734 } := by
  have hp : s.pc = UInt16.ofNat 1731 :=
    hpc.trans (rfl : (1731 : Word) = UInt16.ofNat 1731)
  have g (k : Nat) (h1 : 1731 ≤ k) (h2 : k < 1734) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk108[3]! = 3 := rfl
    exact (g 1731 (by decide) (by decide)).trans ((cell1728 3 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1732 : Word) := by simp [hpc]
    rw [this, (rfl : (1732 : Word) = UInt16.ofNat 1732)]
    have hval : decChunk108[4]! = 18 := rfl
    exact (g 1732 (by decide) (by decide)).trans ((cell1728 4 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1733 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1734 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1733 : Word) = UInt16.ofNat 1733)]
    have hval : decChunk108[5]! = 1734 := rfl
    have hv : (1734 : Word) = UInt16.ofNat 1734 := rfl
    exact (g 1733 (by decide) (by decide)).trans ((cell1728 5 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1734 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T TQ1 at pc 1734. -/
theorem ed_enc_jlez_1734 {s : Machine}
    (hpc : s.pc = 1734)
    (hcode : ∀ k : Nat, 1734 ≤ k → k < 1734+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1767 := by
  have hp : s.pc = UInt16.ofNat 1734 :=
    hpc.trans (rfl : (1734 : Word) = UInt16.ofNat 1734)
  have g (k : Nat) (h1 : 1734 ≤ k) (h2 : k < 1734+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk108[6]! = 0 := rfl
    exact (g 1734 (by decide) (by decide)).trans ((cell1728 6 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1735 : Word) := by simp [hpc]
    rw [this, (rfl : (1735 : Word) = UInt16.ofNat 1735)]
    have hval : decChunk108[7]! = 18 := rfl
    exact (g 1735 (by decide) (by decide)).trans ((cell1728 7 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1767 := by
    have : s.pc + 2 = (1736 : Word) := by simp [hpc]
    rw [this, (rfl : (1736 : Word) = UInt16.ofNat 1736)]
    have hval : decChunk108[8]! = 1767 := rfl
    exact (g 1736 (by decide) (by decide)).trans ((cell1728 8 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1737. -/
theorem ed_dec_T_1737 {s : Machine}
    (hpc : s.pc = 1737)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1737 ≤ k → k < 1740 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1740 } := by
  have hp : s.pc = UInt16.ofNat 1737 :=
    hpc.trans (rfl : (1737 : Word) = UInt16.ofNat 1737)
  have g (k : Nat) (h1 : 1737 ≤ k) (h2 : k < 1740) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk108[9]! = 3 := rfl
    exact (g 1737 (by decide) (by decide)).trans ((cell1728 9 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1738 : Word) := by simp [hpc]
    rw [this, (rfl : (1738 : Word) = UInt16.ofNat 1738)]
    have hval : decChunk108[10]! = 18 := rfl
    exact (g 1738 (by decide) (by decide)).trans ((cell1728 10 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1739 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1740 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1739 : Word) = UInt16.ofNat 1739)]
    have hval : decChunk108[11]! = 1740 := rfl
    have hv : (1740 : Word) = UInt16.ofNat 1740 := rfl
    exact (g 1739 (by decide) (by decide)).trans ((cell1728 11 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1740 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T TQ2 at pc 1740. -/
theorem ed_enc_jlez_1740 {s : Machine}
    (hpc : s.pc = 1740)
    (hcode : ∀ k : Nat, 1740 ≤ k → k < 1740+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1782 := by
  have hp : s.pc = UInt16.ofNat 1740 :=
    hpc.trans (rfl : (1740 : Word) = UInt16.ofNat 1740)
  have g (k : Nat) (h1 : 1740 ≤ k) (h2 : k < 1740+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk108[12]! = 0 := rfl
    exact (g 1740 (by decide) (by decide)).trans ((cell1728 12 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1741 : Word) := by simp [hpc]
    rw [this, (rfl : (1741 : Word) = UInt16.ofNat 1741)]
    have hval : decChunk108[13]! = 18 := rfl
    exact (g 1741 (by decide) (by decide)).trans ((cell1728 13 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1782 := by
    have : s.pc + 2 = (1742 : Word) := by simp [hpc]
    rw [this, (rfl : (1742 : Word) = UInt16.ofNat 1742)]
    have hval : decChunk108[14]! = 1782 := rfl
    exact (g 1742 (by decide) (by decide)).trans ((cell1728 14 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1743. -/
theorem ed_dec_T_1743 {s : Machine}
    (hpc : s.pc = 1743)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1743 ≤ k → k < 1746 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1746 } := by
  have hp : s.pc = UInt16.ofNat 1743 :=
    hpc.trans (rfl : (1743 : Word) = UInt16.ofNat 1743)
  have g (k : Nat) (h1 : 1743 ≤ k) (h2 : k < 1746) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk108[15]! = 3 := rfl
    exact (g 1743 (by decide) (by decide)).trans ((cell1728 15 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1744 : Word) := by simp [hpc]
    rw [this, (rfl : (1744 : Word) = UInt16.ofNat 1744)]
    have hval : decChunk109[0]! = 18 := rfl
    exact (g 1744 (by decide) (by decide)).trans ((cell1744 0 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1745 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1746 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1745 : Word) = UInt16.ofNat 1745)]
    have hval : decChunk109[1]! = 1746 := rfl
    have hv : (1746 : Word) = UInt16.ofNat 1746 := rfl
    exact (g 1745 (by decide) (by decide)).trans ((cell1744 1 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1746 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T TQ3 at pc 1746. -/
theorem ed_enc_jlez_1746 {s : Machine}
    (hpc : s.pc = 1746)
    (hcode : ∀ k : Nat, 1746 ≤ k → k < 1746+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1797 := by
  have hp : s.pc = UInt16.ofNat 1746 :=
    hpc.trans (rfl : (1746 : Word) = UInt16.ofNat 1746)
  have g (k : Nat) (h1 : 1746 ≤ k) (h2 : k < 1746+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk109[2]! = 0 := rfl
    exact (g 1746 (by decide) (by decide)).trans ((cell1744 2 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1747 : Word) := by simp [hpc]
    rw [this, (rfl : (1747 : Word) = UInt16.ofNat 1747)]
    have hval : decChunk109[3]! = 18 := rfl
    exact (g 1747 (by decide) (by decide)).trans ((cell1744 3 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1797 := by
    have : s.pc + 2 = (1748 : Word) := by simp [hpc]
    rw [this, (rfl : (1748 : Word) = UInt16.ofNat 1748)]
    have hval : decChunk109[4]! = 1797 := rfl
    exact (g 1748 (by decide) (by decide)).trans ((cell1744 4 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP TQ4 at pc 1749. -/
theorem ed_enc_jmp_1749 {s : Machine}
    (hpc : s.pc = 1749)
    (hcode : ∀ k : Nat, 1749 ≤ k → k < 1749+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1812 := by
  have hp : s.pc = UInt16.ofNat 1749 :=
    hpc.trans (rfl : (1749 : Word) = UInt16.ofNat 1749)
  have g (k : Nat) (h1 : 1749 ≤ k) (h2 : k < 1749+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk109[5]! = 0 := rfl
    exact (g 1749 (by decide) (by decide)).trans ((cell1744 5 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1750 : Word) := by simp [hpc]
    rw [this, (rfl : (1750 : Word) = UInt16.ofNat 1750)]
    have hval : decChunk109[6]! = 0 := rfl
    exact (g 1750 (by decide) (by decide)).trans ((cell1744 6 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1812 := by
    have : s.pc + 2 = (1751 : Word) := by simp [hpc]
    rw [this, (rfl : (1751 : Word) = UInt16.ofNat 1751)]
    have hval : decChunk109[7]! = 1812 := rfl
    exact (g 1751 (by decide) (by decide)).trans ((cell1744 7 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV Q0 CH at TQ0 (pc 1752). -/
theorem ed_mov_Q0_CH_1752 {s : Machine}
    (hpc : s.pc = 1752)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1752 ≤ k → k < 1764 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1764 ∧
    s4.halted = false ∧
    s4.mem.get 30 = s.mem.get 20 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 20 = s.mem.get 20 ∧
    (∀ a, a ≠ 30 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1752 :=
    hpc.trans (rfl : (1752 : Word) = UInt16.ofNat 1752)
  have g (k : Nat) (h1 : 1752 ≤ k) (h2 : k < 1764) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1752 + off) :=
    word_pc_off 1752 off hp (by omega)
  have m0 : s.mem.get s.pc = 30 := by
    rw [hp]
    have hval : decChunk109[8]! = 30 := rfl
    exact (g 1752 (by decide) (by decide)).trans ((cell1744 8 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 30 := by
    rw [poff 1 (by decide)]
    have hval : decChunk109[9]! = 30 := rfl
    exact (g 1753 (by decide) (by decide)).trans ((cell1744 9 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk109[10]! = 1755 := rfl
    have hv : (1755 : Word) = UInt16.ofNat 1755 := rfl
    exact (g 1754 (by decide) (by decide)).trans ((cell1744 10 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 20 := by
    rw [poff 3 (by decide)]
    have hval : decChunk109[11]! = 20 := rfl
    exact (g 1755 (by decide) (by decide)).trans ((cell1744 11 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk109[12]! = 0 := rfl
    exact (g 1756 (by decide) (by decide)).trans ((cell1744 12 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk109[13]! = 1758 := rfl
    have hv : (1758 : Word) = UInt16.ofNat 1758 := rfl
    exact (g 1757 (by decide) (by decide)).trans ((cell1744 13 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk109[14]! = 0 := rfl
    exact (g 1758 (by decide) (by decide)).trans ((cell1744 14 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 30 := by
    rw [poff 7 (by decide)]
    have hval : decChunk109[15]! = 30 := rfl
    exact (g 1759 (by decide) (by decide)).trans ((cell1744 15 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk110[0]! = 1761 := rfl
    have hv : (1761 : Word) = UInt16.ofNat 1761 := rfl
    exact (g 1760 (by decide) (by decide)).trans ((cell1760 0 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk110[1]! = 0 := rfl
    exact (g 1761 (by decide) (by decide)).trans ((cell1760 1 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk110[2]! = 0 := rfl
    exact (g 1762 (by decide) (by decide)).trans ((cell1760 2 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk110[3]! = 1764 := rfl
    have hv : (1764 : Word) = UInt16.ofNat 1764 := rfl
    exact (g 1763 (by decide) (by decide)).trans ((cell1760 3 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (30 : Word) := by
    intro i hi
    have : (30 : Word) = UInt16.ofNat 30 := rfl
    rw [this]
    exact pc_off_ne 1752 i 30 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1752 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 20) (dst := 30)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1764 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1764 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1764 = (1764 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP HAVE_CH at pc 1764. -/
theorem ed_enc_jmp_1764 {s : Machine}
    (hpc : s.pc = 1764)
    (hcode : ∀ k : Nat, 1764 ≤ k → k < 1764+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1824 := by
  have hp : s.pc = UInt16.ofNat 1764 :=
    hpc.trans (rfl : (1764 : Word) = UInt16.ofNat 1764)
  have g (k : Nat) (h1 : 1764 ≤ k) (h2 : k < 1764+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk110[4]! = 0 := rfl
    exact (g 1764 (by decide) (by decide)).trans ((cell1760 4 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1765 : Word) := by simp [hpc]
    rw [this, (rfl : (1765 : Word) = UInt16.ofNat 1765)]
    have hval : decChunk110[5]! = 0 := rfl
    exact (g 1765 (by decide) (by decide)).trans ((cell1760 5 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1824 := by
    have : s.pc + 2 = (1766 : Word) := by simp [hpc]
    rw [this, (rfl : (1766 : Word) = UInt16.ofNat 1766)]
    have hval : decChunk110[6]! = 1824 := rfl
    exact (g 1766 (by decide) (by decide)).trans ((cell1760 6 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV Q1 CH at TQ1 (pc 1767). -/
theorem ed_mov_Q1_CH_1767 {s : Machine}
    (hpc : s.pc = 1767)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1767 ≤ k → k < 1779 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1779 ∧
    s4.halted = false ∧
    s4.mem.get 30 = s.mem.get 21 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 21 = s.mem.get 21 ∧
    (∀ a, a ≠ 30 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1767 :=
    hpc.trans (rfl : (1767 : Word) = UInt16.ofNat 1767)
  have g (k : Nat) (h1 : 1767 ≤ k) (h2 : k < 1779) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1767 + off) :=
    word_pc_off 1767 off hp (by omega)
  have m0 : s.mem.get s.pc = 30 := by
    rw [hp]
    have hval : decChunk110[7]! = 30 := rfl
    exact (g 1767 (by decide) (by decide)).trans ((cell1760 7 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 30 := by
    rw [poff 1 (by decide)]
    have hval : decChunk110[8]! = 30 := rfl
    exact (g 1768 (by decide) (by decide)).trans ((cell1760 8 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk110[9]! = 1770 := rfl
    have hv : (1770 : Word) = UInt16.ofNat 1770 := rfl
    exact (g 1769 (by decide) (by decide)).trans ((cell1760 9 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 21 := by
    rw [poff 3 (by decide)]
    have hval : decChunk110[10]! = 21 := rfl
    exact (g 1770 (by decide) (by decide)).trans ((cell1760 10 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk110[11]! = 0 := rfl
    exact (g 1771 (by decide) (by decide)).trans ((cell1760 11 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk110[12]! = 1773 := rfl
    have hv : (1773 : Word) = UInt16.ofNat 1773 := rfl
    exact (g 1772 (by decide) (by decide)).trans ((cell1760 12 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk110[13]! = 0 := rfl
    exact (g 1773 (by decide) (by decide)).trans ((cell1760 13 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 30 := by
    rw [poff 7 (by decide)]
    have hval : decChunk110[14]! = 30 := rfl
    exact (g 1774 (by decide) (by decide)).trans ((cell1760 14 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk110[15]! = 1776 := rfl
    have hv : (1776 : Word) = UInt16.ofNat 1776 := rfl
    exact (g 1775 (by decide) (by decide)).trans ((cell1760 15 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk111[0]! = 0 := rfl
    exact (g 1776 (by decide) (by decide)).trans ((cell1776 0 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk111[1]! = 0 := rfl
    exact (g 1777 (by decide) (by decide)).trans ((cell1776 1 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk111[2]! = 1779 := rfl
    have hv : (1779 : Word) = UInt16.ofNat 1779 := rfl
    exact (g 1778 (by decide) (by decide)).trans ((cell1776 2 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (30 : Word) := by
    intro i hi
    have : (30 : Word) = UInt16.ofNat 30 := rfl
    rw [this]
    exact pc_off_ne 1767 i 30 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1767 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 21) (dst := 30)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1779 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1779 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1779 = (1779 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP HAVE_CH at pc 1779. -/
theorem ed_enc_jmp_1779 {s : Machine}
    (hpc : s.pc = 1779)
    (hcode : ∀ k : Nat, 1779 ≤ k → k < 1779+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1824 := by
  have hp : s.pc = UInt16.ofNat 1779 :=
    hpc.trans (rfl : (1779 : Word) = UInt16.ofNat 1779)
  have g (k : Nat) (h1 : 1779 ≤ k) (h2 : k < 1779+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk111[3]! = 0 := rfl
    exact (g 1779 (by decide) (by decide)).trans ((cell1776 3 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1780 : Word) := by simp [hpc]
    rw [this, (rfl : (1780 : Word) = UInt16.ofNat 1780)]
    have hval : decChunk111[4]! = 0 := rfl
    exact (g 1780 (by decide) (by decide)).trans ((cell1776 4 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1824 := by
    have : s.pc + 2 = (1781 : Word) := by simp [hpc]
    rw [this, (rfl : (1781 : Word) = UInt16.ofNat 1781)]
    have hval : decChunk111[5]! = 1824 := rfl
    exact (g 1781 (by decide) (by decide)).trans ((cell1776 5 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV Q2 CH at TQ2 (pc 1782). -/
theorem ed_mov_Q2_CH_1782 {s : Machine}
    (hpc : s.pc = 1782)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1782 ≤ k → k < 1794 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1794 ∧
    s4.halted = false ∧
    s4.mem.get 30 = s.mem.get 22 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 22 = s.mem.get 22 ∧
    (∀ a, a ≠ 30 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1782 :=
    hpc.trans (rfl : (1782 : Word) = UInt16.ofNat 1782)
  have g (k : Nat) (h1 : 1782 ≤ k) (h2 : k < 1794) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1782 + off) :=
    word_pc_off 1782 off hp (by omega)
  have m0 : s.mem.get s.pc = 30 := by
    rw [hp]
    have hval : decChunk111[6]! = 30 := rfl
    exact (g 1782 (by decide) (by decide)).trans ((cell1776 6 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 30 := by
    rw [poff 1 (by decide)]
    have hval : decChunk111[7]! = 30 := rfl
    exact (g 1783 (by decide) (by decide)).trans ((cell1776 7 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk111[8]! = 1785 := rfl
    have hv : (1785 : Word) = UInt16.ofNat 1785 := rfl
    exact (g 1784 (by decide) (by decide)).trans ((cell1776 8 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 22 := by
    rw [poff 3 (by decide)]
    have hval : decChunk111[9]! = 22 := rfl
    exact (g 1785 (by decide) (by decide)).trans ((cell1776 9 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk111[10]! = 0 := rfl
    exact (g 1786 (by decide) (by decide)).trans ((cell1776 10 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk111[11]! = 1788 := rfl
    have hv : (1788 : Word) = UInt16.ofNat 1788 := rfl
    exact (g 1787 (by decide) (by decide)).trans ((cell1776 11 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk111[12]! = 0 := rfl
    exact (g 1788 (by decide) (by decide)).trans ((cell1776 12 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 30 := by
    rw [poff 7 (by decide)]
    have hval : decChunk111[13]! = 30 := rfl
    exact (g 1789 (by decide) (by decide)).trans ((cell1776 13 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk111[14]! = 1791 := rfl
    have hv : (1791 : Word) = UInt16.ofNat 1791 := rfl
    exact (g 1790 (by decide) (by decide)).trans ((cell1776 14 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk111[15]! = 0 := rfl
    exact (g 1791 (by decide) (by decide)).trans ((cell1776 15 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk112[0]! = 0 := rfl
    exact (g 1792 (by decide) (by decide)).trans ((cell1792 0 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk112[1]! = 1794 := rfl
    have hv : (1794 : Word) = UInt16.ofNat 1794 := rfl
    exact (g 1793 (by decide) (by decide)).trans ((cell1792 1 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (30 : Word) := by
    intro i hi
    have : (30 : Word) = UInt16.ofNat 30 := rfl
    rw [this]
    exact pc_off_ne 1782 i 30 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1782 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 22) (dst := 30)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1794 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1794 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1794 = (1794 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP HAVE_CH at pc 1794. -/
theorem ed_enc_jmp_1794 {s : Machine}
    (hpc : s.pc = 1794)
    (hcode : ∀ k : Nat, 1794 ≤ k → k < 1794+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1824 := by
  have hp : s.pc = UInt16.ofNat 1794 :=
    hpc.trans (rfl : (1794 : Word) = UInt16.ofNat 1794)
  have g (k : Nat) (h1 : 1794 ≤ k) (h2 : k < 1794+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk112[2]! = 0 := rfl
    exact (g 1794 (by decide) (by decide)).trans ((cell1792 2 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1795 : Word) := by simp [hpc]
    rw [this, (rfl : (1795 : Word) = UInt16.ofNat 1795)]
    have hval : decChunk112[3]! = 0 := rfl
    exact (g 1795 (by decide) (by decide)).trans ((cell1792 3 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1824 := by
    have : s.pc + 2 = (1796 : Word) := by simp [hpc]
    rw [this, (rfl : (1796 : Word) = UInt16.ofNat 1796)]
    have hval : decChunk112[4]! = 1824 := rfl
    exact (g 1796 (by decide) (by decide)).trans ((cell1792 4 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV Q3 CH at TQ3 (pc 1797). -/
theorem ed_mov_Q3_CH_1797 {s : Machine}
    (hpc : s.pc = 1797)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1797 ≤ k → k < 1809 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1809 ∧
    s4.halted = false ∧
    s4.mem.get 30 = s.mem.get 23 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 23 = s.mem.get 23 ∧
    (∀ a, a ≠ 30 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1797 :=
    hpc.trans (rfl : (1797 : Word) = UInt16.ofNat 1797)
  have g (k : Nat) (h1 : 1797 ≤ k) (h2 : k < 1809) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1797 + off) :=
    word_pc_off 1797 off hp (by omega)
  have m0 : s.mem.get s.pc = 30 := by
    rw [hp]
    have hval : decChunk112[5]! = 30 := rfl
    exact (g 1797 (by decide) (by decide)).trans ((cell1792 5 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 30 := by
    rw [poff 1 (by decide)]
    have hval : decChunk112[6]! = 30 := rfl
    exact (g 1798 (by decide) (by decide)).trans ((cell1792 6 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk112[7]! = 1800 := rfl
    have hv : (1800 : Word) = UInt16.ofNat 1800 := rfl
    exact (g 1799 (by decide) (by decide)).trans ((cell1792 7 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 23 := by
    rw [poff 3 (by decide)]
    have hval : decChunk112[8]! = 23 := rfl
    exact (g 1800 (by decide) (by decide)).trans ((cell1792 8 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk112[9]! = 0 := rfl
    exact (g 1801 (by decide) (by decide)).trans ((cell1792 9 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk112[10]! = 1803 := rfl
    have hv : (1803 : Word) = UInt16.ofNat 1803 := rfl
    exact (g 1802 (by decide) (by decide)).trans ((cell1792 10 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk112[11]! = 0 := rfl
    exact (g 1803 (by decide) (by decide)).trans ((cell1792 11 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 30 := by
    rw [poff 7 (by decide)]
    have hval : decChunk112[12]! = 30 := rfl
    exact (g 1804 (by decide) (by decide)).trans ((cell1792 12 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk112[13]! = 1806 := rfl
    have hv : (1806 : Word) = UInt16.ofNat 1806 := rfl
    exact (g 1805 (by decide) (by decide)).trans ((cell1792 13 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk112[14]! = 0 := rfl
    exact (g 1806 (by decide) (by decide)).trans ((cell1792 14 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk112[15]! = 0 := rfl
    exact (g 1807 (by decide) (by decide)).trans ((cell1792 15 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk113[0]! = 1809 := rfl
    have hv : (1809 : Word) = UInt16.ofNat 1809 := rfl
    exact (g 1808 (by decide) (by decide)).trans ((cell1808 0 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (30 : Word) := by
    intro i hi
    have : (30 : Word) = UInt16.ofNat 30 := rfl
    rw [this]
    exact pc_off_ne 1797 i 30 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1797 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 23) (dst := 30)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1809 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1809 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1809 = (1809 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP HAVE_CH at pc 1809. -/
theorem ed_enc_jmp_1809 {s : Machine}
    (hpc : s.pc = 1809)
    (hcode : ∀ k : Nat, 1809 ≤ k → k < 1809+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1824 := by
  have hp : s.pc = UInt16.ofNat 1809 :=
    hpc.trans (rfl : (1809 : Word) = UInt16.ofNat 1809)
  have g (k : Nat) (h1 : 1809 ≤ k) (h2 : k < 1809+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk113[1]! = 0 := rfl
    exact (g 1809 (by decide) (by decide)).trans ((cell1808 1 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1810 : Word) := by simp [hpc]
    rw [this, (rfl : (1810 : Word) = UInt16.ofNat 1810)]
    have hval : decChunk113[2]! = 0 := rfl
    exact (g 1810 (by decide) (by decide)).trans ((cell1808 2 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1824 := by
    have : s.pc + 2 = (1811 : Word) := by simp [hpc]
    rw [this, (rfl : (1811 : Word) = UInt16.ofNat 1811)]
    have hval : decChunk113[3]! = 1824 := rfl
    exact (g 1811 (by decide) (by decide)).trans ((cell1808 3 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV Q4 CH at TQ4 (pc 1812), falls into HAVE_CH. -/
theorem ed_mov_Q4_CH_1812 {s : Machine}
    (hpc : s.pc = 1812)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1812 ≤ k → k < 1824 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1824 ∧
    s4.halted = false ∧
    s4.mem.get 30 = s.mem.get 24 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 24 = s.mem.get 24 ∧
    (∀ a, a ≠ 30 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1812 :=
    hpc.trans (rfl : (1812 : Word) = UInt16.ofNat 1812)
  have g (k : Nat) (h1 : 1812 ≤ k) (h2 : k < 1824) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1812 + off) :=
    word_pc_off 1812 off hp (by omega)
  have m0 : s.mem.get s.pc = 30 := by
    rw [hp]
    have hval : decChunk113[4]! = 30 := rfl
    exact (g 1812 (by decide) (by decide)).trans ((cell1808 4 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 30 := by
    rw [poff 1 (by decide)]
    have hval : decChunk113[5]! = 30 := rfl
    exact (g 1813 (by decide) (by decide)).trans ((cell1808 5 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk113[6]! = 1815 := rfl
    have hv : (1815 : Word) = UInt16.ofNat 1815 := rfl
    exact (g 1814 (by decide) (by decide)).trans ((cell1808 6 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 24 := by
    rw [poff 3 (by decide)]
    have hval : decChunk113[7]! = 24 := rfl
    exact (g 1815 (by decide) (by decide)).trans ((cell1808 7 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk113[8]! = 0 := rfl
    exact (g 1816 (by decide) (by decide)).trans ((cell1808 8 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk113[9]! = 1818 := rfl
    have hv : (1818 : Word) = UInt16.ofNat 1818 := rfl
    exact (g 1817 (by decide) (by decide)).trans ((cell1808 9 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk113[10]! = 0 := rfl
    exact (g 1818 (by decide) (by decide)).trans ((cell1808 10 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 30 := by
    rw [poff 7 (by decide)]
    have hval : decChunk113[11]! = 30 := rfl
    exact (g 1819 (by decide) (by decide)).trans ((cell1808 11 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk113[12]! = 1821 := rfl
    have hv : (1821 : Word) = UInt16.ofNat 1821 := rfl
    exact (g 1820 (by decide) (by decide)).trans ((cell1808 12 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk113[13]! = 0 := rfl
    exact (g 1821 (by decide) (by decide)).trans ((cell1808 13 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk113[14]! = 0 := rfl
    exact (g 1822 (by decide) (by decide)).trans ((cell1808 14 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk113[15]! = 1824 := rfl
    have hv : (1824 : Word) = UInt16.ofNat 1824 := rfl
    exact (g 1823 (by decide) (by decide)).trans ((cell1808 15 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (30 : Word) := by
    intro i hi
    have : (30 : Word) = UInt16.ofNat 30 := rfl
    rw [this]
    exact pc_off_ne 1812 i 30 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1812 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 24) (dst := 30)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1824 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1824 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1824 = (1824 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- MOV IDX T at HAVE_CH (pc 1824). -/
theorem ed_mov_IDX_T_1824 {s : Machine}
    (hpc : s.pc = 1824)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1824 ≤ k → k < 1836 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1836 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 29 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 29 = s.mem.get 29 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1824 :=
    hpc.trans (rfl : (1824 : Word) = UInt16.ofNat 1824)
  have g (k : Nat) (h1 : 1824 ≤ k) (h2 : k < 1836) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1824 + off) :=
    word_pc_off 1824 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk114[0]! = 18 := rfl
    exact (g 1824 (by decide) (by decide)).trans ((cell1824 0 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk114[1]! = 18 := rfl
    exact (g 1825 (by decide) (by decide)).trans ((cell1824 1 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk114[2]! = 1827 := rfl
    have hv : (1827 : Word) = UInt16.ofNat 1827 := rfl
    exact (g 1826 (by decide) (by decide)).trans ((cell1824 2 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 29 := by
    rw [poff 3 (by decide)]
    have hval : decChunk114[3]! = 29 := rfl
    exact (g 1827 (by decide) (by decide)).trans ((cell1824 3 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk114[4]! = 0 := rfl
    exact (g 1828 (by decide) (by decide)).trans ((cell1824 4 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk114[5]! = 1830 := rfl
    have hv : (1830 : Word) = UInt16.ofNat 1830 := rfl
    exact (g 1829 (by decide) (by decide)).trans ((cell1824 5 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk114[6]! = 0 := rfl
    exact (g 1830 (by decide) (by decide)).trans ((cell1824 6 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk114[7]! = 18 := rfl
    exact (g 1831 (by decide) (by decide)).trans ((cell1824 7 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk114[8]! = 1833 := rfl
    have hv : (1833 : Word) = UInt16.ofNat 1833 := rfl
    exact (g 1832 (by decide) (by decide)).trans ((cell1824 8 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk114[9]! = 0 := rfl
    exact (g 1833 (by decide) (by decide)).trans ((cell1824 9 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk114[10]! = 0 := rfl
    exact (g 1834 (by decide) (by decide)).trans ((cell1824 10 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk114[11]! = 1836 := rfl
    have hv : (1836 : Word) = UInt16.ofNat 1836 := rfl
    exact (g 1835 (by decide) (by decide)).trans ((cell1824 11 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1824 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1824 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 29) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1836 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1836 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1836 = (1836 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- SUB ROOM T at pc 1836. -/
theorem ed_sub_ROOM_T_1836 {s : Machine}
    (hpc : s.pc = 1836)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1836 ≤ k → k < 1839 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 28)
        pc := 1839 } := by
  have hp : s.pc = UInt16.ofNat 1836 :=
    hpc.trans (rfl : (1836 : Word) = UInt16.ofNat 1836)
  have g (k : Nat) (h1 : 1836 ≤ k) (h2 : k < 1839) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 28 := by
    rw [hp]
    have hval : decChunk114[12]! = 28 := rfl
    exact (g 1836 (by decide) (by decide)).trans ((cell1824 12 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1837 : Word) := by simp [hpc]
    rw [this, (rfl : (1837 : Word) = UInt16.ofNat 1837)]
    have hval : decChunk114[13]! = 18 := rfl
    exact (g 1837 (by decide) (by decide)).trans ((cell1824 13 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1838 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1839 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1838 : Word) = UInt16.ofNat 1838)]
    have hval : decChunk114[14]! = 1839 := rfl
    have hv : (1839 : Word) = UInt16.ofNat 1839 := rfl
    exact (g 1838 (by decide) (by decide)).trans ((cell1824 14 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 28) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1839 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T DG_EQ at pc 1839. -/
theorem ed_enc_jlez_1839 {s : Machine}
    (hpc : s.pc = 1839)
    (hcode : ∀ k : Nat, 1839 ≤ k → k < 1839+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1845 := by
  have hp : s.pc = UInt16.ofNat 1839 :=
    hpc.trans (rfl : (1839 : Word) = UInt16.ofNat 1839)
  have g (k : Nat) (h1 : 1839 ≤ k) (h2 : k < 1839+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk114[15]! = 0 := rfl
    exact (g 1839 (by decide) (by decide)).trans ((cell1824 15 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1840 : Word) := by simp [hpc]
    rw [this, (rfl : (1840 : Word) = UInt16.ofNat 1840)]
    have hval : decChunk115[0]! = 18 := rfl
    exact (g 1840 (by decide) (by decide)).trans ((cell1840 0 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1845 := by
    have : s.pc + 2 = (1841 : Word) := by simp [hpc]
    rw [this, (rfl : (1841 : Word) = UInt16.ofNat 1841)]
    have hval : decChunk115[1]! = 1845 := rfl
    exact (g 1841 (by decide) (by decide)).trans ((cell1840 1 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP DIG_NEXT at pc 1842 (IDX > ROOM). -/
theorem ed_enc_jmp_1842 {s : Machine}
    (hpc : s.pc = 1842)
    (hcode : ∀ k : Nat, 1842 ≤ k → k < 1842+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1893 := by
  have hp : s.pc = UInt16.ofNat 1842 :=
    hpc.trans (rfl : (1842 : Word) = UInt16.ofNat 1842)
  have g (k : Nat) (h1 : 1842 ≤ k) (h2 : k < 1842+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk115[2]! = 0 := rfl
    exact (g 1842 (by decide) (by decide)).trans ((cell1840 2 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1843 : Word) := by simp [hpc]
    rw [this, (rfl : (1843 : Word) = UInt16.ofNat 1843)]
    have hval : decChunk115[3]! = 0 := rfl
    exact (g 1843 (by decide) (by decide)).trans ((cell1840 3 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1893 := by
    have : s.pc + 2 = (1844 : Word) := by simp [hpc]
    rw [this, (rfl : (1844 : Word) = UInt16.ofNat 1844)]
    have hval : decChunk115[4]! = 1893 := rfl
    exact (g 1844 (by decide) (by decide)).trans ((cell1840 4 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- INC T at DG_EQ (pc 1845). -/
theorem ed_inc_T_1845 {s : Machine}
    (hpc : s.pc = 1845)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1845 ≤ k → k < 1854 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1854 ∧
    s3.halted = false ∧
    s3.mem.get 18 = s.mem.get 18 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1845 :=
    hpc.trans (rfl : (1845 : Word) = UInt16.ofNat 1845)
  have g (k : Nat) (h1 : 1845 ≤ k) (h2 : k < 1854) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1845 + off) :=
    word_pc_off 1845 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk115[5]! = 3 := rfl
    exact (g 1845 (by decide) (by decide)).trans ((cell1840 5 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk115[6]! = 0 := rfl
    exact (g 1846 (by decide) (by decide)).trans ((cell1840 6 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk115[7]! = 1848 := rfl
    have hv : (1848 : Word) = UInt16.ofNat 1848 := rfl
    exact (g 1847 (by decide) (by decide)).trans ((cell1840 7 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk115[8]! = 0 := rfl
    exact (g 1848 (by decide) (by decide)).trans ((cell1840 8 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 18 := by
    rw [poff 4 (by decide)]
    have hval : decChunk115[9]! = 18 := rfl
    exact (g 1849 (by decide) (by decide)).trans ((cell1840 9 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk115[10]! = 1851 := rfl
    have hv : (1851 : Word) = UInt16.ofNat 1851 := rfl
    exact (g 1850 (by decide) (by decide)).trans ((cell1840 10 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk115[11]! = 0 := rfl
    exact (g 1851 (by decide) (by decide)).trans ((cell1840 11 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk115[12]! = 0 := rfl
    exact (g 1852 (by decide) (by decide)).trans ((cell1840 12 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk115[13]! = 1854 := rfl
    have hv : (1854 : Word) = UInt16.ofNat 1854 := rfl
    exact (g 1853 (by decide) (by decide)).trans ((cell1840 13 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1845 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1845 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1854 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1854 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1854 = (1854 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 18 = s.mem.get 18 + 1 := by
    have : s.mem.get 18 + s.mem.get 3 = s.mem.get 18 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- JLEZ T DG_STORE at pc 1854. -/
theorem ed_enc_jlez_1854 {s : Machine}
    (hpc : s.pc = 1854)
    (hcode : ∀ k : Nat, 1854 ≤ k → k < 1854+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1860 := by
  have hp : s.pc = UInt16.ofNat 1854 :=
    hpc.trans (rfl : (1854 : Word) = UInt16.ofNat 1854)
  have g (k : Nat) (h1 : 1854 ≤ k) (h2 : k < 1854+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk115[14]! = 0 := rfl
    exact (g 1854 (by decide) (by decide)).trans ((cell1840 14 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1855 : Word) := by simp [hpc]
    rw [this, (rfl : (1855 : Word) = UInt16.ofNat 1855)]
    have hval : decChunk115[15]! = 18 := rfl
    exact (g 1855 (by decide) (by decide)).trans ((cell1840 15 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1860 := by
    have : s.pc + 2 = (1856 : Word) := by simp [hpc]
    rw [this, (rfl : (1856 : Word) = UInt16.ofNat 1856)]
    have hval : decChunk116[0]! = 1860 := rfl
    exact (g 1856 (by decide) (by decide)).trans ((cell1856 0 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP DIG_NEXT at pc 1857 (IDX = ROOM). -/
theorem ed_enc_jmp_1857 {s : Machine}
    (hpc : s.pc = 1857)
    (hcode : ∀ k : Nat, 1857 ≤ k → k < 1857+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1893 := by
  have hp : s.pc = UInt16.ofNat 1857 :=
    hpc.trans (rfl : (1857 : Word) = UInt16.ofNat 1857)
  have g (k : Nat) (h1 : 1857 ≤ k) (h2 : k < 1857+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk116[1]! = 0 := rfl
    exact (g 1857 (by decide) (by decide)).trans ((cell1856 1 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1858 : Word) := by simp [hpc]
    rw [this, (rfl : (1858 : Word) = UInt16.ofNat 1858)]
    have hval : decChunk116[2]! = 0 := rfl
    exact (g 1858 (by decide) (by decide)).trans ((cell1856 2 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1893 := by
    have : s.pc + 2 = (1859 : Word) := by simp [hpc]
    rw [this, (rfl : (1859 : Word) = UInt16.ofNat 1859)]
    have hval : decChunk116[3]! = 1893 := rfl
    exact (g 1859 (by decide) (by decide)).trans ((cell1856 3 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV ONE RETID at DG_STORE (pc 1860). -/
theorem ed_mov_ONE_RETID_1860 {s : Machine}
    (hpc : s.pc = 1860)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1860 ≤ k → k < 1872 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1872 ∧
    s4.halted = false ∧
    s4.mem.get 2319 = s.mem.get 3 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 3 = s.mem.get 3 ∧
    (∀ a, a ≠ 2319 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1860 :=
    hpc.trans (rfl : (1860 : Word) = UInt16.ofNat 1860)
  have g (k : Nat) (h1 : 1860 ≤ k) (h2 : k < 1872) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1860 + off) :=
    word_pc_off 1860 off hp (by omega)
  have m0 : s.mem.get s.pc = 2319 := by
    rw [hp]
    have hval : decChunk116[4]! = 2319 := rfl
    exact (g 1860 (by decide) (by decide)).trans ((cell1856 4 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 2319 := by
    rw [poff 1 (by decide)]
    have hval : decChunk116[5]! = 2319 := rfl
    exact (g 1861 (by decide) (by decide)).trans ((cell1856 5 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk116[6]! = 1863 := rfl
    have hv : (1863 : Word) = UInt16.ofNat 1863 := rfl
    exact (g 1862 (by decide) (by decide)).trans ((cell1856 6 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 3 := by
    rw [poff 3 (by decide)]
    have hval : decChunk116[7]! = 3 := rfl
    exact (g 1863 (by decide) (by decide)).trans ((cell1856 7 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk116[8]! = 0 := rfl
    exact (g 1864 (by decide) (by decide)).trans ((cell1856 8 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk116[9]! = 1866 := rfl
    have hv : (1866 : Word) = UInt16.ofNat 1866 := rfl
    exact (g 1865 (by decide) (by decide)).trans ((cell1856 9 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk116[10]! = 0 := rfl
    exact (g 1866 (by decide) (by decide)).trans ((cell1856 10 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 2319 := by
    rw [poff 7 (by decide)]
    have hval : decChunk116[11]! = 2319 := rfl
    exact (g 1867 (by decide) (by decide)).trans ((cell1856 11 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk116[12]! = 1869 := rfl
    have hv : (1869 : Word) = UInt16.ofNat 1869 := rfl
    exact (g 1868 (by decide) (by decide)).trans ((cell1856 12 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk116[13]! = 0 := rfl
    exact (g 1869 (by decide) (by decide)).trans ((cell1856 13 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk116[14]! = 0 := rfl
    exact (g 1870 (by decide) (by decide)).trans ((cell1856 14 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk116[15]! = 1872 := rfl
    have hv : (1872 : Word) = UInt16.ofNat 1872 := rfl
    exact (g 1871 (by decide) (by decide)).trans ((cell1856 15 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (2319 : Word) := by
    intro i hi
    have : (2319 : Word) = UInt16.ofNat 2319 := rfl
    rw [this]
    exact pc_off_ne 1860 i 2319 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1860 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 3) (dst := 2319)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1872 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1872 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1872 = (1872 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- INC RETID at pc 1872. -/
theorem ed_inc_RETID_1872 {s : Machine}
    (hpc : s.pc = 1872)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1872 ≤ k → k < 1881 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1881 ∧
    s3.halted = false ∧
    s3.mem.get 2319 = s.mem.get 2319 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 2319 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1872 :=
    hpc.trans (rfl : (1872 : Word) = UInt16.ofNat 1872)
  have g (k : Nat) (h1 : 1872 ≤ k) (h2 : k < 1881) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1872 + off) :=
    word_pc_off 1872 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk117[0]! = 3 := rfl
    exact (g 1872 (by decide) (by decide)).trans ((cell1872 0 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk117[1]! = 0 := rfl
    exact (g 1873 (by decide) (by decide)).trans ((cell1872 1 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk117[2]! = 1875 := rfl
    have hv : (1875 : Word) = UInt16.ofNat 1875 := rfl
    exact (g 1874 (by decide) (by decide)).trans ((cell1872 2 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk117[3]! = 0 := rfl
    exact (g 1875 (by decide) (by decide)).trans ((cell1872 3 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 2319 := by
    rw [poff 4 (by decide)]
    have hval : decChunk117[4]! = 2319 := rfl
    exact (g 1876 (by decide) (by decide)).trans ((cell1872 4 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk117[5]! = 1878 := rfl
    have hv : (1878 : Word) = UInt16.ofNat 1878 := rfl
    exact (g 1877 (by decide) (by decide)).trans ((cell1872 5 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk117[6]! = 0 := rfl
    exact (g 1878 (by decide) (by decide)).trans ((cell1872 6 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk117[7]! = 0 := rfl
    exact (g 1879 (by decide) (by decide)).trans ((cell1872 7 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk117[8]! = 1881 := rfl
    have hv : (1881 : Word) = UInt16.ofNat 1881 := rfl
    exact (g 1880 (by decide) (by decide)).trans ((cell1872 8 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (2319 : Word) := by
    intro i hi
    have : (2319 : Word) = UInt16.ofNat 2319 := rfl
    rw [this]
    exact pc_off_ne 1872 i 2319 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1872 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 2319)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1881 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1881 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1881 = (1881 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 2319 = s.mem.get 2319 + 1 := by
    have : s.mem.get 2319 + s.mem.get 3 = s.mem.get 2319 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- INC RETID at pc 1881. -/
theorem ed_inc_RETID_1881 {s : Machine}
    (hpc : s.pc = 1881)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1881 ≤ k → k < 1890 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1890 ∧
    s3.halted = false ∧
    s3.mem.get 2319 = s.mem.get 2319 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 2319 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1881 :=
    hpc.trans (rfl : (1881 : Word) = UInt16.ofNat 1881)
  have g (k : Nat) (h1 : 1881 ≤ k) (h2 : k < 1890) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1881 + off) :=
    word_pc_off 1881 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk117[9]! = 3 := rfl
    exact (g 1881 (by decide) (by decide)).trans ((cell1872 9 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk117[10]! = 0 := rfl
    exact (g 1882 (by decide) (by decide)).trans ((cell1872 10 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk117[11]! = 1884 := rfl
    have hv : (1884 : Word) = UInt16.ofNat 1884 := rfl
    exact (g 1883 (by decide) (by decide)).trans ((cell1872 11 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk117[12]! = 0 := rfl
    exact (g 1884 (by decide) (by decide)).trans ((cell1872 12 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 2319 := by
    rw [poff 4 (by decide)]
    have hval : decChunk117[13]! = 2319 := rfl
    exact (g 1885 (by decide) (by decide)).trans ((cell1872 13 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk117[14]! = 1887 := rfl
    have hv : (1887 : Word) = UInt16.ofNat 1887 := rfl
    exact (g 1886 (by decide) (by decide)).trans ((cell1872 14 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk117[15]! = 0 := rfl
    exact (g 1887 (by decide) (by decide)).trans ((cell1872 15 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk118[0]! = 0 := rfl
    exact (g 1888 (by decide) (by decide)).trans ((cell1888 0 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk118[1]! = 1890 := rfl
    have hv : (1890 : Word) = UInt16.ofNat 1890 := rfl
    exact (g 1889 (by decide) (by decide)).trans ((cell1888 1 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (2319 : Word) := by
    intro i hi
    have : (2319 : Word) = UInt16.ofNat 2319 := rfl
    rw [this]
    exact pc_off_ne 1881 i 2319 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1881 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 2319)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1890 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1890 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1890 = (1890 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 2319 = s.mem.get 2319 + 1 := by
    have : s.mem.get 2319 + s.mem.get 3 = s.mem.get 2319 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- JMP STORE_CH at pc 1890. -/
theorem ed_enc_jmp_1890 {s : Machine}
    (hpc : s.pc = 1890)
    (hcode : ∀ k : Nat, 1890 ≤ k → k < 1890+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1185 := by
  have hp : s.pc = UInt16.ofNat 1890 :=
    hpc.trans (rfl : (1890 : Word) = UInt16.ofNat 1890)
  have g (k : Nat) (h1 : 1890 ≤ k) (h2 : k < 1890+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk118[2]! = 0 := rfl
    exact (g 1890 (by decide) (by decide)).trans ((cell1888 2 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1891 : Word) := by simp [hpc]
    rw [this, (rfl : (1891 : Word) = UInt16.ofNat 1891)]
    have hval : decChunk118[3]! = 0 := rfl
    exact (g 1891 (by decide) (by decide)).trans ((cell1888 3 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1185 := by
    have : s.pc + 2 = (1892 : Word) := by simp [hpc]
    rw [this, (rfl : (1892 : Word) = UInt16.ofNat 1892)]
    have hval : decChunk118[4]! = 1185 := rfl
    exact (g 1892 (by decide) (by decide)).trans ((cell1888 4 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- INC DI at DIG_NEXT (pc 1893). -/
theorem ed_inc_DI_1893 {s : Machine}
    (hpc : s.pc = 1893)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1893 ≤ k → k < 1902 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1902 ∧
    s3.halted = false ∧
    s3.mem.get 2321 = s.mem.get 2321 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 2321 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1893 :=
    hpc.trans (rfl : (1893 : Word) = UInt16.ofNat 1893)
  have g (k : Nat) (h1 : 1893 ≤ k) (h2 : k < 1902) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1893 + off) :=
    word_pc_off 1893 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk118[5]! = 3 := rfl
    exact (g 1893 (by decide) (by decide)).trans ((cell1888 5 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk118[6]! = 0 := rfl
    exact (g 1894 (by decide) (by decide)).trans ((cell1888 6 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk118[7]! = 1896 := rfl
    have hv : (1896 : Word) = UInt16.ofNat 1896 := rfl
    exact (g 1895 (by decide) (by decide)).trans ((cell1888 7 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk118[8]! = 0 := rfl
    exact (g 1896 (by decide) (by decide)).trans ((cell1888 8 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 2321 := by
    rw [poff 4 (by decide)]
    have hval : decChunk118[9]! = 2321 := rfl
    exact (g 1897 (by decide) (by decide)).trans ((cell1888 9 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk118[10]! = 1899 := rfl
    have hv : (1899 : Word) = UInt16.ofNat 1899 := rfl
    exact (g 1898 (by decide) (by decide)).trans ((cell1888 10 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk118[11]! = 0 := rfl
    exact (g 1899 (by decide) (by decide)).trans ((cell1888 11 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk118[12]! = 0 := rfl
    exact (g 1900 (by decide) (by decide)).trans ((cell1888 12 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk118[13]! = 1902 := rfl
    have hv : (1902 : Word) = UInt16.ofNat 1902 := rfl
    exact (g 1901 (by decide) (by decide)).trans ((cell1888 13 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (2321 : Word) := by
    intro i hi
    have : (2321 : Word) = UInt16.ofNat 2321 := rfl
    rw [this]
    exact pc_off_ne 1893 i 2321 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1893 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 2321)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1902 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1902 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1902 = (1902 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 2321 = s.mem.get 2321 + 1 := by
    have : s.mem.get 2321 + s.mem.get 3 = s.mem.get 2321 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- JMP DIG_LOOP at pc 1902. -/
theorem ed_enc_jmp_1902 {s : Machine}
    (hpc : s.pc = 1902)
    (hcode : ∀ k : Nat, 1902 ≤ k → k < 1902+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1641 := by
  have hp : s.pc = UInt16.ofNat 1902 :=
    hpc.trans (rfl : (1902 : Word) = UInt16.ofNat 1902)
  have g (k : Nat) (h1 : 1902 ≤ k) (h2 : k < 1902+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk118[14]! = 0 := rfl
    exact (g 1902 (by decide) (by decide)).trans ((cell1888 14 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1903 : Word) := by simp [hpc]
    rw [this, (rfl : (1903 : Word) = UInt16.ofNat 1903)]
    have hval : decChunk118[15]! = 0 := rfl
    exact (g 1903 (by decide) (by decide)).trans ((cell1888 15 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1641 := by
    have : s.pc + 2 = (1904 : Word) := by simp [hpc]
    rw [this, (rfl : (1904 : Word) = UInt16.ofNat 1904)]
    have hval : decChunk119[0]! = 1641 := rfl
    exact (g 1904 (by decide) (by decide)).trans ((cell1904 0 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- `EMIT_DIGS` prelude: 22 steps to `DIG_LOOP` with `SK = 5 - NDIG` and `DI = 0`. -/
theorem emit_prelude {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hNle : (s.mem.get 25).toNat ≤ 5)
    (hcode : ∀ k : Nat, 1575 ≤ k → k < 1641 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s22 := runN s 22
    s22.pc = 1641 ∧
    s22.halted = false ∧
    s22.mem.get 0 = 0 ∧
    s22.mem.get 2320 = (5 : Word) - s.mem.get 25 ∧
    s22.mem.get 2321 = 0 ∧
    s22.mem.get 31 = (5 : Word) - s.mem.get 25 ∧
    (∀ a, a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → s22.mem.get a = s.mem.get a) := by
  intro s22
  have hm := ed_mov_ONE_TMP_1575 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1587 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 31 = 1 := hm.2.2.1.trans hONE
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hN4 : s4.mem.get 25 = s.mem.get 25 := hpres4 25 (by decide) (by decide)
  have g4 : ∀ k : Nat, 1587 ≤ k → k < 1623 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n31 n0).trans (hcode k (by omega) (by omega))
  have ha1 := ed_add_ONE_TMP_1587 (s := s4) hs4pc hs4h hs4Z hONE4
    (fun k h1 h2 => g4 k h1 (by omega))
  have hrun7 : runN s 7 = runN s4 3 := runN_add_eq s 4 3 7 (by decide)
  let s7 := runN s 7
  have hs7eq : s7 = runN s4 3 := hrun7
  have hs7pc : s7.pc = 1596 := by rw [hs7eq]; exact ha1.1
  have hs7h : s7.halted = false := by rw [hs7eq]; exact ha1.2.1
  have hs7T : s7.mem.get 31 = 2 := by
    rw [hs7eq, ha1.2.2.1, hs4T]; exact (rfl : (1 : Word) + 1 = 2)
  have hs7Z : s7.mem.get 0 = 0 := by rw [hs7eq]; exact ha1.2.2.2.1
  have hpres7 : ∀ a, a ≠ 31 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    rw [hs7eq]; exact (ha1.2.2.2.2 a ha31 ha0).trans (hpres4 a ha31 ha0)
  have hONE7 : s7.mem.get 3 = 1 := (hpres7 3 (by decide) (by decide)).trans hONE
  have g7 : ∀ k : Nat, 1596 ≤ k → k < 1623 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres7 (UInt16.ofNat k) n31 n0).trans (hcode k (by omega) (by omega))
  have ha2 := ed_add_ONE_TMP_1596 (s := s7) hs7pc hs7h hs7Z hONE7
    (fun k h1 h2 => g7 k h1 (by omega))
  have hrun10 : runN s 10 = runN s7 3 := runN_add_eq s 7 3 10 (by decide)
  let s10 := runN s 10
  have hs10eq : s10 = runN s7 3 := hrun10
  have hs10pc : s10.pc = 1605 := by rw [hs10eq]; exact ha2.1
  have hs10h : s10.halted = false := by rw [hs10eq]; exact ha2.2.1
  have hs10T : s10.mem.get 31 = 3 := by
    rw [hs10eq, ha2.2.2.1, hs7T]; exact (rfl : (2 : Word) + 1 = 3)
  have hs10Z : s10.mem.get 0 = 0 := by rw [hs10eq]; exact ha2.2.2.2.1
  have hpres10 : ∀ a, a ≠ 31 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    rw [hs10eq]; exact (ha2.2.2.2.2 a ha31 ha0).trans (hpres7 a ha31 ha0)
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have g10 : ∀ k : Nat, 1605 ≤ k → k < 1623 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n31 n0).trans (hcode k (by omega) (by omega))
  have ha3 := ed_add_ONE_TMP_1605 (s := s10) hs10pc hs10h hs10Z hONE10
    (fun k h1 h2 => g10 k h1 (by omega))
  have hrun13 : runN s 13 = runN s10 3 := runN_add_eq s 10 3 13 (by decide)
  let s13 := runN s 13
  have hs13eq : s13 = runN s10 3 := hrun13
  have hs13pc : s13.pc = 1614 := by rw [hs13eq]; exact ha3.1
  have hs13h : s13.halted = false := by rw [hs13eq]; exact ha3.2.1
  have hs13T : s13.mem.get 31 = 4 := by
    rw [hs13eq, ha3.2.2.1, hs10T]; exact (rfl : (3 : Word) + 1 = 4)
  have hs13Z : s13.mem.get 0 = 0 := by rw [hs13eq]; exact ha3.2.2.2.1
  have hpres13 : ∀ a, a ≠ 31 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    rw [hs13eq]; exact (ha3.2.2.2.2 a ha31 ha0).trans (hpres10 a ha31 ha0)
  have hONE13 : s13.mem.get 3 = 1 := (hpres13 3 (by decide) (by decide)).trans hONE
  have g13 : ∀ k : Nat, 1614 ≤ k → k < 1623 →
      s13.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres13 (UInt16.ofNat k) n31 n0).trans (hcode k (by omega) (by omega))
  have ha4 := ed_add_ONE_TMP_1614 (s := s13) hs13pc hs13h hs13Z hONE13
    (fun k h1 h2 => g13 k h1 (by omega))
  have hrun16 : runN s 16 = runN s13 3 := runN_add_eq s 13 3 16 (by decide)
  let s16 := runN s 16
  have hs16eq : s16 = runN s13 3 := hrun16
  have hs16pc : s16.pc = 1623 := by rw [hs16eq]; exact ha4.1
  have hs16h : s16.halted = false := by rw [hs16eq]; exact ha4.2.1
  have hs16T : s16.mem.get 31 = 5 := by
    rw [hs16eq, ha4.2.2.1, hs13T]; exact (rfl : (4 : Word) + 1 = 5)
  have hs16Z : s16.mem.get 0 = 0 := by rw [hs16eq]; exact ha4.2.2.2.1
  have hpres16 : ∀ a, a ≠ 31 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    rw [hs16eq]; exact (ha4.2.2.2.2 a ha31 ha0).trans (hpres13 a ha31 ha0)
  have hN16 : s16.mem.get 25 = s.mem.get 25 := hpres16 25 (by decide) (by decide)
  have g16 : ∀ k : Nat, 1623 ≤ k → k < 1626 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n31 n0).trans (hcode k (by omega) (by omega))
  have hsub := ed_sub_NDIG_TMP_1623 (s := s16) hs16pc hs16h g16
  have hrun17 : runN s 17 = step s16 := by
    have h17 : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
    have hpc16 : s16.pc.toNat < 32768 := by simp [hs16pc]
    exact h17.trans (runN_one s16 hs16h hpc16)
  let s17 := runN s 17
  have hs17eq' : s17 =
      { s16 with mem := s16.mem.set 31 (s16.mem.get 31 - s16.mem.get 25), pc := 1626 } := by
    have : s17 = step s16 := hrun17
    rw [this, hsub]
  have hs17pc : s17.pc = 1626 := by rw [hs17eq']
  have hs17h : s17.halted = false := by rw [hs17eq']; exact hs16h
  have hs17T : s17.mem.get 31 = (5 : Word) - s.mem.get 25 := by
    rw [hs17eq', Mem.get_set_eq, hs16T, hN16]
  have hs17Z : s17.mem.get 0 = 0 := by
    rw [hs17eq']
    exact (Mem.get_set_ne s16.mem 31 0 (s16.mem.get 31 - s16.mem.get 25) (by decide)).trans hs16Z
  have hpres17 : ∀ a, a ≠ 31 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha31 ha0
    rw [hs17eq']
    exact (Mem.get_set_ne s16.mem 31 a (s16.mem.get 31 - s16.mem.get 25) ha31).trans
      (hpres16 a ha31 ha0)
  have g17 : ∀ k : Nat, 1626 ≤ k → k < 1638 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n31 n0).trans (hcode k (by omega) (by omega))
  have hm2 := ed_mov_TMP_SK_1626 (s := s17) hs17pc hs17h hs17Z g17
  have hrun21 : runN s 21 = runN s17 4 := runN_add_eq s 17 4 21 (by decide)
  let s21 := runN s 21
  have hs21eq : s21 = runN s17 4 := hrun21
  have hs21pc : s21.pc = 1638 := by rw [hs21eq]; exact hm2.1
  have hs21h : s21.halted = false := by rw [hs21eq]; exact hm2.2.1
  have hs21SK : s21.mem.get 2320 = (5 : Word) - s.mem.get 25 := by
    rw [hs21eq, hm2.2.2.1, hs17T]
  have hs21Z : s21.mem.get 0 = 0 := by rw [hs21eq]; exact hm2.2.2.2.1
  have hs21T : s21.mem.get 31 = (5 : Word) - s.mem.get 25 := by
    rw [hs21eq]
    exact (hm2.2.2.2.2.1).trans hs17T
  have hpres21 : ∀ a, a ≠ 31 → a ≠ 2320 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha31 haSK ha0
    rw [hs21eq]
    exact (hm2.2.2.2.2.2 a haSK ha0).trans (hpres17 a ha31 ha0)
  have g21 : ∀ k : Nat, 1638 ≤ k → k < 1641 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have nSK : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n31 nSK n0).trans (hcode k (by omega) (by omega))
  have hz := ed_zero_DI_1638 (s := s21) hs21pc hs21h g21
  have hrun : s22 = step s21 := by
    have h22 : runN s 22 = runN s21 1 := runN_add_eq s 21 1 22 (by decide)
    have hpc21 : s21.pc.toNat < 32768 := by simp [hs21pc]
    exact h22.trans (runN_one s21 hs21h hpc21)
  have hs22eq' : s22 = { s21 with mem := s21.mem.set 2321 0, pc := 1641 } := by
    rw [hrun, hz]
  have hs22pc : s22.pc = 1641 := by rw [hs22eq']
  have hs22h : s22.halted = false := by rw [hs22eq']; exact hs21h
  have hs22Z : s22.mem.get 0 = 0 := by
    rw [hs22eq']
    exact (Mem.get_set_ne s21.mem 2321 0 0 (by decide)).trans hs21Z
  have hs22SK : s22.mem.get 2320 = (5 : Word) - s.mem.get 25 := by
    rw [hs22eq']
    exact (Mem.get_set_ne s21.mem 2321 2320 0 (by decide)).trans hs21SK
  have hs22DI : s22.mem.get 2321 = 0 := by rw [hs22eq', Mem.get_set_eq]
  have hs22T : s22.mem.get 31 = (5 : Word) - s.mem.get 25 := by
    rw [hs22eq']
    exact (Mem.get_set_ne s21.mem 2321 31 0 (by decide)).trans hs21T
  have hpres : ∀ a, a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → s22.mem.get a = s.mem.get a := by
    intro a ha31 haSK haDI ha0
    rw [hs22eq']
    exact (Mem.get_set_ne s21.mem 2321 a 0 haDI).trans (hpres21 a ha31 haSK ha0)
  exact ⟨hs22pc, hs22h, hs22Z, hs22SK, hs22DI, hs22T, hpres⟩

/-- `DIG_NEXT`: increment `DI` and jump back to `DIG_LOOP`. 4 steps. -/
theorem dig_next {s : Machine}
    (hpc : s.pc = 1893)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1641 ∧
    s4.halted = false ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 2321 = s.mem.get 2321 + 1 ∧
    (∀ a, a ≠ 2321 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hinc := ed_inc_DI_1893 (s := s) hpc hh hZ hONE
    (fun k h1 h2 => hcode k h1 (by omega))
  let s3 := runN s 3
  have hs3pc : s3.pc = 1902 := hinc.1
  have hs3h : s3.halted = false := hinc.2.1
  have hs3DI : s3.mem.get 2321 = s.mem.get 2321 + 1 := hinc.2.2.1
  have hs3Z : s3.mem.get 0 = 0 := hinc.2.2.2.1
  have hpres3 := hinc.2.2.2.2
  have g3 : ∀ k : Nat, 1902 ≤ k → k < 1905 →
      s3.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nDI : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres3 (UInt16.ofNat k) nDI n0).trans (hcode k (by omega) (by omega))
  have henc := ed_enc_jmp_1902 (s := s3) hs3pc g3
  have hpc3 : s3.pc.toNat < 32768 := by simp [hs3pc]
  have hjmp := step_JMP (s := s3) (dest := 1641)
    hs3h hpc3 hs3Z henc.1 henc.2.1 henc.2.2
  have hrun : s4 = step s3 := by
    have h4 : runN s 4 = runN s3 1 := runN_add_eq s 3 1 4 (by decide)
    exact h4.trans (runN_one s3 hs3h hpc3)
  have hs4pc : s4.pc = 1641 := by rw [hrun, hjmp]
  have hs4h : s4.halted = false := by rw [hrun, hjmp]; exact hs3h
  have hs4Z : s4.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs3Z
  have hs4DI : s4.mem.get 2321 = s.mem.get 2321 + 1 := by rw [hrun, hjmp]; exact hs3DI
  have hpres : ∀ a, a ≠ 2321 → a ≠ 0 → s4.mem.get a = s.mem.get a := by
    intro a haDI ha0
    rw [hrun, hjmp]; exact hpres3 a haDI ha0
  exact ⟨hs4pc, hs4h, hs4Z, hs4DI, hpres⟩

/-- `DIG_LOOP` with `DI = 5`: 11 steps to `AFTER_DIGS`. -/
theorem dig_loop_exit {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 5)
    (hK5 : s.mem.get 2322 = 5)
    (hcode : ∀ k : Nat, 1641 ≤ k → k < 1677 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s11 := runN s 11
    s11.pc = 1905 ∧
    s11.halted = false ∧
    s11.mem.get 0 = 0 ∧
    s11.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a) := by
  intro s11
  have hm := ed_mov_DI_T_1641 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1653 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 5 := hm.2.2.1.trans hDI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hK4 : s4.mem.get 2322 = 5 := (hpres4 2322 (by decide) (by decide)).trans hK5
  have hDI4 : s4.mem.get 2321 = 5 := (hpres4 2321 (by decide) (by decide)).trans hDI
  have g4 : ∀ k : Nat, 1653 ≤ k → k < 1659 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hsub := ed_sub_K5_T_1653 (s := s4) hs4pc hs4h
    (fun k h1 h2 => g4 k h1 (by omega))
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5eq' : s5 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - s4.mem.get 2322), pc := 1656 } := by
    have : s5 = step s4 := hrun5
    rw [this, hsub]
  have hs5pc : s5.pc = 1656 := by rw [hs5eq']
  have hs5h : s5.halted = false := by rw [hs5eq']; exact hs4h
  have hs5T : s5.mem.get 18 = 0 := by
    rw [hs5eq', Mem.get_set_eq, hs4T, hK4]
    exact (rfl : (5 : Word) - 5 = 0)
  have hs5Z : s5.mem.get 0 = 0 := by
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - s4.mem.get 2322) (by decide)).trans hs4Z
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - s4.mem.get 2322) ha18).trans
      (hpres4 a ha18 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hDI5 : s5.mem.get 2321 = 5 := (hpres5 2321 (by decide) (by decide)).trans hDI
  have g5 : ∀ k : Nat, 1656 ≤ k → k < 1659 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc1 := ed_enc_jlez_1656 (s := s5) hs5pc g5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj1 :=
    step_JLEZ (s := s5) (x := 18) (dest := 1662)
      hs5h hpc5 hs5Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = true := by
    have : le0 (s5.mem.get 18) = true := by rw [hs5T]; exact le0_zero
    simpa [le0] using this
  have hs6eq' : step s5 = { s5 with pc := 1662 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (1662 : Word) else s5.pc + 3) = (1662 : Word) := by
      simp [hle1]
    rw [hj1, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hs6pc : s6.pc = 1662 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5Z
  have hs6T : s6.mem.get 18 = 0 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5T
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq']; exact hpres5 a ha18 ha0
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have hDI6 : s6.mem.get 2321 = 5 := (hpres6 2321 (by decide) (by decide)).trans hDI
  have g6 : ∀ k : Nat, 1662 ≤ k → k < 1671 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hinc := ed_inc_T_1662 (s := s6) hs6pc hs6h hs6Z hONE6 g6
  have hrun9 : runN s 9 = runN s6 3 := runN_add_eq s 6 3 9 (by decide)
  let s9 := runN s 9
  have hs9eq : s9 = runN s6 3 := hrun9
  have hs9pc : s9.pc = 1671 := by rw [hs9eq]; exact hinc.1
  have hs9h : s9.halted = false := by rw [hs9eq]; exact hinc.2.1
  have hs9T : s9.mem.get 18 = 1 := by
    rw [hs9eq, hinc.2.2.1, hs6T]; exact (rfl : (0 : Word) + 1 = 1)
  have hs9Z : s9.mem.get 0 = 0 := by rw [hs9eq]; exact hinc.2.2.2.1
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs9eq]; exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hDI9 : s9.mem.get 2321 = 5 := (hpres9 2321 (by decide) (by decide)).trans hDI
  have g9 : ∀ k : Nat, 1671 ≤ k → k < 1677 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc2 := ed_enc_jlez_1671 (s := s9) hs9pc
    (fun k h1 h2 => g9 k h1 (by omega))
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hj2 :=
    step_JLEZ (s := s9) (x := 18) (dest := 1677)
      hs9h hpc9 hs9Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = false := by
    have : le0 (s9.mem.get 18) = false := by
      rw [hs9T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs10eq' : step s9 = { s9 with pc := 1674 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18
          then (1677 : Word) else s9.pc + 3) = (1674 : Word) := by
      have hfall : s9.pc + 3 = (1674 : Word) := by simp [hs9pc]
      simp [hle2, hfall]
    rw [hj2, hif]
  have hrun10 : runN s 10 = step s9 := by
    have h10 : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact h10.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hs10pc : s10.pc = 1674 := by have : s10 = step s9 := hrun10; rw [this, hs10eq']
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq']; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by have : s10 = step s9 := hrun10; rw [this, hs10eq']; exact hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq']; exact hpres9 a ha18 ha0
  have hDI10 : s10.mem.get 2321 = 5 := (hpres10 2321 (by decide) (by decide)).trans hDI
  have g10 : ∀ k : Nat, 1674 ≤ k → k < 1677 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc3 := ed_enc_jmp_1674 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hj3 := step_JMP (s := s10) (dest := 1905)
    hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2
  have hrun : s11 = step s10 := by
    have h11 : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact h11.trans (runN_one s10 hs10h hpc10)
  have hs11pc : s11.pc = 1905 := by rw [hrun, hj3]
  have hs11h : s11.halted = false := by rw [hrun, hj3]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by rw [hrun, hj3]; exact hs10Z
  have hs11DI : s11.mem.get 2321 = 5 := by rw [hrun, hj3]; exact hDI10
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hj3]; exact hpres10 a ha18 ha0
  exact ⟨hs11pc, hs11h, hs11Z, hs11DI, hpres⟩

/-- `DIG_LOOP` with `DI < 5`: 10 steps to `DIG_BODY`, `DI` unchanged. -/
theorem dig_loop_to_body {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDIlt : (s.mem.get 2321).toNat < 5)
    (hK5 : s.mem.get 2322 = 5)
    (hcode : ∀ k : Nat, 1641 ≤ k → k < 1677 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s10 := runN s 10
    s10.pc = 1677 ∧
    s10.halted = false ∧
    s10.mem.get 0 = 0 ∧
    s10.mem.get 2321 = s.mem.get 2321 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a) := by
  intro s10
  have hm := ed_mov_DI_T_1641 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1653 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 2321 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hK4 : s4.mem.get 2322 = 5 := (hpres4 2322 (by decide) (by decide)).trans hK5
  have hDI4 : s4.mem.get 2321 = s.mem.get 2321 := hpres4 2321 (by decide) (by decide)
  have g4 : ∀ k : Nat, 1653 ≤ k → k < 1659 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hsub := ed_sub_K5_T_1653 (s := s4) hs4pc hs4h
    (fun k h1 h2 => g4 k h1 (by omega))
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5eq' : s5 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - s4.mem.get 2322), pc := 1656 } := by
    have : s5 = step s4 := hrun5
    rw [this, hsub]
  have hs5pc : s5.pc = 1656 := by rw [hs5eq']
  have hs5h : s5.halted = false := by rw [hs5eq']; exact hs4h
  have hs5T : s5.mem.get 18 = s.mem.get 2321 - 5 := by
    rw [hs5eq', Mem.get_set_eq, hs4T, hK4]
  have hs5Z : s5.mem.get 0 = 0 := by
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - s4.mem.get 2322) (by decide)).trans hs4Z
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - s4.mem.get 2322) ha18).trans
      (hpres4 a ha18 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hDI5 : s5.mem.get 2321 = s.mem.get 2321 := hpres5 2321 (by decide) (by decide)
  have g5 : ∀ k : Nat, 1656 ≤ k → k < 1659 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc1 := ed_enc_jlez_1656 (s := s5) hs5pc g5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj1 :=
    step_JLEZ (s := s5) (x := 18) (dest := 1662)
      hs5h hpc5 hs5Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = true := by
    have : le0 (s5.mem.get 18) = true := by
      rw [hs5T]
      exact idx_lt_room_le0 (s.mem.get 2321) 5 (by decide) hDIlt
    simpa [le0] using this
  have hs6eq' : step s5 = { s5 with pc := 1662 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (1662 : Word) else s5.pc + 3) = (1662 : Word) := by
      simp [hle1]
    rw [hj1, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hs6pc : s6.pc = 1662 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5Z
  have hs6T : s6.mem.get 18 = s.mem.get 2321 - 5 := by
    have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5T
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq']; exact hpres5 a ha18 ha0
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have hDI6 : s6.mem.get 2321 = s.mem.get 2321 := hpres6 2321 (by decide) (by decide)
  have g6 : ∀ k : Nat, 1662 ≤ k → k < 1671 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hinc := ed_inc_T_1662 (s := s6) hs6pc hs6h hs6Z hONE6 g6
  have hrun9 : runN s 9 = runN s6 3 := runN_add_eq s 6 3 9 (by decide)
  let s9 := runN s 9
  have hs9eq : s9 = runN s6 3 := hrun9
  have hs9pc : s9.pc = 1671 := by rw [hs9eq]; exact hinc.1
  have hs9h : s9.halted = false := by rw [hs9eq]; exact hinc.2.1
  have hs9T : s9.mem.get 18 = (s.mem.get 2321 - 5) + 1 := by
    rw [hs9eq, hinc.2.2.1, hs6T]
  have hs9Z : s9.mem.get 0 = 0 := by rw [hs9eq]; exact hinc.2.2.2.1
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs9eq]; exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hDI9 : s9.mem.get 2321 = s.mem.get 2321 := hpres9 2321 (by decide) (by decide)
  have g9 : ∀ k : Nat, 1671 ≤ k → k < 1674 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc2 := ed_enc_jlez_1671 (s := s9) hs9pc g9
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hj2 :=
    step_JLEZ (s := s9) (x := 18) (dest := 1677)
      hs9h hpc9 hs9Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = true := by
    have : le0 (s9.mem.get 18) = true := by
      rw [hs9T]
      exact idx_lt_room_inc_le0 (s.mem.get 2321) 5 (by decide) hDIlt
    simpa [le0] using this
  have hs10eq' : step s9 = { s9 with pc := 1677 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18
          then (1677 : Word) else s9.pc + 3) = (1677 : Word) := by
      simp [hle2]
    rw [hj2, hif]
  have hrun : s10 = step s9 := by
    have h10 : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact h10.trans (runN_one s9 hs9h hpc9)
  have hs10pc : s10.pc = 1677 := by rw [hrun, hs10eq']
  have hs10h : s10.halted = false := by rw [hrun, hs10eq']; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by rw [hrun, hs10eq']; exact hs9Z
  have hs10DI : s10.mem.get 2321 = s.mem.get 2321 := by rw [hrun, hs10eq']; exact hDI9
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hs10eq']; exact hpres9 a ha18 ha0
  exact ⟨hs10pc, hs10h, hs10Z, hs10DI, hpres⟩

/-- `DIG_BODY` with `DI < SK`: 11 steps to `DIG_NEXT`, no store. -/
theorem dig_body_skip {s : Machine}
    (hpc : s.pc = 1677)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDIlt : (s.mem.get 2321).toNat < (s.mem.get 2320).toNat)
    (hSKhi : (s.mem.get 2320).toNat < 32768)
    (hcode : ∀ k : Nat, 1677 ≤ k → k < 1716 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s11 := runN s 11
    s11.pc = 1893 ∧
    s11.halted = false ∧
    s11.mem.get 0 = 0 ∧
    s11.mem.get 2321 = s.mem.get 2321 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a) := by
  intro s11
  have hm := ed_mov_DI_T_1677 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1689 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 2321 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hSK4 : s4.mem.get 2320 = s.mem.get 2320 := hpres4 2320 (by decide) (by decide)
  have hDI4 : s4.mem.get 2321 = s.mem.get 2321 := hpres4 2321 (by decide) (by decide)
  have g4 : ∀ k : Nat, 1689 ≤ k → k < 1695 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hsub := ed_sub_SK_T_1689 (s := s4) hs4pc hs4h
    (fun k h1 h2 => g4 k h1 (by omega))
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5eq' : s5 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - s4.mem.get 2320), pc := 1692 } := by
    have : s5 = step s4 := hrun5
    rw [this, hsub]
  have hs5pc : s5.pc = 1692 := by rw [hs5eq']
  have hs5h : s5.halted = false := by rw [hs5eq']; exact hs4h
  have hs5T : s5.mem.get 18 = s.mem.get 2321 - s.mem.get 2320 := by
    rw [hs5eq', Mem.get_set_eq, hs4T, hSK4]
  have hs5Z : s5.mem.get 0 = 0 := by
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - s4.mem.get 2320) (by decide)).trans hs4Z
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - s4.mem.get 2320) ha18).trans
      (hpres4 a ha18 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hDI5 : s5.mem.get 2321 = s.mem.get 2321 := hpres5 2321 (by decide) (by decide)
  have g5 : ∀ k : Nat, 1692 ≤ k → k < 1695 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc1 := ed_enc_jlez_1692 (s := s5) hs5pc g5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj1 :=
    step_JLEZ (s := s5) (x := 18) (dest := 1698)
      hs5h hpc5 hs5Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = true := by
    have : le0 (s5.mem.get 18) = true := by
      rw [hs5T]
      exact idx_lt_room_le0 (s.mem.get 2321) (s.mem.get 2320) hSKhi hDIlt
    simpa [le0] using this
  have hs6eq' : step s5 = { s5 with pc := 1698 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (1698 : Word) else s5.pc + 3) = (1698 : Word) := by
      simp [hle1]
    rw [hj1, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hs6pc : s6.pc = 1698 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5Z
  have hs6T : s6.mem.get 18 = s.mem.get 2321 - s.mem.get 2320 := by
    have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5T
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq']; exact hpres5 a ha18 ha0
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have hDI6 : s6.mem.get 2321 = s.mem.get 2321 := hpres6 2321 (by decide) (by decide)
  have g6 : ∀ k : Nat, 1698 ≤ k → k < 1707 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hinc := ed_inc_T_1698 (s := s6) hs6pc hs6h hs6Z hONE6 g6
  have hrun9 : runN s 9 = runN s6 3 := runN_add_eq s 6 3 9 (by decide)
  let s9 := runN s 9
  have hs9eq : s9 = runN s6 3 := hrun9
  have hs9pc : s9.pc = 1707 := by rw [hs9eq]; exact hinc.1
  have hs9h : s9.halted = false := by rw [hs9eq]; exact hinc.2.1
  have hs9T : s9.mem.get 18 = (s.mem.get 2321 - s.mem.get 2320) + 1 := by
    rw [hs9eq, hinc.2.2.1, hs6T]
  have hs9Z : s9.mem.get 0 = 0 := by rw [hs9eq]; exact hinc.2.2.2.1
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs9eq]; exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hDI9 : s9.mem.get 2321 = s.mem.get 2321 := hpres9 2321 (by decide) (by decide)
  have g9 : ∀ k : Nat, 1707 ≤ k → k < 1713 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc2 := ed_enc_jlez_1707 (s := s9) hs9pc
    (fun k h1 h2 => g9 k h1 (by omega))
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hj2 :=
    step_JLEZ (s := s9) (x := 18) (dest := 1713)
      hs9h hpc9 hs9Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = true := by
    have : le0 (s9.mem.get 18) = true := by
      rw [hs9T]
      exact idx_lt_room_inc_le0 (s.mem.get 2321) (s.mem.get 2320) hSKhi hDIlt
    simpa [le0] using this
  have hs10eq' : step s9 = { s9 with pc := 1713 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18
          then (1713 : Word) else s9.pc + 3) = (1713 : Word) := by
      simp [hle2]
    rw [hj2, hif]
  have hrun10 : runN s 10 = step s9 := by
    have h10 : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact h10.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hs10pc : s10.pc = 1713 := by have : s10 = step s9 := hrun10; rw [this, hs10eq']
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq']; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by have : s10 = step s9 := hrun10; rw [this, hs10eq']; exact hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq']; exact hpres9 a ha18 ha0
  have hDI10 : s10.mem.get 2321 = s.mem.get 2321 := hpres10 2321 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1713 ≤ k → k < 1716 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc3 := ed_enc_jmp_1713 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hj3 := step_JMP (s := s10) (dest := 1893)
    hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2
  have hrun : s11 = step s10 := by
    have h11 : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact h11.trans (runN_one s10 hs10h hpc10)
  have hs11pc : s11.pc = 1893 := by rw [hrun, hj3]
  have hs11h : s11.halted = false := by rw [hrun, hj3]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by rw [hrun, hj3]; exact hs10Z
  have hs11DI : s11.mem.get 2321 = s.mem.get 2321 := by rw [hrun, hj3]; exact hDI10
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hj3]; exact hpres10 a ha18 ha0
  exact ⟨hs11pc, hs11h, hs11Z, hs11DI, hpres⟩

/-- `DIG_BODY` with `DI = SK`: 11 steps to `TAKE_DIG`. -/
theorem dig_body_take_eq {s : Machine}
    (hpc : s.pc = 1677)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = s.mem.get 2320)
    (hcode : ∀ k : Nat, 1677 ≤ k → k < 1716 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s11 := runN s 11
    s11.pc = 1716 ∧
    s11.halted = false ∧
    s11.mem.get 0 = 0 ∧
    s11.mem.get 2321 = s.mem.get 2321 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a) := by
  intro s11
  have hm := ed_mov_DI_T_1677 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1689 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 2321 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hSK4 : s4.mem.get 2320 = s.mem.get 2320 := hpres4 2320 (by decide) (by decide)
  have g4 : ∀ k : Nat, 1689 ≤ k → k < 1695 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hsub := ed_sub_SK_T_1689 (s := s4) hs4pc hs4h
    (fun k h1 h2 => g4 k h1 (by omega))
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5eq' : s5 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - s4.mem.get 2320), pc := 1692 } := by
    have : s5 = step s4 := hrun5
    rw [this, hsub]
  have hs5pc : s5.pc = 1692 := by rw [hs5eq']
  have hs5h : s5.halted = false := by rw [hs5eq']; exact hs4h
  have hs5T : s5.mem.get 18 = 0 := by
    rw [hs5eq', Mem.get_set_eq, hs4T, hSK4, hDI]
    simp
  have hs5Z : s5.mem.get 0 = 0 := by
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - s4.mem.get 2320) (by decide)).trans hs4Z
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - s4.mem.get 2320) ha18).trans
      (hpres4 a ha18 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have g5 : ∀ k : Nat, 1692 ≤ k → k < 1695 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc1 := ed_enc_jlez_1692 (s := s5) hs5pc g5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj1 :=
    step_JLEZ (s := s5) (x := 18) (dest := 1698)
      hs5h hpc5 hs5Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = true := by
    have : le0 (s5.mem.get 18) = true := by rw [hs5T]; exact le0_zero
    simpa [le0] using this
  have hs6eq' : step s5 = { s5 with pc := 1698 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (1698 : Word) else s5.pc + 3) = (1698 : Word) := by
      simp [hle1]
    rw [hj1, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hs6pc : s6.pc = 1698 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5Z
  have hs6T : s6.mem.get 18 = 0 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5T
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq']; exact hpres5 a ha18 ha0
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have g6 : ∀ k : Nat, 1698 ≤ k → k < 1707 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hinc := ed_inc_T_1698 (s := s6) hs6pc hs6h hs6Z hONE6 g6
  have hrun9 : runN s 9 = runN s6 3 := runN_add_eq s 6 3 9 (by decide)
  let s9 := runN s 9
  have hs9eq : s9 = runN s6 3 := hrun9
  have hs9pc : s9.pc = 1707 := by rw [hs9eq]; exact hinc.1
  have hs9h : s9.halted = false := by rw [hs9eq]; exact hinc.2.1
  have hs9T : s9.mem.get 18 = 1 := by
    rw [hs9eq, hinc.2.2.1, hs6T]; exact (rfl : (0 : Word) + 1 = 1)
  have hs9Z : s9.mem.get 0 = 0 := by rw [hs9eq]; exact hinc.2.2.2.1
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs9eq]; exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have g9 : ∀ k : Nat, 1707 ≤ k → k < 1716 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc2 := ed_enc_jlez_1707 (s := s9) hs9pc
    (fun k h1 h2 => g9 k h1 (by omega))
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hj2 :=
    step_JLEZ (s := s9) (x := 18) (dest := 1713)
      hs9h hpc9 hs9Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = false := by
    have : le0 (s9.mem.get 18) = false := by
      rw [hs9T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs10eq' : step s9 = { s9 with pc := 1710 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18
          then (1713 : Word) else s9.pc + 3) = (1710 : Word) := by
      have hfall : s9.pc + 3 = (1710 : Word) := by simp [hs9pc]
      simp [hle2, hfall]
    rw [hj2, hif]
  have hrun10 : runN s 10 = step s9 := by
    have h10 : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact h10.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hs10pc : s10.pc = 1710 := by have : s10 = step s9 := hrun10; rw [this, hs10eq']
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq']; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by have : s10 = step s9 := hrun10; rw [this, hs10eq']; exact hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq']; exact hpres9 a ha18 ha0
  have g10 : ∀ k : Nat, 1710 ≤ k → k < 1716 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc3 := ed_enc_jmp_1710 (s := s10) hs10pc
    (fun k h1 h2 => g10 k h1 (by omega))
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hj3 := step_JMP (s := s10) (dest := 1716)
    hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2
  have hrun : s11 = step s10 := by
    have h11 : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact h11.trans (runN_one s10 hs10h hpc10)
  have hs11pc : s11.pc = 1716 := by rw [hrun, hj3]
  have hs11h : s11.halted = false := by rw [hrun, hj3]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by rw [hrun, hj3]; exact hs10Z
  have hs11DI : s11.mem.get 2321 = s.mem.get 2321 := by
    rw [hrun, hj3]; exact hpres10 2321 (by decide) (by decide)
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hj3]; exact hpres10 a ha18 ha0
  exact ⟨hs11pc, hs11h, hs11Z, hs11DI, hpres⟩

/-- `DIG_BODY` with `DI > SK` (both below the sign bit): 7 steps to `TAKE_DIG`. -/
theorem dig_body_take_gt {s : Machine}
    (hpc : s.pc = 1677)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hSKlo : (s.mem.get 2320).toNat < (s.mem.get 2321).toNat)
    (hDIhi : (s.mem.get 2321).toNat < 32768)
    (hcode : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s7 := runN s 7
    s7.pc = 1716 ∧
    s7.halted = false ∧
    s7.mem.get 0 = 0 ∧
    s7.mem.get 2321 = s.mem.get 2321 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a) := by
  intro s7
  have hm := ed_mov_DI_T_1677 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1689 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 2321 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hSK4 : s4.mem.get 2320 = s.mem.get 2320 := hpres4 2320 (by decide) (by decide)
  have g4 : ∀ k : Nat, 1689 ≤ k → k < 1698 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hsub := ed_sub_SK_T_1689 (s := s4) hs4pc hs4h
    (fun k h1 h2 => g4 k h1 (by omega))
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5eq' : s5 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - s4.mem.get 2320), pc := 1692 } := by
    have : s5 = step s4 := hrun5
    rw [this, hsub]
  have hs5pc : s5.pc = 1692 := by rw [hs5eq']
  have hs5h : s5.halted = false := by rw [hs5eq']; exact hs4h
  have hs5T : s5.mem.get 18 = s.mem.get 2321 - s.mem.get 2320 := by
    rw [hs5eq', Mem.get_set_eq, hs4T, hSK4]
  have hs5Z : s5.mem.get 0 = 0 := by
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - s4.mem.get 2320) (by decide)).trans hs4Z
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - s4.mem.get 2320) ha18).trans
      (hpres4 a ha18 ha0)
  have g5 : ∀ k : Nat, 1692 ≤ k → k < 1698 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc1 := ed_enc_jlez_1692 (s := s5) hs5pc
    (fun k h1 h2 => g5 k h1 (by omega))
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj1 :=
    step_JLEZ (s := s5) (x := 18) (dest := 1698)
      hs5h hpc5 hs5Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = false := by
    have htn := word_sub_ge (s.mem.get 2321) (s.mem.get 2320) (by omega)
    have hpos : 0 < (s.mem.get 2321 - s.mem.get 2320).toNat := by omega
    have hhi : (s.mem.get 2321 - s.mem.get 2320).toNat < 32768 := by omega
    have : le0 (s5.mem.get 18) = false := by
      rw [hs5T]; exact le0_pos hpos hhi
    simpa [le0] using this
  have hs6eq' : step s5 = { s5 with pc := 1695 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (1698 : Word) else s5.pc + 3) = (1695 : Word) := by
      have hfall : s5.pc + 3 = (1695 : Word) := by simp [hs5pc]
      simp [hle1, hfall]
    rw [hj1, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hs6pc : s6.pc = 1695 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq']; exact hpres5 a ha18 ha0
  have g6 : ∀ k : Nat, 1695 ≤ k → k < 1698 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc2 := ed_enc_jmp_1695 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hj2 := step_JMP (s := s6) (dest := 1716)
    hs6h hpc6 hs6Z henc2.1 henc2.2.1 henc2.2.2
  have hrun : s7 = step s6 := by
    have h7 : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact h7.trans (runN_one s6 hs6h hpc6)
  have hs7pc : s7.pc = 1716 := by rw [hrun, hj2]
  have hs7h : s7.halted = false := by rw [hrun, hj2]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by rw [hrun, hj2]; exact hs6Z
  have hs7DI : s7.mem.get 2321 = s.mem.get 2321 := by
    rw [hrun, hj2]; exact hpres6 2321 (by decide) (by decide)
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hj2]; exact hpres6 a ha18 ha0
  exact ⟨hs7pc, hs7h, hs7Z, hs7DI, hpres⟩

/-- `TAKE_DIG` with `DI = 0`: 10 steps to `HAVE_CH` with `CH = Q0`. -/
theorem take_dig_di0 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hDI : s.mem.get 2321 = 0)
    (hcode : ∀ k : Nat, 1716 ≤ k → k < 1824 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s10 := runN s 10
    s10.pc = 1824 ∧
    s10.halted = false ∧
    s10.mem.get 0 = 0 ∧
    s10.mem.get 30 = s.mem.get 20 ∧
    s10.mem.get 2321 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s10.mem.get a = s.mem.get a) := by
  intro s10
  have hm := ed_mov_DI_T_1716 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1728 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 0 := hm.2.2.1.trans hDI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hDI4 : s4.mem.get 2321 = 0 := (hpres4 2321 (by decide) (by decide)).trans hDI
  have hQ4 : s4.mem.get 20 = s.mem.get 20 := hpres4 20 (by decide) (by decide)
  have g4 : ∀ k : Nat, 1728 ≤ k → k < 1731 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := ed_enc_jlez_1728 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hj :=
    step_JLEZ (s := s4) (x := 18) (dest := 1752)
      hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = true := by
    have : le0 (s4.mem.get 18) = true := by rw [hs4T]; exact le0_zero
    simpa [le0] using this
  have hs5eq' : step s4 = { s4 with pc := 1752 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1752 : Word) else s4.pc + 3) = (1752 : Word) := by
      simp [hle]
    rw [hj, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1752 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4Z
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq']; exact hpres4 a ha18 ha0
  have hDI5 : s5.mem.get 2321 = 0 := (hpres5 2321 (by decide) (by decide)).trans hDI
  have hQ5 : s5.mem.get 20 = s.mem.get 20 := hpres5 20 (by decide) (by decide)
  have g5 : ∀ k : Nat, 1752 ≤ k → k < 1764 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hm2 := ed_mov_Q0_CH_1752 (s := s5) hs5pc hs5h hs5Z g5
  have hrun9 : runN s 9 = runN s5 4 := runN_add_eq s 5 4 9 (by decide)
  let s9 := runN s 9
  have hs9eq : s9 = runN s5 4 := hrun9
  have hs9pc : s9.pc = 1764 := by rw [hs9eq]; exact hm2.1
  have hs9h : s9.halted = false := by rw [hs9eq]; exact hm2.2.1
  have hs9CH : s9.mem.get 30 = s.mem.get 20 := by rw [hs9eq, hm2.2.2.1, hQ5]
  have hs9Z : s9.mem.get 0 = 0 := by rw [hs9eq]; exact hm2.2.2.2.1
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs9eq]
    exact (hm2.2.2.2.2.2 a ha30 ha0).trans (hpres5 a ha18 ha0)
  have hDI9 : s9.mem.get 2321 = 0 := (hpres9 2321 (by decide) (by decide) (by decide)).trans hDI
  have g9 : ∀ k : Nat, 1764 ≤ k → k < 1767 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hencj := ed_enc_jmp_1764 (s := s9) hs9pc g9
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hjmp := step_JMP (s := s9) (dest := 1824)
    hs9h hpc9 hs9Z hencj.1 hencj.2.1 hencj.2.2
  have hrun : s10 = step s9 := by
    have h10 : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact h10.trans (runN_one s9 hs9h hpc9)
  have hs10pc : s10.pc = 1824 := by rw [hrun, hjmp]
  have hs10h : s10.halted = false := by rw [hrun, hjmp]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs9Z
  have hs10CH : s10.mem.get 30 = s.mem.get 20 := by rw [hrun, hjmp]; exact hs9CH
  have hs10DI : s10.mem.get 2321 = 0 := by rw [hrun, hjmp]; exact hDI9
  have hpres : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hrun, hjmp]; exact hpres9 a ha18 ha30 ha0
  exact ⟨hs10pc, hs10h, hs10Z, hs10CH, hs10DI, hpres⟩

/-- `TAKE_DIG` with `DI = 1`: 12 steps to `HAVE_CH` with `CH = Q1`. -/
theorem take_dig_di1 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 1)
    (hcode : ∀ k : Nat, 1716 ≤ k → k < 1824 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s12 := runN s 12
    s12.pc = 1824 ∧
    s12.halted = false ∧
    s12.mem.get 0 = 0 ∧
    s12.mem.get 30 = s.mem.get 21 ∧
    s12.mem.get 2321 = 1 ∧
    (∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s12.mem.get a = s.mem.get a) := by
  intro s12
  have hm := ed_mov_DI_T_1716 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1728 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 1 := hm.2.2.1.trans hDI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hQ : s4.mem.get 21 = s.mem.get 21 := hpres4 21 (by decide) (by decide)
  have g4 : ∀ k : Nat, 1728 ≤ k → k < 1731 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc0 := ed_enc_jlez_1728 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hj0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1752)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq' : step s4 = { s4 with pc := 1731 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1752 : Word) else s4.pc + 3) = (1731 : Word) := by
      have hfall : s4.pc + 3 = (1731 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hj0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1731 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4Z
  have hs5T : s5.mem.get 18 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4T
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq']; exact hpres4 a ha18 ha0
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hQ5 : s5.mem.get 21 = s.mem.get 21 := hpres5 21 (by decide) (by decide)
  have gdec : ∀ k : Nat, 1731 ≤ k → k < 1734 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hdec := ed_dec_T_1731 (s := s5) hs5pc hs5h gdec
  have hrun6 : runN s 6 = step s5 := by
    have hx : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    have hpcx : s5.pc.toNat < 32768 := by simp [hs5pc]
    exact hx.trans (runN_one s5 hs5h hpcx)
  let s6 := runN s 6
  have hs6eq' : s6 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1734 } := by
    have : s6 = step s5 := hrun6
    rw [this, hdec]
  have hs6pc : s6.pc = 1734 := by rw [hs6eq']
  have hs6h : s6.halted = false := by rw [hs6eq']; exact hs5h
  have hs6T : s6.mem.get 18 = 0 := by
    rw [hs6eq', Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (1 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hs6Z : s6.mem.get 0 = 0 := by
    rw [hs6eq']
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs6eq']
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have hQ6 : s6.mem.get 21 = s.mem.get 21 := hpres6 21 (by decide) (by decide)
  have gjlez : ∀ k : Nat, 1734 ≤ k → k < 1734+3 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := ed_enc_jlez_1734 (s := s6) hs6pc gjlez
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hj :=
    step_JLEZ (s := s6) (x := 18) (dest := 1767)
      hs6h hpc6 hs6Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = true := by
    have : le0 (s6.mem.get 18) = true := by rw [hs6T]; exact le0_zero
    simpa [le0] using this
  have hs7eq' : step s6 = { s6 with pc := 1767 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1767 : Word) else s6.pc + 3) = (1767 : Word) := by
      simp [hle]
    rw [hj, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hx : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hx.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1767 := by have : s7 = step s6 := hrun7; rw [this, hs7eq']
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq']; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq']; exact hs6Z
  have hs7T : s7.mem.get 18 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq']; exact hs6T
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq']; exact hpres6 a ha18 ha0
  have hONE7 : s7.mem.get 3 = 1 := (hpres7 3 (by decide) (by decide)).trans hONE
  have hQ7 : s7.mem.get 21 = s.mem.get 21 := hpres7 21 (by decide) (by decide)
  have gmov : ∀ k : Nat, 1767 ≤ k → k < 1779 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres7 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hm2 := ed_mov_Q1_CH_1767 (s := s7) hs7pc hs7h hs7Z gmov
  have hrun11 : runN s 11 = runN s7 4 := runN_add_eq s 7 4 11 (by decide)
  let s11 := runN s 11
  have hs11eq : s11 = runN s7 4 := hrun11
  have hs11pc : s11.pc = 1779 := by rw [hs11eq]; exact hm2.1
  have hs11h : s11.halted = false := by rw [hs11eq]; exact hm2.2.1
  have hs11CH : s11.mem.get 30 = s.mem.get 21 := by
    rw [hs11eq, hm2.2.2.1, hQ7]
  have hs11Z : s11.mem.get 0 = 0 := by rw [hs11eq]; exact hm2.2.2.2.1
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs11eq]
    exact (hm2.2.2.2.2.2 a ha30 ha0).trans (hpres7 a ha18 ha0)
  have hDI11 : s11.mem.get 2321 = 1 :=
    (hpres11 2321 (by decide) (by decide) (by decide)).trans hDI
  have gjmp : ∀ k : Nat, 1779 ≤ k → k < 1779+3 →
      s11.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres11 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hencj := ed_enc_jmp_1779 (s := s11) hs11pc gjmp
  have hpc11 : s11.pc.toNat < 32768 := by simp [hs11pc]
  have hjmp := step_JMP (s := s11) (dest := 1824)
    hs11h hpc11 hs11Z hencj.1 hencj.2.1 hencj.2.2
  have hrun : s12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
  have hs12eq : s12 = step s11 := hrun.trans (runN_one s11 hs11h hpc11)
  have hs12pc : s12.pc = 1824 := by rw [hs12eq, hjmp]
  have hs12h : s12.halted = false := by rw [hs12eq, hjmp]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by rw [hs12eq, hjmp]; exact hs11Z
  have hs12CH : s12.mem.get 30 = s.mem.get 21 := by rw [hs12eq, hjmp]; exact hs11CH
  have hs12DI : s12.mem.get 2321 = 1 := by rw [hs12eq, hjmp]; exact hDI11
  have hpres : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs12eq, hjmp]; exact hpres11 a ha18 ha30 ha0
  exact ⟨hs12pc, hs12h, hs12Z, hs12CH, hs12DI, hpres⟩


/-- `TAKE_DIG` with `DI = 2`: 14 steps to `HAVE_CH` with `CH = Q2`. -/
theorem take_dig_di2 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 2)
    (hcode : ∀ k : Nat, 1716 ≤ k → k < 1824 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s14 := runN s 14
    s14.pc = 1824 ∧
    s14.halted = false ∧
    s14.mem.get 0 = 0 ∧
    s14.mem.get 30 = s.mem.get 22 ∧
    s14.mem.get 2321 = 2 ∧
    (∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s14.mem.get a = s.mem.get a) := by
  intro s14
  have hm := ed_mov_DI_T_1716 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1728 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 2 := hm.2.2.1.trans hDI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hQ : s4.mem.get 22 = s.mem.get 22 := hpres4 22 (by decide) (by decide)
  have g4 : ∀ k : Nat, 1728 ≤ k → k < 1731 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc0 := ed_enc_jlez_1728 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hj0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1752)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq' : step s4 = { s4 with pc := 1731 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1752 : Word) else s4.pc + 3) = (1731 : Word) := by
      have hfall : s4.pc + 3 = (1731 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hj0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1731 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4Z
  have hs5T : s5.mem.get 18 = 2 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4T
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq']; exact hpres4 a ha18 ha0
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hQ5 : s5.mem.get 22 = s.mem.get 22 := hpres5 22 (by decide) (by decide)
  have gdec : ∀ k : Nat, 1731 ≤ k → k < 1734 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hdec := ed_dec_T_1731 (s := s5) hs5pc hs5h gdec
  have hrun6 : runN s 6 = step s5 := by
    have hx : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    have hpcx : s5.pc.toNat < 32768 := by simp [hs5pc]
    exact hx.trans (runN_one s5 hs5h hpcx)
  let s6 := runN s 6
  have hs6eq' : s6 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1734 } := by
    have : s6 = step s5 := hrun6
    rw [this, hdec]
  have hs6pc : s6.pc = 1734 := by rw [hs6eq']
  have hs6h : s6.halted = false := by rw [hs6eq']; exact hs5h
  have hs6T : s6.mem.get 18 = 1 := by
    rw [hs6eq', Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (2 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hs6Z : s6.mem.get 0 = 0 := by
    rw [hs6eq']
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs6eq']
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have hQ6 : s6.mem.get 22 = s.mem.get 22 := hpres6 22 (by decide) (by decide)
  have gjlez : ∀ k : Nat, 1734 ≤ k → k < 1734+3 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := ed_enc_jlez_1734 (s := s6) hs6pc gjlez
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hj :=
    step_JLEZ (s := s6) (x := 18) (dest := 1767)
      hs6h hpc6 hs6Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq' : step s6 = { s6 with pc := 1737 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1767 : Word) else s6.pc + 3) = (1737 : Word) := by
      have hfall : s6.pc + 3 = (1737 : Word) := by simp [hs6pc]
      simp [hle, hfall]
    rw [hj, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hx : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hx.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1737 := by have : s7 = step s6 := hrun7; rw [this, hs7eq']
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq']; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq']; exact hs6Z
  have hs7T : s7.mem.get 18 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq']; exact hs6T
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq']; exact hpres6 a ha18 ha0
  have hONE7 : s7.mem.get 3 = 1 := (hpres7 3 (by decide) (by decide)).trans hONE
  have hQ7 : s7.mem.get 22 = s.mem.get 22 := hpres7 22 (by decide) (by decide)
  have gdec : ∀ k : Nat, 1737 ≤ k → k < 1740 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres7 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hdec := ed_dec_T_1737 (s := s7) hs7pc hs7h gdec
  have hrun8 : runN s 8 = step s7 := by
    have hx : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    have hpcx : s7.pc.toNat < 32768 := by simp [hs7pc]
    exact hx.trans (runN_one s7 hs7h hpcx)
  let s8 := runN s 8
  have hs8eq' : s8 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1740 } := by
    have : s8 = step s7 := hrun8
    rw [this, hdec]
  have hs8pc : s8.pc = 1740 := by rw [hs8eq']
  have hs8h : s8.halted = false := by rw [hs8eq']; exact hs7h
  have hs8T : s8.mem.get 18 = 0 := by
    rw [hs8eq', Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (1 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hs8Z : s8.mem.get 0 = 0 := by
    rw [hs8eq']
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs8eq']
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have hONE8 : s8.mem.get 3 = 1 := (hpres8 3 (by decide) (by decide)).trans hONE
  have hQ8 : s8.mem.get 22 = s.mem.get 22 := hpres8 22 (by decide) (by decide)
  have gjlez : ∀ k : Nat, 1740 ≤ k → k < 1740+3 →
      s8.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres8 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := ed_enc_jlez_1740 (s := s8) hs8pc gjlez
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hj :=
    step_JLEZ (s := s8) (x := 18) (dest := 1782)
      hs8h hpc8 hs8Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = true := by
    have : le0 (s8.mem.get 18) = true := by rw [hs8T]; exact le0_zero
    simpa [le0] using this
  have hs9eq' : step s8 = { s8 with pc := 1782 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1782 : Word) else s8.pc + 3) = (1782 : Word) := by
      simp [hle]
    rw [hj, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hx : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hx.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1782 := by have : s9 = step s8 := hrun9; rw [this, hs9eq']
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq']; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq']; exact hs8Z
  have hs9T : s9.mem.get 18 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq']; exact hs8T
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq']; exact hpres8 a ha18 ha0
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide)).trans hONE
  have hQ9 : s9.mem.get 22 = s.mem.get 22 := hpres9 22 (by decide) (by decide)
  have gmov : ∀ k : Nat, 1782 ≤ k → k < 1794 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hm2 := ed_mov_Q2_CH_1782 (s := s9) hs9pc hs9h hs9Z gmov
  have hrun13 : runN s 13 = runN s9 4 := runN_add_eq s 9 4 13 (by decide)
  let s13 := runN s 13
  have hs13eq : s13 = runN s9 4 := hrun13
  have hs13pc : s13.pc = 1794 := by rw [hs13eq]; exact hm2.1
  have hs13h : s13.halted = false := by rw [hs13eq]; exact hm2.2.1
  have hs13CH : s13.mem.get 30 = s.mem.get 22 := by
    rw [hs13eq, hm2.2.2.1, hQ9]
  have hs13Z : s13.mem.get 0 = 0 := by rw [hs13eq]; exact hm2.2.2.2.1
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs13eq]
    exact (hm2.2.2.2.2.2 a ha30 ha0).trans (hpres9 a ha18 ha0)
  have hDI13 : s13.mem.get 2321 = 2 :=
    (hpres13 2321 (by decide) (by decide) (by decide)).trans hDI
  have gjmp : ∀ k : Nat, 1794 ≤ k → k < 1794+3 →
      s13.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres13 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hencj := ed_enc_jmp_1794 (s := s13) hs13pc gjmp
  have hpc13 : s13.pc.toNat < 32768 := by simp [hs13pc]
  have hjmp := step_JMP (s := s13) (dest := 1824)
    hs13h hpc13 hs13Z hencj.1 hencj.2.1 hencj.2.2
  have hrun : s14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
  have hs14eq : s14 = step s13 := hrun.trans (runN_one s13 hs13h hpc13)
  have hs14pc : s14.pc = 1824 := by rw [hs14eq, hjmp]
  have hs14h : s14.halted = false := by rw [hs14eq, hjmp]; exact hs13h
  have hs14Z : s14.mem.get 0 = 0 := by rw [hs14eq, hjmp]; exact hs13Z
  have hs14CH : s14.mem.get 30 = s.mem.get 22 := by rw [hs14eq, hjmp]; exact hs13CH
  have hs14DI : s14.mem.get 2321 = 2 := by rw [hs14eq, hjmp]; exact hDI13
  have hpres : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs14eq, hjmp]; exact hpres13 a ha18 ha30 ha0
  exact ⟨hs14pc, hs14h, hs14Z, hs14CH, hs14DI, hpres⟩


/-- `TAKE_DIG` with `DI = 3`: 16 steps to `HAVE_CH` with `CH = Q3`. -/
theorem take_dig_di3 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 3)
    (hcode : ∀ k : Nat, 1716 ≤ k → k < 1824 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s16 := runN s 16
    s16.pc = 1824 ∧
    s16.halted = false ∧
    s16.mem.get 0 = 0 ∧
    s16.mem.get 30 = s.mem.get 23 ∧
    s16.mem.get 2321 = 3 ∧
    (∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s16.mem.get a = s.mem.get a) := by
  intro s16
  have hm := ed_mov_DI_T_1716 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1728 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 3 := hm.2.2.1.trans hDI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hQ : s4.mem.get 23 = s.mem.get 23 := hpres4 23 (by decide) (by decide)
  have g4 : ∀ k : Nat, 1728 ≤ k → k < 1731 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc0 := ed_enc_jlez_1728 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hj0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1752)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq' : step s4 = { s4 with pc := 1731 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1752 : Word) else s4.pc + 3) = (1731 : Word) := by
      have hfall : s4.pc + 3 = (1731 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hj0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1731 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4Z
  have hs5T : s5.mem.get 18 = 3 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4T
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq']; exact hpres4 a ha18 ha0
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hQ5 : s5.mem.get 23 = s.mem.get 23 := hpres5 23 (by decide) (by decide)
  have gdec : ∀ k : Nat, 1731 ≤ k → k < 1734 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hdec := ed_dec_T_1731 (s := s5) hs5pc hs5h gdec
  have hrun6 : runN s 6 = step s5 := by
    have hx : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    have hpcx : s5.pc.toNat < 32768 := by simp [hs5pc]
    exact hx.trans (runN_one s5 hs5h hpcx)
  let s6 := runN s 6
  have hs6eq' : s6 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1734 } := by
    have : s6 = step s5 := hrun6
    rw [this, hdec]
  have hs6pc : s6.pc = 1734 := by rw [hs6eq']
  have hs6h : s6.halted = false := by rw [hs6eq']; exact hs5h
  have hs6T : s6.mem.get 18 = 2 := by
    rw [hs6eq', Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (3 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hs6Z : s6.mem.get 0 = 0 := by
    rw [hs6eq']
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs6eq']
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have hQ6 : s6.mem.get 23 = s.mem.get 23 := hpres6 23 (by decide) (by decide)
  have gjlez : ∀ k : Nat, 1734 ≤ k → k < 1734+3 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := ed_enc_jlez_1734 (s := s6) hs6pc gjlez
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hj :=
    step_JLEZ (s := s6) (x := 18) (dest := 1767)
      hs6h hpc6 hs6Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq' : step s6 = { s6 with pc := 1737 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1767 : Word) else s6.pc + 3) = (1737 : Word) := by
      have hfall : s6.pc + 3 = (1737 : Word) := by simp [hs6pc]
      simp [hle, hfall]
    rw [hj, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hx : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hx.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1737 := by have : s7 = step s6 := hrun7; rw [this, hs7eq']
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq']; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq']; exact hs6Z
  have hs7T : s7.mem.get 18 = 2 := by have : s7 = step s6 := hrun7; rw [this, hs7eq']; exact hs6T
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq']; exact hpres6 a ha18 ha0
  have hONE7 : s7.mem.get 3 = 1 := (hpres7 3 (by decide) (by decide)).trans hONE
  have hQ7 : s7.mem.get 23 = s.mem.get 23 := hpres7 23 (by decide) (by decide)
  have gdec : ∀ k : Nat, 1737 ≤ k → k < 1740 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres7 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hdec := ed_dec_T_1737 (s := s7) hs7pc hs7h gdec
  have hrun8 : runN s 8 = step s7 := by
    have hx : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    have hpcx : s7.pc.toNat < 32768 := by simp [hs7pc]
    exact hx.trans (runN_one s7 hs7h hpcx)
  let s8 := runN s 8
  have hs8eq' : s8 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1740 } := by
    have : s8 = step s7 := hrun8
    rw [this, hdec]
  have hs8pc : s8.pc = 1740 := by rw [hs8eq']
  have hs8h : s8.halted = false := by rw [hs8eq']; exact hs7h
  have hs8T : s8.mem.get 18 = 1 := by
    rw [hs8eq', Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (2 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hs8Z : s8.mem.get 0 = 0 := by
    rw [hs8eq']
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs8eq']
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have hONE8 : s8.mem.get 3 = 1 := (hpres8 3 (by decide) (by decide)).trans hONE
  have hQ8 : s8.mem.get 23 = s.mem.get 23 := hpres8 23 (by decide) (by decide)
  have gjlez : ∀ k : Nat, 1740 ≤ k → k < 1740+3 →
      s8.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres8 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := ed_enc_jlez_1740 (s := s8) hs8pc gjlez
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hj :=
    step_JLEZ (s := s8) (x := 18) (dest := 1782)
      hs8h hpc8 hs8Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq' : step s8 = { s8 with pc := 1743 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1782 : Word) else s8.pc + 3) = (1743 : Word) := by
      have hfall : s8.pc + 3 = (1743 : Word) := by simp [hs8pc]
      simp [hle, hfall]
    rw [hj, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hx : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hx.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1743 := by have : s9 = step s8 := hrun9; rw [this, hs9eq']
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq']; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq']; exact hs8Z
  have hs9T : s9.mem.get 18 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq']; exact hs8T
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq']; exact hpres8 a ha18 ha0
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide)).trans hONE
  have hQ9 : s9.mem.get 23 = s.mem.get 23 := hpres9 23 (by decide) (by decide)
  have gdec : ∀ k : Nat, 1743 ≤ k → k < 1746 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hdec := ed_dec_T_1743 (s := s9) hs9pc hs9h gdec
  have hrun10 : runN s 10 = step s9 := by
    have hx : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    have hpcx : s9.pc.toNat < 32768 := by simp [hs9pc]
    exact hx.trans (runN_one s9 hs9h hpcx)
  let s10 := runN s 10
  have hs10eq' : s10 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1746 } := by
    have : s10 = step s9 := hrun10
    rw [this, hdec]
  have hs10pc : s10.pc = 1746 := by rw [hs10eq']
  have hs10h : s10.halted = false := by rw [hs10eq']; exact hs9h
  have hs10T : s10.mem.get 18 = 0 := by
    rw [hs10eq', Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (1 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hs10Z : s10.mem.get 0 = 0 := by
    rw [hs10eq']
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs10eq']
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hQ10 : s10.mem.get 23 = s.mem.get 23 := hpres10 23 (by decide) (by decide)
  have gjlez : ∀ k : Nat, 1746 ≤ k → k < 1746+3 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := ed_enc_jlez_1746 (s := s10) hs10pc gjlez
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hj :=
    step_JLEZ (s := s10) (x := 18) (dest := 1797)
      hs10h hpc10 hs10Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = true := by
    have : le0 (s10.mem.get 18) = true := by rw [hs10T]; exact le0_zero
    simpa [le0] using this
  have hs11eq' : step s10 = { s10 with pc := 1797 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1797 : Word) else s10.pc + 3) = (1797 : Word) := by
      simp [hle]
    rw [hj, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hx : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hx.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1797 := by have : s11 = step s10 := hrun11; rw [this, hs11eq']
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq']; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq']; exact hs10Z
  have hs11T : s11.mem.get 18 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq']; exact hs10T
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq']; exact hpres10 a ha18 ha0
  have hONE11 : s11.mem.get 3 = 1 := (hpres11 3 (by decide) (by decide)).trans hONE
  have hQ11 : s11.mem.get 23 = s.mem.get 23 := hpres11 23 (by decide) (by decide)
  have gmov : ∀ k : Nat, 1797 ≤ k → k < 1809 →
      s11.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres11 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hm2 := ed_mov_Q3_CH_1797 (s := s11) hs11pc hs11h hs11Z gmov
  have hrun15 : runN s 15 = runN s11 4 := runN_add_eq s 11 4 15 (by decide)
  let s15 := runN s 15
  have hs15eq : s15 = runN s11 4 := hrun15
  have hs15pc : s15.pc = 1809 := by rw [hs15eq]; exact hm2.1
  have hs15h : s15.halted = false := by rw [hs15eq]; exact hm2.2.1
  have hs15CH : s15.mem.get 30 = s.mem.get 23 := by
    rw [hs15eq, hm2.2.2.1, hQ11]
  have hs15Z : s15.mem.get 0 = 0 := by rw [hs15eq]; exact hm2.2.2.2.1
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs15eq]
    exact (hm2.2.2.2.2.2 a ha30 ha0).trans (hpres11 a ha18 ha0)
  have hDI15 : s15.mem.get 2321 = 3 :=
    (hpres15 2321 (by decide) (by decide) (by decide)).trans hDI
  have gjmp : ∀ k : Nat, 1809 ≤ k → k < 1809+3 →
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres15 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hencj := ed_enc_jmp_1809 (s := s15) hs15pc gjmp
  have hpc15 : s15.pc.toNat < 32768 := by simp [hs15pc]
  have hjmp := step_JMP (s := s15) (dest := 1824)
    hs15h hpc15 hs15Z hencj.1 hencj.2.1 hencj.2.2
  have hrun : s16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
  have hs16eq : s16 = step s15 := hrun.trans (runN_one s15 hs15h hpc15)
  have hs16pc : s16.pc = 1824 := by rw [hs16eq, hjmp]
  have hs16h : s16.halted = false := by rw [hs16eq, hjmp]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by rw [hs16eq, hjmp]; exact hs15Z
  have hs16CH : s16.mem.get 30 = s.mem.get 23 := by rw [hs16eq, hjmp]; exact hs15CH
  have hs16DI : s16.mem.get 2321 = 3 := by rw [hs16eq, hjmp]; exact hDI15
  have hpres : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs16eq, hjmp]; exact hpres15 a ha18 ha30 ha0
  exact ⟨hs16pc, hs16h, hs16Z, hs16CH, hs16DI, hpres⟩


/-- `TAKE_DIG` with `DI = 4`: 16 steps to `HAVE_CH` with `CH = Q4`. -/
theorem take_dig_di4 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 4)
    (hcode : ∀ k : Nat, 1716 ≤ k → k < 1824 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s16 := runN s 16
    s16.pc = 1824 ∧
    s16.halted = false ∧
    s16.mem.get 0 = 0 ∧
    s16.mem.get 30 = s.mem.get 24 ∧
    s16.mem.get 2321 = 4 ∧
    (∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s16.mem.get a = s.mem.get a) := by
  intro s16
  have hm := ed_mov_DI_T_1716 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1728 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 4 := hm.2.2.1.trans hDI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hQ : s4.mem.get 24 = s.mem.get 24 := hpres4 24 (by decide) (by decide)
  have g4 : ∀ k : Nat, 1728 ≤ k → k < 1731 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc0 := ed_enc_jlez_1728 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hj0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1752)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq' : step s4 = { s4 with pc := 1731 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1752 : Word) else s4.pc + 3) = (1731 : Word) := by
      have hfall : s4.pc + 3 = (1731 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hj0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1731 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4Z
  have hs5T : s5.mem.get 18 = 4 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4T
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq']; exact hpres4 a ha18 ha0
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hQ5 : s5.mem.get 24 = s.mem.get 24 := hpres5 24 (by decide) (by decide)
  have gdec : ∀ k : Nat, 1731 ≤ k → k < 1734 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hdec := ed_dec_T_1731 (s := s5) hs5pc hs5h gdec
  have hrun6 : runN s 6 = step s5 := by
    have hx : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    have hpcx : s5.pc.toNat < 32768 := by simp [hs5pc]
    exact hx.trans (runN_one s5 hs5h hpcx)
  let s6 := runN s 6
  have hs6eq' : s6 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1734 } := by
    have : s6 = step s5 := hrun6
    rw [this, hdec]
  have hs6pc : s6.pc = 1734 := by rw [hs6eq']
  have hs6h : s6.halted = false := by rw [hs6eq']; exact hs5h
  have hs6T : s6.mem.get 18 = 3 := by
    rw [hs6eq', Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (4 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (4 : Word) - 1 = 3)
  have hs6Z : s6.mem.get 0 = 0 := by
    rw [hs6eq']
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs6eq']
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have hQ6 : s6.mem.get 24 = s.mem.get 24 := hpres6 24 (by decide) (by decide)
  have gjlez : ∀ k : Nat, 1734 ≤ k → k < 1734+3 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := ed_enc_jlez_1734 (s := s6) hs6pc gjlez
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hj :=
    step_JLEZ (s := s6) (x := 18) (dest := 1767)
      hs6h hpc6 hs6Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq' : step s6 = { s6 with pc := 1737 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1767 : Word) else s6.pc + 3) = (1737 : Word) := by
      have hfall : s6.pc + 3 = (1737 : Word) := by simp [hs6pc]
      simp [hle, hfall]
    rw [hj, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hx : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hx.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1737 := by have : s7 = step s6 := hrun7; rw [this, hs7eq']
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq']; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq']; exact hs6Z
  have hs7T : s7.mem.get 18 = 3 := by have : s7 = step s6 := hrun7; rw [this, hs7eq']; exact hs6T
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq']; exact hpres6 a ha18 ha0
  have hONE7 : s7.mem.get 3 = 1 := (hpres7 3 (by decide) (by decide)).trans hONE
  have hQ7 : s7.mem.get 24 = s.mem.get 24 := hpres7 24 (by decide) (by decide)
  have gdec : ∀ k : Nat, 1737 ≤ k → k < 1740 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres7 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hdec := ed_dec_T_1737 (s := s7) hs7pc hs7h gdec
  have hrun8 : runN s 8 = step s7 := by
    have hx : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    have hpcx : s7.pc.toNat < 32768 := by simp [hs7pc]
    exact hx.trans (runN_one s7 hs7h hpcx)
  let s8 := runN s 8
  have hs8eq' : s8 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1740 } := by
    have : s8 = step s7 := hrun8
    rw [this, hdec]
  have hs8pc : s8.pc = 1740 := by rw [hs8eq']
  have hs8h : s8.halted = false := by rw [hs8eq']; exact hs7h
  have hs8T : s8.mem.get 18 = 2 := by
    rw [hs8eq', Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (3 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hs8Z : s8.mem.get 0 = 0 := by
    rw [hs8eq']
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs8eq']
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have hONE8 : s8.mem.get 3 = 1 := (hpres8 3 (by decide) (by decide)).trans hONE
  have hQ8 : s8.mem.get 24 = s.mem.get 24 := hpres8 24 (by decide) (by decide)
  have gjlez : ∀ k : Nat, 1740 ≤ k → k < 1740+3 →
      s8.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres8 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := ed_enc_jlez_1740 (s := s8) hs8pc gjlez
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hj :=
    step_JLEZ (s := s8) (x := 18) (dest := 1782)
      hs8h hpc8 hs8Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq' : step s8 = { s8 with pc := 1743 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1782 : Word) else s8.pc + 3) = (1743 : Word) := by
      have hfall : s8.pc + 3 = (1743 : Word) := by simp [hs8pc]
      simp [hle, hfall]
    rw [hj, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hx : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hx.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1743 := by have : s9 = step s8 := hrun9; rw [this, hs9eq']
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq']; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq']; exact hs8Z
  have hs9T : s9.mem.get 18 = 2 := by have : s9 = step s8 := hrun9; rw [this, hs9eq']; exact hs8T
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq']; exact hpres8 a ha18 ha0
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide)).trans hONE
  have hQ9 : s9.mem.get 24 = s.mem.get 24 := hpres9 24 (by decide) (by decide)
  have gdec : ∀ k : Nat, 1743 ≤ k → k < 1746 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hdec := ed_dec_T_1743 (s := s9) hs9pc hs9h gdec
  have hrun10 : runN s 10 = step s9 := by
    have hx : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    have hpcx : s9.pc.toNat < 32768 := by simp [hs9pc]
    exact hx.trans (runN_one s9 hs9h hpcx)
  let s10 := runN s 10
  have hs10eq' : s10 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1746 } := by
    have : s10 = step s9 := hrun10
    rw [this, hdec]
  have hs10pc : s10.pc = 1746 := by rw [hs10eq']
  have hs10h : s10.halted = false := by rw [hs10eq']; exact hs9h
  have hs10T : s10.mem.get 18 = 1 := by
    rw [hs10eq', Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (2 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hs10Z : s10.mem.get 0 = 0 := by
    rw [hs10eq']
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs10eq']
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hQ10 : s10.mem.get 24 = s.mem.get 24 := hpres10 24 (by decide) (by decide)
  have gjlez : ∀ k : Nat, 1746 ≤ k → k < 1746+3 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := ed_enc_jlez_1746 (s := s10) hs10pc gjlez
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hj :=
    step_JLEZ (s := s10) (x := 18) (dest := 1797)
      hs10h hpc10 hs10Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = false := by
    have : le0 (s10.mem.get 18) = false := by
      rw [hs10T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq' : step s10 = { s10 with pc := 1749 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1797 : Word) else s10.pc + 3) = (1749 : Word) := by
      have hfall : s10.pc + 3 = (1749 : Word) := by simp [hs10pc]
      simp [hle, hfall]
    rw [hj, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hx : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hx.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1749 := by have : s11 = step s10 := hrun11; rw [this, hs11eq']
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq']; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq']; exact hs10Z
  have hs11T : s11.mem.get 18 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq']; exact hs10T
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq']; exact hpres10 a ha18 ha0
  have hONE11 : s11.mem.get 3 = 1 := (hpres11 3 (by decide) (by decide)).trans hONE
  have hQ11 : s11.mem.get 24 = s.mem.get 24 := hpres11 24 (by decide) (by decide)
  have gjmp4 : ∀ k : Nat, 1749 ≤ k → k < 1752 →
      s11.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres11 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc4 := ed_enc_jmp_1749 (s := s11) hs11pc gjmp4
  have hpc11 : s11.pc.toNat < 32768 := by simp [hs11pc]
  have hj4 := step_JMP (s := s11) (dest := 1812)
    hs11h hpc11 hs11Z henc4.1 henc4.2.1 henc4.2.2
  have hrun12 : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
  let s12 := runN s 12
  have hs12eq : s12 = step s11 := hrun12.trans (runN_one s11 hs11h hpc11)
  have hs12pc : s12.pc = 1812 := by rw [hs12eq, hj4]
  have hs12h : s12.halted = false := by rw [hs12eq, hj4]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by rw [hs12eq, hj4]; exact hs11Z
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs12eq, hj4]; exact hpres11 a ha18 ha0
  have hQ12 : s12.mem.get 24 = s.mem.get 24 := hpres12 24 (by decide) (by decide)
  have gmov : ∀ k : Nat, 1812 ≤ k → k < 1824 →
      s12.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres12 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hm2 := ed_mov_Q4_CH_1812 (s := s12) hs12pc hs12h hs12Z gmov
  have hrun : s16 = runN s12 4 := runN_add_eq s 12 4 16 (by decide)
  have hs16pc : s16.pc = 1824 := by rw [hrun]; exact hm2.1
  have hs16h : s16.halted = false := by rw [hrun]; exact hm2.2.1
  have hs16CH : s16.mem.get 30 = s.mem.get 24 := by
    rw [hrun, hm2.2.2.1, hQ12]
  have hs16Z : s16.mem.get 0 = 0 := by rw [hrun]; exact hm2.2.2.2.1
  have hpres : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hrun]
    exact (hm2.2.2.2.2.2 a ha30 ha0).trans (hpres12 a ha18 ha0)
  have hs16DI : s16.mem.get 2321 = 4 :=
    (hpres 2321 (by decide) (by decide) (by decide)).trans hDI
  exact ⟨hs16pc, hs16h, hs16Z, hs16CH, hs16DI, hpres⟩

/-- `HAVE_CH` with `IDX < ROOM`: 21 steps to `STORE_CH` with `RETID = 3`. -/
theorem have_ch_to_store {s : Machine}
    (hpc : s.pc = 1824)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hIlt : (s.mem.get 29).toNat < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s21 := runN s 21
    s21.pc = 1185 ∧
    s21.halted = false ∧
    s21.mem.get 0 = 0 ∧
    s21.mem.get 2319 = 3 ∧
    s21.mem.get 29 = s.mem.get 29 ∧
    s21.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 18 → a ≠ 2319 → a ≠ 0 → s21.mem.get a = s.mem.get a) := by
  intro s21
  have hm := ed_mov_IDX_T_1824 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1836 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 29 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hI4 : s4.mem.get 29 = s.mem.get 29 := hpres4 29 (by decide) (by decide)
  have hR4 : s4.mem.get 28 = s.mem.get 28 := hpres4 28 (by decide) (by decide)
  have g4 : ∀ k : Nat, 1836 ≤ k → k < 1842 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hsub := ed_sub_ROOM_T_1836 (s := s4) hs4pc hs4h
    (fun k h1 h2 => g4 k h1 (by omega))
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5eq' : s5 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - s4.mem.get 28), pc := 1839 } := by
    have : s5 = step s4 := hrun5
    rw [this, hsub]
  have hs5pc : s5.pc = 1839 := by rw [hs5eq']
  have hs5h : s5.halted = false := by rw [hs5eq']; exact hs4h
  have hs5T : s5.mem.get 18 = s.mem.get 29 - s.mem.get 28 := by
    rw [hs5eq', Mem.get_set_eq, hs4T, hR4]
  have hs5Z : s5.mem.get 0 = 0 := by
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - s4.mem.get 28) (by decide)).trans hs4Z
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - s4.mem.get 28) ha18).trans
      (hpres4 a ha18 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have g5 : ∀ k : Nat, 1839 ≤ k → k < 1842 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc1 := ed_enc_jlez_1839 (s := s5) hs5pc g5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj1 :=
    step_JLEZ (s := s5) (x := 18) (dest := 1845)
      hs5h hpc5 hs5Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = true := by
    have : le0 (s5.mem.get 18) = true := by
      rw [hs5T]; exact idx_lt_room_le0 (s.mem.get 29) (s.mem.get 28) hRhi hIlt
    simpa [le0] using this
  have hs6eq' : step s5 = { s5 with pc := 1845 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (1845 : Word) else s5.pc + 3) = (1845 : Word) := by
      simp [hle1]
    rw [hj1, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hs6pc : s6.pc = 1845 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5Z
  have hs6T : s6.mem.get 18 = s.mem.get 29 - s.mem.get 28 := by
    have : s6 = step s5 := hrun6; rw [this, hs6eq']; exact hs5T
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq']; exact hpres5 a ha18 ha0
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have g6 : ∀ k : Nat, 1845 ≤ k → k < 1854 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hinc := ed_inc_T_1845 (s := s6) hs6pc hs6h hs6Z hONE6 g6
  have hrun9 : runN s 9 = runN s6 3 := runN_add_eq s 6 3 9 (by decide)
  let s9 := runN s 9
  have hs9eq : s9 = runN s6 3 := hrun9
  have hs9pc : s9.pc = 1854 := by rw [hs9eq]; exact hinc.1
  have hs9h : s9.halted = false := by rw [hs9eq]; exact hinc.2.1
  have hs9T : s9.mem.get 18 = (s.mem.get 29 - s.mem.get 28) + 1 := by
    rw [hs9eq, hinc.2.2.1, hs6T]
  have hs9Z : s9.mem.get 0 = 0 := by rw [hs9eq]; exact hinc.2.2.2.1
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs9eq]; exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide)).trans hONE
  have g9 : ∀ k : Nat, 1854 ≤ k → k < 1857 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc2 := ed_enc_jlez_1854 (s := s9) hs9pc g9
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hj2 :=
    step_JLEZ (s := s9) (x := 18) (dest := 1860)
      hs9h hpc9 hs9Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = true := by
    have : le0 (s9.mem.get 18) = true := by
      rw [hs9T]; exact idx_lt_room_inc_le0 (s.mem.get 29) (s.mem.get 28) hRhi hIlt
    simpa [le0] using this
  have hs10eq' : step s9 = { s9 with pc := 1860 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18
          then (1860 : Word) else s9.pc + 3) = (1860 : Word) := by
      simp [hle2]
    rw [hj2, hif]
  have hrun10 : runN s 10 = step s9 := by
    have h10 : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact h10.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hs10pc : s10.pc = 1860 := by have : s10 = step s9 := hrun10; rw [this, hs10eq']
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq']; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by have : s10 = step s9 := hrun10; rw [this, hs10eq']; exact hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq']; exact hpres9 a ha18 ha0
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have g10 : ∀ k : Nat, 1860 ≤ k → k < 1872 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hm2 := ed_mov_ONE_RETID_1860 (s := s10) hs10pc hs10h hs10Z g10
  have hrun14 : runN s 14 = runN s10 4 := runN_add_eq s 10 4 14 (by decide)
  let s14 := runN s 14
  have hs14eq : s14 = runN s10 4 := hrun14
  have hs14pc : s14.pc = 1872 := by rw [hs14eq]; exact hm2.1
  have hs14h : s14.halted = false := by rw [hs14eq]; exact hm2.2.1
  have hs14R : s14.mem.get 2319 = 1 := by
    rw [hs14eq, hm2.2.2.1]
    exact (hpres10 3 (by decide) (by decide)).trans hONE
  have hs14Z : s14.mem.get 0 = 0 := by rw [hs14eq]; exact hm2.2.2.2.1
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 2319 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 haR ha0
    rw [hs14eq]
    exact (hm2.2.2.2.2.2 a haR ha0).trans (hpres10 a ha18 ha0)
  have hONE14 : s14.mem.get 3 = 1 := (hpres14 3 (by decide) (by decide) (by decide)).trans hONE
  have g14 : ∀ k : Nat, 1872 ≤ k → k < 1881 →
      s14.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have nR : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres14 (UInt16.ofNat k) n18 nR n0).trans (hcode k (by omega) (by omega))
  have hinc1 := ed_inc_RETID_1872 (s := s14) hs14pc hs14h hs14Z hONE14 g14
  have hrun17 : runN s 17 = runN s14 3 := runN_add_eq s 14 3 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s14 3 := hrun17
  have hs17pc : s17.pc = 1881 := by rw [hs17eq]; exact hinc1.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact hinc1.2.1
  have hs17R : s17.mem.get 2319 = 2 := by
    rw [hs17eq, hinc1.2.2.1, hs14R]
    exact (rfl : (1 : Word) + 1 = 2)
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact hinc1.2.2.2.1
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 2319 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 haR ha0
    rw [hs17eq]; exact (hinc1.2.2.2.2 a haR ha0).trans (hpres14 a ha18 haR ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide) (by decide)).trans hONE
  have g17 : ∀ k : Nat, 1881 ≤ k → k < 1890 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have nR : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 nR n0).trans (hcode k (by omega) (by omega))
  have hinc2 := ed_inc_RETID_1881 (s := s17) hs17pc hs17h hs17Z hONE17 g17
  have hrun20 : runN s 20 = runN s17 3 := runN_add_eq s 17 3 20 (by decide)
  let s20 := runN s 20
  have hs20eq : s20 = runN s17 3 := hrun20
  have hs20pc : s20.pc = 1890 := by rw [hs20eq]; exact hinc2.1
  have hs20h : s20.halted = false := by rw [hs20eq]; exact hinc2.2.1
  have hs20R : s20.mem.get 2319 = 3 := by
    rw [hs20eq, hinc2.2.2.1, hs17R]
    exact (rfl : (2 : Word) + 1 = 3)
  have hs20Z : s20.mem.get 0 = 0 := by rw [hs20eq]; exact hinc2.2.2.2.1
  have hpres20 : ∀ a, a ≠ 18 → a ≠ 2319 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a ha18 haR ha0
    rw [hs20eq]; exact (hinc2.2.2.2.2 a haR ha0).trans (hpres17 a ha18 haR ha0)
  have hI20 : s20.mem.get 29 = s.mem.get 29 := hpres20 29 (by decide) (by decide) (by decide)
  have hCH20 : s20.mem.get 30 = s.mem.get 30 := hpres20 30 (by decide) (by decide) (by decide)
  have g20 : ∀ k : Nat, 1890 ≤ k → k < 1893 →
      s20.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have nR : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres20 (UInt16.ofNat k) n18 nR n0).trans (hcode k (by omega) (by omega))
  have henc3 := ed_enc_jmp_1890 (s := s20) hs20pc g20
  have hpc20 : s20.pc.toNat < 32768 := by simp [hs20pc]
  have hj3 := step_JMP (s := s20) (dest := 1185)
    hs20h hpc20 hs20Z henc3.1 henc3.2.1 henc3.2.2
  have hrun : s21 = runN s20 1 := runN_add_eq s 20 1 21 (by decide)
  have hs21eq : s21 = step s20 := hrun.trans (runN_one s20 hs20h hpc20)
  have hs21pc : s21.pc = 1185 := by rw [hs21eq, hj3]
  have hs21h : s21.halted = false := by rw [hs21eq, hj3]; exact hs20h
  have hs21Z : s21.mem.get 0 = 0 := by rw [hs21eq, hj3]; exact hs20Z
  have hs21R : s21.mem.get 2319 = 3 := by rw [hs21eq, hj3]; exact hs20R
  have hs21I : s21.mem.get 29 = s.mem.get 29 := by rw [hs21eq, hj3]; exact hI20
  have hs21CH : s21.mem.get 30 = s.mem.get 30 := by rw [hs21eq, hj3]; exact hCH20
  have hpres : ∀ a, a ≠ 18 → a ≠ 2319 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 haR ha0
    rw [hs21eq, hj3]; exact hpres20 a ha18 haR ha0
  exact ⟨hs21pc, hs21h, hs21Z, hs21R, hs21I, hs21CH, hpres⟩

/-- From `TAKE_DIG` with `DI = 0` and `IDX = 0 < ROOM`: write `Q0`
at `BUF+0`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 58 steps. -/
theorem take_store_next_di0_idx0 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 0)
    (hI : s.mem.get 29 = 0)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s58 := runN s 58
    s58.pc = 1641 ∧
    s58.halted = false ∧
    s58.mem.get 0 = 0 ∧
    s58.mem.get 32 = s.mem.get 20 ∧
    s58.mem.get 29 = 1 ∧
    s58.mem.get 2321 = 1 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s58.mem.get a = s.mem.get a) := by
  intro s58
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di0 (s := s) hs0pc hs0h hs0Z hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1824 := ht.1
  have hs10h : s10.halted = false := ht.2.1
  have hs10Z : s10.mem.get 0 = 0 := ht.2.2.1
  have hs10CH : s10.mem.get 30 = s.mem.get 20 := ht.2.2.2.1
  have hs10DI : s10.mem.get 2321 = 0 := ht.2.2.2.2.1
  have hpres10 := ht.2.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide) (by decide)).trans hONE
  have hI10 : s10.mem.get 29 = 0 := (hpres10 29 (by decide) (by decide) (by decide)).trans hI
  have hR10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide) (by decide)
  have hIlt : (s10.mem.get 29).toNat < (s10.mem.get 28).toNat := by
    rw [hI10, hR10]; simp; exact hRlo
  have hRhi' : (s10.mem.get 28).toNat < 32768 := by rw [hR10]; exact hRhi
  have g10 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s10) hs10pc hs10h hs10Z hONE10 hIlt hRhi' g10
  have hrun31 : runN s 31 = runN s10 21 := runN_add_eq s 10 21 31 (by decide)
  let s31 := runN s 31
  have hs31eq : s31 = runN s10 21 := hrun31
  have hs31pc : s31.pc = 1185 := by rw [hs31eq]; exact hhv.1
  have hs31h : s31.halted = false := by rw [hs31eq]; exact hhv.2.1
  have hs31Z : s31.mem.get 0 = 0 := by rw [hs31eq]; exact hhv.2.2.1
  have hs31R : s31.mem.get 2319 = 3 := by rw [hs31eq]; exact hhv.2.2.2.1
  have hs31I : s31.mem.get 29 = 0 := by
    rw [hs31eq, hhv.2.2.2.2.1, hI10]
  have hs31CH : s31.mem.get 30 = s.mem.get 20 := by
    rw [hs31eq, hhv.2.2.2.2.2.1, hs10CH]
  have hpres31 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s31.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs31eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres10 a ha18 ha30 ha0)
  have hONE31 : s31.mem.get 3 = 1 := (hpres31 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI31 : s31.mem.get 2321 = 0 := (hpres31 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g31a : ∀ k : Nat, 1185 ≤ k → k < 1200 →
      s31.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres31 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have g31b : ∀ k : Nat, 1287 ≤ k → k < 1302 →
      s31.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres31 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx0 (s := s31) hs31pc hs31h hs31Z hs31I g31a g31b
  have hrun41 : runN s 41 = runN s31 10 := runN_add_eq s 31 10 41 (by decide)
  let s41 := runN s 41
  have hs41eq : s41 = runN s31 10 := hrun41
  have hs41pc : s41.pc = 1527 := by rw [hs41eq]; exact hs.1
  have hs41h : s41.halted = false := by rw [hs41eq]; exact hs.2.1
  have hs41Z : s41.mem.get 0 = 0 := by rw [hs41eq]; exact hs.2.2.1
  have hs41B : s41.mem.get 32 = s.mem.get 20 := by
    rw [hs41eq, hs.2.2.2.1, hs31CH]
  have hs41I : s41.mem.get 29 = 0 := by rw [hs41eq]; exact hs.2.2.2.2.1
  have hpres41 : ∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s41.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs41eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres31 a ha18 ha30 haR ha0)
  have hONE41 : s41.mem.get 3 = 1 := (hpres41 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR41 : s41.mem.get 2319 = 3 := by
    rw [hs41eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs31R
  have hDI41 : s41.mem.get 2321 = 0 := (hpres41 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g41 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s41.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres41 (UInt16.ofNat k) n32 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s41) hs41pc hs41h hs41Z hONE41 hR41 g41
  have hrun54 : runN s 54 = runN s41 13 := runN_add_eq s 41 13 54 (by decide)
  let s54 := runN s 54
  have hs54eq : s54 = runN s41 13 := hrun54
  have hs54pc : s54.pc = 1893 := by rw [hs54eq]; exact hr.1
  have hs54h : s54.halted = false := by rw [hs54eq]; exact hr.2.1
  have hs54Z : s54.mem.get 0 = 0 := by rw [hs54eq]; exact hr.2.2.1
  have hs54I : s54.mem.get 29 = 1 := by
    rw [hs54eq, hr.2.2.2.1, hs41I]
    exact (rfl : (0 : Word) + 1 = 1)
  have hs54B : s54.mem.get 32 = s.mem.get 20 := by
    rw [hs54eq]
    exact (hr.2.2.2.2 32 (by decide) (by decide) (by decide)).trans hs41B
  have hpres54 : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s54.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs54eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres41 a haB ha18 ha30 haR ha0)
  have hONE54 : s54.mem.get 3 = 1 := (hpres54 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI54 : s54.mem.get 2321 = 0 := (hpres54 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g54 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s54.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres54 (UInt16.ofNat k) n32 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s54) hs54pc hs54h hs54Z hONE54 g54
  have hrun : s58 = runN s54 4 := runN_add_eq s 54 4 58 (by decide)
  have hsTpc : s58.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s58.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s58.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s58.mem.get 2321 = 1 := by
    rw [hrun, hn.2.2.2.1, hDI54]
    exact (rfl : (0 : Word) + 1 = 1)
  have hsTI : s58.mem.get 29 = 1 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs54I
  have hsTB : s58.mem.get 32 = s.mem.get 20 := by
    rw [hrun]; exact (hn.2.2.2.2 32 (by decide) (by decide)).trans hs54B
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s58.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres54 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- From `TAKE_DIG` with `DI = 0` and `IDX = 1 < ROOM`: write `Q0`
at `BUF+1`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 60 steps. -/
theorem take_store_next_di0_idx1 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 0)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s60 := runN s 60
    s60.pc = 1641 ∧
    s60.halted = false ∧
    s60.mem.get 0 = 0 ∧
    s60.mem.get 33 = s.mem.get 20 ∧
    s60.mem.get 29 = 2 ∧
    s60.mem.get 2321 = 1 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s60.mem.get a = s.mem.get a) := by
  intro s60
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di0 (s := s) hs0pc hs0h hs0Z hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1824 := ht.1
  have hs10h : s10.halted = false := ht.2.1
  have hs10Z : s10.mem.get 0 = 0 := ht.2.2.1
  have hs10CH : s10.mem.get 30 = s.mem.get 20 := ht.2.2.2.1
  have hs10DI : s10.mem.get 2321 = 0 := ht.2.2.2.2.1
  have hpres10 := ht.2.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide) (by decide)).trans hONE
  have hI10 : s10.mem.get 29 = 1 := (hpres10 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide) (by decide)
  have hIlt : (s10.mem.get 29).toNat < (s10.mem.get 28).toNat := by
    rw [hI10, hRmem10]; simp; exact hRlo
  have hRhi' : (s10.mem.get 28).toNat < 32768 := by rw [hRmem10]; exact hRhi
  have g10 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s10) hs10pc hs10h hs10Z hONE10 hIlt hRhi' g10
  have hrun31 : runN s 31 = runN s10 21 := runN_add_eq s 10 21 31 (by decide)
  let s31 := runN s 31
  have hs31eq : s31 = runN s10 21 := hrun31
  have hs31pc : s31.pc = 1185 := by rw [hs31eq]; exact hhv.1
  have hs31h : s31.halted = false := by rw [hs31eq]; exact hhv.2.1
  have hs31Z : s31.mem.get 0 = 0 := by rw [hs31eq]; exact hhv.2.2.1
  have hs31R : s31.mem.get 2319 = 3 := by rw [hs31eq]; exact hhv.2.2.2.1
  have hs31I : s31.mem.get 29 = 1 := by
    rw [hs31eq, hhv.2.2.2.2.1, hI10]
  have hs31CH : s31.mem.get 30 = s.mem.get 20 := by
    rw [hs31eq, hhv.2.2.2.2.2.1, hs10CH]
  have hpres31 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s31.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs31eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres10 a ha18 ha30 ha0)
  have hONE31 : s31.mem.get 3 = 1 := (hpres31 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI31 : s31.mem.get 2321 = 0 := (hpres31 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g31 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s31.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres31 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx1 (s := s31) hs31pc hs31h hs31Z hONE31 hs31I g31
  have hrun43 : runN s 43 = runN s31 12 := runN_add_eq s 31 12 43 (by decide)
  let s43 := runN s 43
  have hs43eq : s43 = runN s31 12 := hrun43
  have hs43pc : s43.pc = 1527 := by rw [hs43eq]; exact hs.1
  have hs43h : s43.halted = false := by rw [hs43eq]; exact hs.2.1
  have hs43Z : s43.mem.get 0 = 0 := by rw [hs43eq]; exact hs.2.2.1
  have hs43B : s43.mem.get 33 = s.mem.get 20 := by
    rw [hs43eq, hs.2.2.2.1, hs31CH]
  have hs43I : s43.mem.get 29 = 1 := by rw [hs43eq]; exact hs.2.2.2.2.1
  have hpres43 : ∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s43.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs43eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres31 a ha18 ha30 haR ha0)
  have hONE43 : s43.mem.get 3 = 1 := (hpres43 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR43 : s43.mem.get 2319 = 3 := by
    rw [hs43eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs31R
  have hDI43 : s43.mem.get 2321 = 0 := (hpres43 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g43 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s43.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres43 (UInt16.ofNat k) n33 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s43) hs43pc hs43h hs43Z hONE43 hR43 g43
  have hrun56 : runN s 56 = runN s43 13 := runN_add_eq s 43 13 56 (by decide)
  let s56 := runN s 56
  have hs56eq : s56 = runN s43 13 := hrun56
  have hs56pc : s56.pc = 1893 := by rw [hs56eq]; exact hr.1
  have hs56h : s56.halted = false := by rw [hs56eq]; exact hr.2.1
  have hs56Z : s56.mem.get 0 = 0 := by rw [hs56eq]; exact hr.2.2.1
  have hs56I : s56.mem.get 29 = 2 := by
    rw [hs56eq, hr.2.2.2.1, hs43I]
    exact (rfl : (1 : Word) + 1 = 2)
  have hs56B : s56.mem.get 33 = s.mem.get 20 := by
    rw [hs56eq]
    exact (hr.2.2.2.2 33 (by decide) (by decide) (by decide)).trans hs43B
  have hpres56 : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s56.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs56eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres43 a haB ha18 ha30 haR ha0)
  have hONE56 : s56.mem.get 3 = 1 := (hpres56 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI56 : s56.mem.get 2321 = 0 := (hpres56 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g56 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s56.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres56 (UInt16.ofNat k) n33 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s56) hs56pc hs56h hs56Z hONE56 g56
  have hrun : s60 = runN s56 4 := runN_add_eq s 56 4 60 (by decide)
  have hsTpc : s60.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s60.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s60.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s60.mem.get 2321 = 1 := by
    rw [hrun, hn.2.2.2.1, hDI56]
    exact (rfl : (0 : Word) + 1 = 1)
  have hsTI : s60.mem.get 29 = 2 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs56I
  have hsTB : s60.mem.get 33 = s.mem.get 20 := by
    rw [hrun]; exact (hn.2.2.2.2 33 (by decide) (by decide)).trans hs56B
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s60.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres56 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 0` and `IDX = 2 < ROOM`: write `Q0`
at `BUF+2`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 62 steps. -/
theorem take_store_next_di0_idx2 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 0)
    (hI : s.mem.get 29 = 2)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s62 := runN s 62
    s62.pc = 1641 ∧
    s62.halted = false ∧
    s62.mem.get 0 = 0 ∧
    s62.mem.get 34 = s.mem.get 20 ∧
    s62.mem.get 29 = 3 ∧
    s62.mem.get 2321 = 1 ∧
    (∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s62.mem.get a = s.mem.get a) := by
  intro s62
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di0 (s := s) hs0pc hs0h hs0Z hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1824 := ht.1
  have hs10h : s10.halted = false := ht.2.1
  have hs10Z : s10.mem.get 0 = 0 := ht.2.2.1
  have hs10CH : s10.mem.get 30 = s.mem.get 20 := ht.2.2.2.1
  have hs10DI : s10.mem.get 2321 = 0 := ht.2.2.2.2.1
  have hpres10 := ht.2.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide) (by decide)).trans hONE
  have hI10 : s10.mem.get 29 = 2 := (hpres10 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide) (by decide)
  have hIlt : (s10.mem.get 29).toNat < (s10.mem.get 28).toNat := by
    rw [hI10, hRmem10]; simp; exact hRlo
  have hRhi' : (s10.mem.get 28).toNat < 32768 := by rw [hRmem10]; exact hRhi
  have g10 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s10) hs10pc hs10h hs10Z hONE10 hIlt hRhi' g10
  have hrun31 : runN s 31 = runN s10 21 := runN_add_eq s 10 21 31 (by decide)
  let s31 := runN s 31
  have hs31eq : s31 = runN s10 21 := hrun31
  have hs31pc : s31.pc = 1185 := by rw [hs31eq]; exact hhv.1
  have hs31h : s31.halted = false := by rw [hs31eq]; exact hhv.2.1
  have hs31Z : s31.mem.get 0 = 0 := by rw [hs31eq]; exact hhv.2.2.1
  have hs31R : s31.mem.get 2319 = 3 := by rw [hs31eq]; exact hhv.2.2.2.1
  have hs31I : s31.mem.get 29 = 2 := by
    rw [hs31eq, hhv.2.2.2.2.1, hI10]
  have hs31CH : s31.mem.get 30 = s.mem.get 20 := by
    rw [hs31eq, hhv.2.2.2.2.2.1, hs10CH]
  have hpres31 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s31.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs31eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres10 a ha18 ha30 ha0)
  have hONE31 : s31.mem.get 3 = 1 := (hpres31 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI31 : s31.mem.get 2321 = 0 := (hpres31 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g31 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s31.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres31 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx2 (s := s31) hs31pc hs31h hs31Z hONE31 hs31I g31
  have hrun45 : runN s 45 = runN s31 14 := runN_add_eq s 31 14 45 (by decide)
  let s45 := runN s 45
  have hs45eq : s45 = runN s31 14 := hrun45
  have hs45pc : s45.pc = 1527 := by rw [hs45eq]; exact hs.1
  have hs45h : s45.halted = false := by rw [hs45eq]; exact hs.2.1
  have hs45Z : s45.mem.get 0 = 0 := by rw [hs45eq]; exact hs.2.2.1
  have hs45B : s45.mem.get 34 = s.mem.get 20 := by
    rw [hs45eq, hs.2.2.2.1, hs31CH]
  have hs45I : s45.mem.get 29 = 2 := by rw [hs45eq]; exact hs.2.2.2.2.1
  have hpres45 : ∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s45.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs45eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres31 a ha18 ha30 haR ha0)
  have hONE45 : s45.mem.get 3 = 1 := (hpres45 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR45 : s45.mem.get 2319 = 3 := by
    rw [hs45eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs31R
  have hDI45 : s45.mem.get 2321 = 0 := (hpres45 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g45 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s45.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres45 (UInt16.ofNat k) n34 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s45) hs45pc hs45h hs45Z hONE45 hR45 g45
  have hrun58 : runN s 58 = runN s45 13 := runN_add_eq s 45 13 58 (by decide)
  let s58 := runN s 58
  have hs58eq : s58 = runN s45 13 := hrun58
  have hs58pc : s58.pc = 1893 := by rw [hs58eq]; exact hr.1
  have hs58h : s58.halted = false := by rw [hs58eq]; exact hr.2.1
  have hs58Z : s58.mem.get 0 = 0 := by rw [hs58eq]; exact hr.2.2.1
  have hs58I : s58.mem.get 29 = 3 := by
    rw [hs58eq, hr.2.2.2.1, hs45I]
    exact (rfl : (2 : Word) + 1 = 3)
  have hs58B : s58.mem.get 34 = s.mem.get 20 := by
    rw [hs58eq]
    exact (hr.2.2.2.2 34 (by decide) (by decide) (by decide)).trans hs45B
  have hpres58 : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s58.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs58eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres45 a haB ha18 ha30 haR ha0)
  have hONE58 : s58.mem.get 3 = 1 := (hpres58 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI58 : s58.mem.get 2321 = 0 := (hpres58 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g58 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s58.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres58 (UInt16.ofNat k) n34 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s58) hs58pc hs58h hs58Z hONE58 g58
  have hrun : s62 = runN s58 4 := runN_add_eq s 58 4 62 (by decide)
  have hsTpc : s62.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s62.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s62.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s62.mem.get 2321 = 1 := by
    rw [hrun, hn.2.2.2.1, hDI58]
    exact (rfl : (0 : Word) + 1 = 1)
  have hsTI : s62.mem.get 29 = 3 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs58I
  have hsTB : s62.mem.get 34 = s.mem.get 20 := by
    rw [hrun]; exact (hn.2.2.2.2 34 (by decide) (by decide)).trans hs58B
  have hpres : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s62.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres58 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 0` and `IDX = 3 < ROOM`: write `Q0`
at `BUF+3`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 64 steps. -/
theorem take_store_next_di0_idx3 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 0)
    (hI : s.mem.get 29 = 3)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s64 := runN s 64
    s64.pc = 1641 ∧
    s64.halted = false ∧
    s64.mem.get 0 = 0 ∧
    s64.mem.get 35 = s.mem.get 20 ∧
    s64.mem.get 29 = 4 ∧
    s64.mem.get 2321 = 1 ∧
    (∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s64.mem.get a = s.mem.get a) := by
  intro s64
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di0 (s := s) hs0pc hs0h hs0Z hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1824 := ht.1
  have hs10h : s10.halted = false := ht.2.1
  have hs10Z : s10.mem.get 0 = 0 := ht.2.2.1
  have hs10CH : s10.mem.get 30 = s.mem.get 20 := ht.2.2.2.1
  have hs10DI : s10.mem.get 2321 = 0 := ht.2.2.2.2.1
  have hpres10 := ht.2.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide) (by decide)).trans hONE
  have hI10 : s10.mem.get 29 = 3 := (hpres10 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide) (by decide)
  have hIlt : (s10.mem.get 29).toNat < (s10.mem.get 28).toNat := by
    rw [hI10, hRmem10]; simp; exact hRlo
  have hRhi' : (s10.mem.get 28).toNat < 32768 := by rw [hRmem10]; exact hRhi
  have g10 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s10) hs10pc hs10h hs10Z hONE10 hIlt hRhi' g10
  have hrun31 : runN s 31 = runN s10 21 := runN_add_eq s 10 21 31 (by decide)
  let s31 := runN s 31
  have hs31eq : s31 = runN s10 21 := hrun31
  have hs31pc : s31.pc = 1185 := by rw [hs31eq]; exact hhv.1
  have hs31h : s31.halted = false := by rw [hs31eq]; exact hhv.2.1
  have hs31Z : s31.mem.get 0 = 0 := by rw [hs31eq]; exact hhv.2.2.1
  have hs31R : s31.mem.get 2319 = 3 := by rw [hs31eq]; exact hhv.2.2.2.1
  have hs31I : s31.mem.get 29 = 3 := by
    rw [hs31eq, hhv.2.2.2.2.1, hI10]
  have hs31CH : s31.mem.get 30 = s.mem.get 20 := by
    rw [hs31eq, hhv.2.2.2.2.2.1, hs10CH]
  have hpres31 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s31.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs31eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres10 a ha18 ha30 ha0)
  have hONE31 : s31.mem.get 3 = 1 := (hpres31 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI31 : s31.mem.get 2321 = 0 := (hpres31 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g31 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s31.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres31 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx3 (s := s31) hs31pc hs31h hs31Z hONE31 hs31I g31
  have hrun47 : runN s 47 = runN s31 16 := runN_add_eq s 31 16 47 (by decide)
  let s47 := runN s 47
  have hs47eq : s47 = runN s31 16 := hrun47
  have hs47pc : s47.pc = 1527 := by rw [hs47eq]; exact hs.1
  have hs47h : s47.halted = false := by rw [hs47eq]; exact hs.2.1
  have hs47Z : s47.mem.get 0 = 0 := by rw [hs47eq]; exact hs.2.2.1
  have hs47B : s47.mem.get 35 = s.mem.get 20 := by
    rw [hs47eq, hs.2.2.2.1, hs31CH]
  have hs47I : s47.mem.get 29 = 3 := by rw [hs47eq]; exact hs.2.2.2.2.1
  have hpres47 : ∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s47.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs47eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres31 a ha18 ha30 haR ha0)
  have hONE47 : s47.mem.get 3 = 1 := (hpres47 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR47 : s47.mem.get 2319 = 3 := by
    rw [hs47eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs31R
  have hDI47 : s47.mem.get 2321 = 0 := (hpres47 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g47 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n35 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s47) hs47pc hs47h hs47Z hONE47 hR47 g47
  have hrun60 : runN s 60 = runN s47 13 := runN_add_eq s 47 13 60 (by decide)
  let s60 := runN s 60
  have hs60eq : s60 = runN s47 13 := hrun60
  have hs60pc : s60.pc = 1893 := by rw [hs60eq]; exact hr.1
  have hs60h : s60.halted = false := by rw [hs60eq]; exact hr.2.1
  have hs60Z : s60.mem.get 0 = 0 := by rw [hs60eq]; exact hr.2.2.1
  have hs60I : s60.mem.get 29 = 4 := by
    rw [hs60eq, hr.2.2.2.1, hs47I]
    exact (rfl : (3 : Word) + 1 = 4)
  have hs60B : s60.mem.get 35 = s.mem.get 20 := by
    rw [hs60eq]
    exact (hr.2.2.2.2 35 (by decide) (by decide) (by decide)).trans hs47B
  have hpres60 : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s60.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs60eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres47 a haB ha18 ha30 haR ha0)
  have hONE60 : s60.mem.get 3 = 1 := (hpres60 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI60 : s60.mem.get 2321 = 0 := (hpres60 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g60 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s60.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres60 (UInt16.ofNat k) n35 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s60) hs60pc hs60h hs60Z hONE60 g60
  have hrun : s64 = runN s60 4 := runN_add_eq s 60 4 64 (by decide)
  have hsTpc : s64.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s64.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s64.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s64.mem.get 2321 = 1 := by
    rw [hrun, hn.2.2.2.1, hDI60]
    exact (rfl : (0 : Word) + 1 = 1)
  have hsTI : s64.mem.get 29 = 4 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs60I
  have hsTB : s64.mem.get 35 = s.mem.get 20 := by
    rw [hrun]; exact (hn.2.2.2.2 35 (by decide) (by decide)).trans hs60B
  have hpres : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s64.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres60 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 0` and `IDX = 4 < ROOM`: write `Q0`
at `BUF+4`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 66 steps. -/
theorem take_store_next_di0_idx4 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 0)
    (hI : s.mem.get 29 = 4)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s66 := runN s 66
    s66.pc = 1641 ∧
    s66.halted = false ∧
    s66.mem.get 0 = 0 ∧
    s66.mem.get 36 = s.mem.get 20 ∧
    s66.mem.get 29 = 5 ∧
    s66.mem.get 2321 = 1 ∧
    (∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s66.mem.get a = s.mem.get a) := by
  intro s66
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di0 (s := s) hs0pc hs0h hs0Z hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1824 := ht.1
  have hs10h : s10.halted = false := ht.2.1
  have hs10Z : s10.mem.get 0 = 0 := ht.2.2.1
  have hs10CH : s10.mem.get 30 = s.mem.get 20 := ht.2.2.2.1
  have hs10DI : s10.mem.get 2321 = 0 := ht.2.2.2.2.1
  have hpres10 := ht.2.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide) (by decide)).trans hONE
  have hI10 : s10.mem.get 29 = 4 := (hpres10 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide) (by decide)
  have hIlt : (s10.mem.get 29).toNat < (s10.mem.get 28).toNat := by
    rw [hI10, hRmem10]; simp; exact hRlo
  have hRhi' : (s10.mem.get 28).toNat < 32768 := by rw [hRmem10]; exact hRhi
  have g10 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s10) hs10pc hs10h hs10Z hONE10 hIlt hRhi' g10
  have hrun31 : runN s 31 = runN s10 21 := runN_add_eq s 10 21 31 (by decide)
  let s31 := runN s 31
  have hs31eq : s31 = runN s10 21 := hrun31
  have hs31pc : s31.pc = 1185 := by rw [hs31eq]; exact hhv.1
  have hs31h : s31.halted = false := by rw [hs31eq]; exact hhv.2.1
  have hs31Z : s31.mem.get 0 = 0 := by rw [hs31eq]; exact hhv.2.2.1
  have hs31R : s31.mem.get 2319 = 3 := by rw [hs31eq]; exact hhv.2.2.2.1
  have hs31I : s31.mem.get 29 = 4 := by
    rw [hs31eq, hhv.2.2.2.2.1, hI10]
  have hs31CH : s31.mem.get 30 = s.mem.get 20 := by
    rw [hs31eq, hhv.2.2.2.2.2.1, hs10CH]
  have hpres31 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s31.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs31eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres10 a ha18 ha30 ha0)
  have hONE31 : s31.mem.get 3 = 1 := (hpres31 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI31 : s31.mem.get 2321 = 0 := (hpres31 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g31 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s31.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres31 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx4 (s := s31) hs31pc hs31h hs31Z hONE31 hs31I g31
  have hrun49 : runN s 49 = runN s31 18 := runN_add_eq s 31 18 49 (by decide)
  let s49 := runN s 49
  have hs49eq : s49 = runN s31 18 := hrun49
  have hs49pc : s49.pc = 1527 := by rw [hs49eq]; exact hs.1
  have hs49h : s49.halted = false := by rw [hs49eq]; exact hs.2.1
  have hs49Z : s49.mem.get 0 = 0 := by rw [hs49eq]; exact hs.2.2.1
  have hs49B : s49.mem.get 36 = s.mem.get 20 := by
    rw [hs49eq, hs.2.2.2.1, hs31CH]
  have hs49I : s49.mem.get 29 = 4 := by rw [hs49eq]; exact hs.2.2.2.2.1
  have hpres49 : ∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s49.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs49eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres31 a ha18 ha30 haR ha0)
  have hONE49 : s49.mem.get 3 = 1 := (hpres49 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR49 : s49.mem.get 2319 = 3 := by
    rw [hs49eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs31R
  have hDI49 : s49.mem.get 2321 = 0 := (hpres49 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g49 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s49.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres49 (UInt16.ofNat k) n36 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s49) hs49pc hs49h hs49Z hONE49 hR49 g49
  have hrun62 : runN s 62 = runN s49 13 := runN_add_eq s 49 13 62 (by decide)
  let s62 := runN s 62
  have hs62eq : s62 = runN s49 13 := hrun62
  have hs62pc : s62.pc = 1893 := by rw [hs62eq]; exact hr.1
  have hs62h : s62.halted = false := by rw [hs62eq]; exact hr.2.1
  have hs62Z : s62.mem.get 0 = 0 := by rw [hs62eq]; exact hr.2.2.1
  have hs62I : s62.mem.get 29 = 5 := by
    rw [hs62eq, hr.2.2.2.1, hs49I]
    exact (rfl : (4 : Word) + 1 = 5)
  have hs62B : s62.mem.get 36 = s.mem.get 20 := by
    rw [hs62eq]
    exact (hr.2.2.2.2 36 (by decide) (by decide) (by decide)).trans hs49B
  have hpres62 : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s62.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs62eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres49 a haB ha18 ha30 haR ha0)
  have hONE62 : s62.mem.get 3 = 1 := (hpres62 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI62 : s62.mem.get 2321 = 0 := (hpres62 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g62 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s62.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres62 (UInt16.ofNat k) n36 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s62) hs62pc hs62h hs62Z hONE62 g62
  have hrun : s66 = runN s62 4 := runN_add_eq s 62 4 66 (by decide)
  have hsTpc : s66.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s66.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s66.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s66.mem.get 2321 = 1 := by
    rw [hrun, hn.2.2.2.1, hDI62]
    exact (rfl : (0 : Word) + 1 = 1)
  have hsTI : s66.mem.get 29 = 5 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs62I
  have hsTB : s66.mem.get 36 = s.mem.get 20 := by
    rw [hrun]; exact (hn.2.2.2.2 36 (by decide) (by decide)).trans hs62B
  have hpres : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s66.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres62 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 0` and `IDX = 5 < ROOM`: write `Q0`
at `BUF+5`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 68 steps. -/
theorem take_store_next_di0_idx5 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 0)
    (hI : s.mem.get 29 = 5)
    (hRlo : 5 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s68 := runN s 68
    s68.pc = 1641 ∧
    s68.halted = false ∧
    s68.mem.get 0 = 0 ∧
    s68.mem.get 37 = s.mem.get 20 ∧
    s68.mem.get 29 = 6 ∧
    s68.mem.get 2321 = 1 ∧
    (∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s68.mem.get a = s.mem.get a) := by
  intro s68
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di0 (s := s) hs0pc hs0h hs0Z hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1824 := ht.1
  have hs10h : s10.halted = false := ht.2.1
  have hs10Z : s10.mem.get 0 = 0 := ht.2.2.1
  have hs10CH : s10.mem.get 30 = s.mem.get 20 := ht.2.2.2.1
  have hs10DI : s10.mem.get 2321 = 0 := ht.2.2.2.2.1
  have hpres10 := ht.2.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide) (by decide)).trans hONE
  have hI10 : s10.mem.get 29 = 5 := (hpres10 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide) (by decide)
  have hIlt : (s10.mem.get 29).toNat < (s10.mem.get 28).toNat := by
    rw [hI10, hRmem10]; simp; exact hRlo
  have hRhi' : (s10.mem.get 28).toNat < 32768 := by rw [hRmem10]; exact hRhi
  have g10 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s10) hs10pc hs10h hs10Z hONE10 hIlt hRhi' g10
  have hrun31 : runN s 31 = runN s10 21 := runN_add_eq s 10 21 31 (by decide)
  let s31 := runN s 31
  have hs31eq : s31 = runN s10 21 := hrun31
  have hs31pc : s31.pc = 1185 := by rw [hs31eq]; exact hhv.1
  have hs31h : s31.halted = false := by rw [hs31eq]; exact hhv.2.1
  have hs31Z : s31.mem.get 0 = 0 := by rw [hs31eq]; exact hhv.2.2.1
  have hs31R : s31.mem.get 2319 = 3 := by rw [hs31eq]; exact hhv.2.2.2.1
  have hs31I : s31.mem.get 29 = 5 := by
    rw [hs31eq, hhv.2.2.2.2.1, hI10]
  have hs31CH : s31.mem.get 30 = s.mem.get 20 := by
    rw [hs31eq, hhv.2.2.2.2.2.1, hs10CH]
  have hpres31 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s31.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs31eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres10 a ha18 ha30 ha0)
  have hONE31 : s31.mem.get 3 = 1 := (hpres31 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI31 : s31.mem.get 2321 = 0 := (hpres31 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g31 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s31.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres31 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx5 (s := s31) hs31pc hs31h hs31Z hONE31 hs31I g31
  have hrun51 : runN s 51 = runN s31 20 := runN_add_eq s 31 20 51 (by decide)
  let s51 := runN s 51
  have hs51eq : s51 = runN s31 20 := hrun51
  have hs51pc : s51.pc = 1527 := by rw [hs51eq]; exact hs.1
  have hs51h : s51.halted = false := by rw [hs51eq]; exact hs.2.1
  have hs51Z : s51.mem.get 0 = 0 := by rw [hs51eq]; exact hs.2.2.1
  have hs51B : s51.mem.get 37 = s.mem.get 20 := by
    rw [hs51eq, hs.2.2.2.1, hs31CH]
  have hs51I : s51.mem.get 29 = 5 := by rw [hs51eq]; exact hs.2.2.2.2.1
  have hpres51 : ∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s51.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs51eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres31 a ha18 ha30 haR ha0)
  have hONE51 : s51.mem.get 3 = 1 := (hpres51 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR51 : s51.mem.get 2319 = 3 := by
    rw [hs51eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs31R
  have hDI51 : s51.mem.get 2321 = 0 := (hpres51 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g51 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s51.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres51 (UInt16.ofNat k) n37 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s51) hs51pc hs51h hs51Z hONE51 hR51 g51
  have hrun64 : runN s 64 = runN s51 13 := runN_add_eq s 51 13 64 (by decide)
  let s64 := runN s 64
  have hs64eq : s64 = runN s51 13 := hrun64
  have hs64pc : s64.pc = 1893 := by rw [hs64eq]; exact hr.1
  have hs64h : s64.halted = false := by rw [hs64eq]; exact hr.2.1
  have hs64Z : s64.mem.get 0 = 0 := by rw [hs64eq]; exact hr.2.2.1
  have hs64I : s64.mem.get 29 = 6 := by
    rw [hs64eq, hr.2.2.2.1, hs51I]
    exact (rfl : (5 : Word) + 1 = 6)
  have hs64B : s64.mem.get 37 = s.mem.get 20 := by
    rw [hs64eq]
    exact (hr.2.2.2.2 37 (by decide) (by decide) (by decide)).trans hs51B
  have hpres64 : ∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s64.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs64eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres51 a haB ha18 ha30 haR ha0)
  have hONE64 : s64.mem.get 3 = 1 := (hpres64 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI64 : s64.mem.get 2321 = 0 := (hpres64 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g64 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s64.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres64 (UInt16.ofNat k) n37 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s64) hs64pc hs64h hs64Z hONE64 g64
  have hrun : s68 = runN s64 4 := runN_add_eq s 64 4 68 (by decide)
  have hsTpc : s68.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s68.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s68.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s68.mem.get 2321 = 1 := by
    rw [hrun, hn.2.2.2.1, hDI64]
    exact (rfl : (0 : Word) + 1 = 1)
  have hsTI : s68.mem.get 29 = 6 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs64I
  have hsTB : s68.mem.get 37 = s.mem.get 20 := by
    rw [hrun]; exact (hn.2.2.2.2 37 (by decide) (by decide)).trans hs64B
  have hpres : ∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s68.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres64 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 1` and `IDX = 0 < ROOM`: write `Q1`
at `BUF+0`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 60 steps. -/
theorem take_store_next_di1_idx0 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 1)
    (hI : s.mem.get 29 = 0)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s60 := runN s 60
    s60.pc = 1641 ∧
    s60.halted = false ∧
    s60.mem.get 0 = 0 ∧
    s60.mem.get 32 = s.mem.get 21 ∧
    s60.mem.get 29 = 1 ∧
    s60.mem.get 2321 = 2 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s60.mem.get a = s.mem.get a) := by
  intro s60
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di1 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1824 := ht.1
  have hs12h : s12.halted = false := ht.2.1
  have hs12Z : s12.mem.get 0 = 0 := ht.2.2.1
  have hs12CH : s12.mem.get 30 = s.mem.get 21 := ht.2.2.2.1
  have hs12DI : s12.mem.get 2321 = 1 := ht.2.2.2.2.1
  have hpres12 := ht.2.2.2.2.2
  have hONE12 : s12.mem.get 3 = 1 := (hpres12 3 (by decide) (by decide) (by decide)).trans hONE
  have hI12 : s12.mem.get 29 = 0 := (hpres12 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem12 : s12.mem.get 28 = s.mem.get 28 := hpres12 28 (by decide) (by decide) (by decide)
  have hIlt : (s12.mem.get 29).toNat < (s12.mem.get 28).toNat := by
    rw [hI12, hRmem12]; simp; exact hRlo
  have hRhi' : (s12.mem.get 28).toNat < 32768 := by rw [hRmem12]; exact hRhi
  have g12 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s12.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres12 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s12) hs12pc hs12h hs12Z hONE12 hIlt hRhi' g12
  have hrun33 : runN s 33 = runN s12 21 := runN_add_eq s 12 21 33 (by decide)
  let s33 := runN s 33
  have hs33eq : s33 = runN s12 21 := hrun33
  have hs33pc : s33.pc = 1185 := by rw [hs33eq]; exact hhv.1
  have hs33h : s33.halted = false := by rw [hs33eq]; exact hhv.2.1
  have hs33Z : s33.mem.get 0 = 0 := by rw [hs33eq]; exact hhv.2.2.1
  have hs33R : s33.mem.get 2319 = 3 := by rw [hs33eq]; exact hhv.2.2.2.1
  have hs33I : s33.mem.get 29 = 0 := by
    rw [hs33eq, hhv.2.2.2.2.1, hI12]
  have hs33CH : s33.mem.get 30 = s.mem.get 21 := by
    rw [hs33eq, hhv.2.2.2.2.2.1, hs12CH]
  have hpres33 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s33.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs33eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres12 a ha18 ha30 ha0)
  have hONE33 : s33.mem.get 3 = 1 := (hpres33 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI33 : s33.mem.get 2321 = 1 := (hpres33 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g33a : ∀ k : Nat, 1185 ≤ k → k < 1200 →
      s33.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres33 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have g33b : ∀ k : Nat, 1287 ≤ k → k < 1302 →
      s33.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres33 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx0 (s := s33) hs33pc hs33h hs33Z hs33I g33a g33b
  have hrun43 : runN s 43 = runN s33 10 := runN_add_eq s 33 10 43 (by decide)
  let s43 := runN s 43
  have hs43eq : s43 = runN s33 10 := hrun43
  have hs43pc : s43.pc = 1527 := by rw [hs43eq]; exact hs.1
  have hs43h : s43.halted = false := by rw [hs43eq]; exact hs.2.1
  have hs43Z : s43.mem.get 0 = 0 := by rw [hs43eq]; exact hs.2.2.1
  have hs43B : s43.mem.get 32 = s.mem.get 21 := by
    rw [hs43eq, hs.2.2.2.1, hs33CH]
  have hs43I : s43.mem.get 29 = 0 := by rw [hs43eq]; exact hs.2.2.2.2.1
  have hpres43 : ∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s43.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs43eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres33 a ha18 ha30 haR ha0)
  have hONE43 : s43.mem.get 3 = 1 := (hpres43 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR43 : s43.mem.get 2319 = 3 := by
    rw [hs43eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs33R
  have hDI43 : s43.mem.get 2321 = 1 := (hpres43 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g43 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s43.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres43 (UInt16.ofNat k) n32 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s43) hs43pc hs43h hs43Z hONE43 hR43 g43
  have hrun56 : runN s 56 = runN s43 13 := runN_add_eq s 43 13 56 (by decide)
  let s56 := runN s 56
  have hs56eq : s56 = runN s43 13 := hrun56
  have hs56pc : s56.pc = 1893 := by rw [hs56eq]; exact hr.1
  have hs56h : s56.halted = false := by rw [hs56eq]; exact hr.2.1
  have hs56Z : s56.mem.get 0 = 0 := by rw [hs56eq]; exact hr.2.2.1
  have hs56I : s56.mem.get 29 = 1 := by
    rw [hs56eq, hr.2.2.2.1, hs43I]
    exact (rfl : (0 : Word) + 1 = 1)
  have hs56B : s56.mem.get 32 = s.mem.get 21 := by
    rw [hs56eq]
    exact (hr.2.2.2.2 32 (by decide) (by decide) (by decide)).trans hs43B
  have hpres56 : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s56.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs56eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres43 a haB ha18 ha30 haR ha0)
  have hONE56 : s56.mem.get 3 = 1 := (hpres56 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI56 : s56.mem.get 2321 = 1 := (hpres56 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g56 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s56.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres56 (UInt16.ofNat k) n32 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s56) hs56pc hs56h hs56Z hONE56 g56
  have hrun : s60 = runN s56 4 := runN_add_eq s 56 4 60 (by decide)
  have hsTpc : s60.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s60.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s60.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s60.mem.get 2321 = 2 := by
    rw [hrun, hn.2.2.2.1, hDI56]
    exact (rfl : (1 : Word) + 1 = 2)
  have hsTI : s60.mem.get 29 = 1 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs56I
  have hsTB : s60.mem.get 32 = s.mem.get 21 := by
    rw [hrun]; exact (hn.2.2.2.2 32 (by decide) (by decide)).trans hs56B
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s60.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres56 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 1` and `IDX = 1 < ROOM`: write `Q1`
at `BUF+1`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 62 steps. -/
theorem take_store_next_di1_idx1 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 1)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s62 := runN s 62
    s62.pc = 1641 ∧
    s62.halted = false ∧
    s62.mem.get 0 = 0 ∧
    s62.mem.get 33 = s.mem.get 21 ∧
    s62.mem.get 29 = 2 ∧
    s62.mem.get 2321 = 2 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s62.mem.get a = s.mem.get a) := by
  intro s62
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di1 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1824 := ht.1
  have hs12h : s12.halted = false := ht.2.1
  have hs12Z : s12.mem.get 0 = 0 := ht.2.2.1
  have hs12CH : s12.mem.get 30 = s.mem.get 21 := ht.2.2.2.1
  have hs12DI : s12.mem.get 2321 = 1 := ht.2.2.2.2.1
  have hpres12 := ht.2.2.2.2.2
  have hONE12 : s12.mem.get 3 = 1 := (hpres12 3 (by decide) (by decide) (by decide)).trans hONE
  have hI12 : s12.mem.get 29 = 1 := (hpres12 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem12 : s12.mem.get 28 = s.mem.get 28 := hpres12 28 (by decide) (by decide) (by decide)
  have hIlt : (s12.mem.get 29).toNat < (s12.mem.get 28).toNat := by
    rw [hI12, hRmem12]; simp; exact hRlo
  have hRhi' : (s12.mem.get 28).toNat < 32768 := by rw [hRmem12]; exact hRhi
  have g12 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s12.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres12 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s12) hs12pc hs12h hs12Z hONE12 hIlt hRhi' g12
  have hrun33 : runN s 33 = runN s12 21 := runN_add_eq s 12 21 33 (by decide)
  let s33 := runN s 33
  have hs33eq : s33 = runN s12 21 := hrun33
  have hs33pc : s33.pc = 1185 := by rw [hs33eq]; exact hhv.1
  have hs33h : s33.halted = false := by rw [hs33eq]; exact hhv.2.1
  have hs33Z : s33.mem.get 0 = 0 := by rw [hs33eq]; exact hhv.2.2.1
  have hs33R : s33.mem.get 2319 = 3 := by rw [hs33eq]; exact hhv.2.2.2.1
  have hs33I : s33.mem.get 29 = 1 := by
    rw [hs33eq, hhv.2.2.2.2.1, hI12]
  have hs33CH : s33.mem.get 30 = s.mem.get 21 := by
    rw [hs33eq, hhv.2.2.2.2.2.1, hs12CH]
  have hpres33 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s33.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs33eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres12 a ha18 ha30 ha0)
  have hONE33 : s33.mem.get 3 = 1 := (hpres33 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI33 : s33.mem.get 2321 = 1 := (hpres33 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g33 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s33.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres33 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx1 (s := s33) hs33pc hs33h hs33Z hONE33 hs33I g33
  have hrun45 : runN s 45 = runN s33 12 := runN_add_eq s 33 12 45 (by decide)
  let s45 := runN s 45
  have hs45eq : s45 = runN s33 12 := hrun45
  have hs45pc : s45.pc = 1527 := by rw [hs45eq]; exact hs.1
  have hs45h : s45.halted = false := by rw [hs45eq]; exact hs.2.1
  have hs45Z : s45.mem.get 0 = 0 := by rw [hs45eq]; exact hs.2.2.1
  have hs45B : s45.mem.get 33 = s.mem.get 21 := by
    rw [hs45eq, hs.2.2.2.1, hs33CH]
  have hs45I : s45.mem.get 29 = 1 := by rw [hs45eq]; exact hs.2.2.2.2.1
  have hpres45 : ∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s45.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs45eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres33 a ha18 ha30 haR ha0)
  have hONE45 : s45.mem.get 3 = 1 := (hpres45 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR45 : s45.mem.get 2319 = 3 := by
    rw [hs45eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs33R
  have hDI45 : s45.mem.get 2321 = 1 := (hpres45 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g45 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s45.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres45 (UInt16.ofNat k) n33 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s45) hs45pc hs45h hs45Z hONE45 hR45 g45
  have hrun58 : runN s 58 = runN s45 13 := runN_add_eq s 45 13 58 (by decide)
  let s58 := runN s 58
  have hs58eq : s58 = runN s45 13 := hrun58
  have hs58pc : s58.pc = 1893 := by rw [hs58eq]; exact hr.1
  have hs58h : s58.halted = false := by rw [hs58eq]; exact hr.2.1
  have hs58Z : s58.mem.get 0 = 0 := by rw [hs58eq]; exact hr.2.2.1
  have hs58I : s58.mem.get 29 = 2 := by
    rw [hs58eq, hr.2.2.2.1, hs45I]
    exact (rfl : (1 : Word) + 1 = 2)
  have hs58B : s58.mem.get 33 = s.mem.get 21 := by
    rw [hs58eq]
    exact (hr.2.2.2.2 33 (by decide) (by decide) (by decide)).trans hs45B
  have hpres58 : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s58.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs58eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres45 a haB ha18 ha30 haR ha0)
  have hONE58 : s58.mem.get 3 = 1 := (hpres58 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI58 : s58.mem.get 2321 = 1 := (hpres58 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g58 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s58.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres58 (UInt16.ofNat k) n33 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s58) hs58pc hs58h hs58Z hONE58 g58
  have hrun : s62 = runN s58 4 := runN_add_eq s 58 4 62 (by decide)
  have hsTpc : s62.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s62.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s62.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s62.mem.get 2321 = 2 := by
    rw [hrun, hn.2.2.2.1, hDI58]
    exact (rfl : (1 : Word) + 1 = 2)
  have hsTI : s62.mem.get 29 = 2 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs58I
  have hsTB : s62.mem.get 33 = s.mem.get 21 := by
    rw [hrun]; exact (hn.2.2.2.2 33 (by decide) (by decide)).trans hs58B
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s62.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres58 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 1` and `IDX = 2 < ROOM`: write `Q1`
at `BUF+2`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 64 steps. -/
theorem take_store_next_di1_idx2 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 1)
    (hI : s.mem.get 29 = 2)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s64 := runN s 64
    s64.pc = 1641 ∧
    s64.halted = false ∧
    s64.mem.get 0 = 0 ∧
    s64.mem.get 34 = s.mem.get 21 ∧
    s64.mem.get 29 = 3 ∧
    s64.mem.get 2321 = 2 ∧
    (∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s64.mem.get a = s.mem.get a) := by
  intro s64
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di1 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1824 := ht.1
  have hs12h : s12.halted = false := ht.2.1
  have hs12Z : s12.mem.get 0 = 0 := ht.2.2.1
  have hs12CH : s12.mem.get 30 = s.mem.get 21 := ht.2.2.2.1
  have hs12DI : s12.mem.get 2321 = 1 := ht.2.2.2.2.1
  have hpres12 := ht.2.2.2.2.2
  have hONE12 : s12.mem.get 3 = 1 := (hpres12 3 (by decide) (by decide) (by decide)).trans hONE
  have hI12 : s12.mem.get 29 = 2 := (hpres12 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem12 : s12.mem.get 28 = s.mem.get 28 := hpres12 28 (by decide) (by decide) (by decide)
  have hIlt : (s12.mem.get 29).toNat < (s12.mem.get 28).toNat := by
    rw [hI12, hRmem12]; simp; exact hRlo
  have hRhi' : (s12.mem.get 28).toNat < 32768 := by rw [hRmem12]; exact hRhi
  have g12 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s12.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres12 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s12) hs12pc hs12h hs12Z hONE12 hIlt hRhi' g12
  have hrun33 : runN s 33 = runN s12 21 := runN_add_eq s 12 21 33 (by decide)
  let s33 := runN s 33
  have hs33eq : s33 = runN s12 21 := hrun33
  have hs33pc : s33.pc = 1185 := by rw [hs33eq]; exact hhv.1
  have hs33h : s33.halted = false := by rw [hs33eq]; exact hhv.2.1
  have hs33Z : s33.mem.get 0 = 0 := by rw [hs33eq]; exact hhv.2.2.1
  have hs33R : s33.mem.get 2319 = 3 := by rw [hs33eq]; exact hhv.2.2.2.1
  have hs33I : s33.mem.get 29 = 2 := by
    rw [hs33eq, hhv.2.2.2.2.1, hI12]
  have hs33CH : s33.mem.get 30 = s.mem.get 21 := by
    rw [hs33eq, hhv.2.2.2.2.2.1, hs12CH]
  have hpres33 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s33.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs33eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres12 a ha18 ha30 ha0)
  have hONE33 : s33.mem.get 3 = 1 := (hpres33 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI33 : s33.mem.get 2321 = 1 := (hpres33 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g33 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s33.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres33 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx2 (s := s33) hs33pc hs33h hs33Z hONE33 hs33I g33
  have hrun47 : runN s 47 = runN s33 14 := runN_add_eq s 33 14 47 (by decide)
  let s47 := runN s 47
  have hs47eq : s47 = runN s33 14 := hrun47
  have hs47pc : s47.pc = 1527 := by rw [hs47eq]; exact hs.1
  have hs47h : s47.halted = false := by rw [hs47eq]; exact hs.2.1
  have hs47Z : s47.mem.get 0 = 0 := by rw [hs47eq]; exact hs.2.2.1
  have hs47B : s47.mem.get 34 = s.mem.get 21 := by
    rw [hs47eq, hs.2.2.2.1, hs33CH]
  have hs47I : s47.mem.get 29 = 2 := by rw [hs47eq]; exact hs.2.2.2.2.1
  have hpres47 : ∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s47.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs47eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres33 a ha18 ha30 haR ha0)
  have hONE47 : s47.mem.get 3 = 1 := (hpres47 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR47 : s47.mem.get 2319 = 3 := by
    rw [hs47eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs33R
  have hDI47 : s47.mem.get 2321 = 1 := (hpres47 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g47 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n34 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s47) hs47pc hs47h hs47Z hONE47 hR47 g47
  have hrun60 : runN s 60 = runN s47 13 := runN_add_eq s 47 13 60 (by decide)
  let s60 := runN s 60
  have hs60eq : s60 = runN s47 13 := hrun60
  have hs60pc : s60.pc = 1893 := by rw [hs60eq]; exact hr.1
  have hs60h : s60.halted = false := by rw [hs60eq]; exact hr.2.1
  have hs60Z : s60.mem.get 0 = 0 := by rw [hs60eq]; exact hr.2.2.1
  have hs60I : s60.mem.get 29 = 3 := by
    rw [hs60eq, hr.2.2.2.1, hs47I]
    exact (rfl : (2 : Word) + 1 = 3)
  have hs60B : s60.mem.get 34 = s.mem.get 21 := by
    rw [hs60eq]
    exact (hr.2.2.2.2 34 (by decide) (by decide) (by decide)).trans hs47B
  have hpres60 : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s60.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs60eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres47 a haB ha18 ha30 haR ha0)
  have hONE60 : s60.mem.get 3 = 1 := (hpres60 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI60 : s60.mem.get 2321 = 1 := (hpres60 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g60 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s60.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres60 (UInt16.ofNat k) n34 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s60) hs60pc hs60h hs60Z hONE60 g60
  have hrun : s64 = runN s60 4 := runN_add_eq s 60 4 64 (by decide)
  have hsTpc : s64.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s64.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s64.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s64.mem.get 2321 = 2 := by
    rw [hrun, hn.2.2.2.1, hDI60]
    exact (rfl : (1 : Word) + 1 = 2)
  have hsTI : s64.mem.get 29 = 3 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs60I
  have hsTB : s64.mem.get 34 = s.mem.get 21 := by
    rw [hrun]; exact (hn.2.2.2.2 34 (by decide) (by decide)).trans hs60B
  have hpres : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s64.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres60 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 1` and `IDX = 3 < ROOM`: write `Q1`
at `BUF+3`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 66 steps. -/
theorem take_store_next_di1_idx3 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 1)
    (hI : s.mem.get 29 = 3)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s66 := runN s 66
    s66.pc = 1641 ∧
    s66.halted = false ∧
    s66.mem.get 0 = 0 ∧
    s66.mem.get 35 = s.mem.get 21 ∧
    s66.mem.get 29 = 4 ∧
    s66.mem.get 2321 = 2 ∧
    (∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s66.mem.get a = s.mem.get a) := by
  intro s66
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di1 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1824 := ht.1
  have hs12h : s12.halted = false := ht.2.1
  have hs12Z : s12.mem.get 0 = 0 := ht.2.2.1
  have hs12CH : s12.mem.get 30 = s.mem.get 21 := ht.2.2.2.1
  have hs12DI : s12.mem.get 2321 = 1 := ht.2.2.2.2.1
  have hpres12 := ht.2.2.2.2.2
  have hONE12 : s12.mem.get 3 = 1 := (hpres12 3 (by decide) (by decide) (by decide)).trans hONE
  have hI12 : s12.mem.get 29 = 3 := (hpres12 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem12 : s12.mem.get 28 = s.mem.get 28 := hpres12 28 (by decide) (by decide) (by decide)
  have hIlt : (s12.mem.get 29).toNat < (s12.mem.get 28).toNat := by
    rw [hI12, hRmem12]; simp; exact hRlo
  have hRhi' : (s12.mem.get 28).toNat < 32768 := by rw [hRmem12]; exact hRhi
  have g12 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s12.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres12 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s12) hs12pc hs12h hs12Z hONE12 hIlt hRhi' g12
  have hrun33 : runN s 33 = runN s12 21 := runN_add_eq s 12 21 33 (by decide)
  let s33 := runN s 33
  have hs33eq : s33 = runN s12 21 := hrun33
  have hs33pc : s33.pc = 1185 := by rw [hs33eq]; exact hhv.1
  have hs33h : s33.halted = false := by rw [hs33eq]; exact hhv.2.1
  have hs33Z : s33.mem.get 0 = 0 := by rw [hs33eq]; exact hhv.2.2.1
  have hs33R : s33.mem.get 2319 = 3 := by rw [hs33eq]; exact hhv.2.2.2.1
  have hs33I : s33.mem.get 29 = 3 := by
    rw [hs33eq, hhv.2.2.2.2.1, hI12]
  have hs33CH : s33.mem.get 30 = s.mem.get 21 := by
    rw [hs33eq, hhv.2.2.2.2.2.1, hs12CH]
  have hpres33 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s33.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs33eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres12 a ha18 ha30 ha0)
  have hONE33 : s33.mem.get 3 = 1 := (hpres33 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI33 : s33.mem.get 2321 = 1 := (hpres33 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g33 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s33.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres33 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx3 (s := s33) hs33pc hs33h hs33Z hONE33 hs33I g33
  have hrun49 : runN s 49 = runN s33 16 := runN_add_eq s 33 16 49 (by decide)
  let s49 := runN s 49
  have hs49eq : s49 = runN s33 16 := hrun49
  have hs49pc : s49.pc = 1527 := by rw [hs49eq]; exact hs.1
  have hs49h : s49.halted = false := by rw [hs49eq]; exact hs.2.1
  have hs49Z : s49.mem.get 0 = 0 := by rw [hs49eq]; exact hs.2.2.1
  have hs49B : s49.mem.get 35 = s.mem.get 21 := by
    rw [hs49eq, hs.2.2.2.1, hs33CH]
  have hs49I : s49.mem.get 29 = 3 := by rw [hs49eq]; exact hs.2.2.2.2.1
  have hpres49 : ∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s49.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs49eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres33 a ha18 ha30 haR ha0)
  have hONE49 : s49.mem.get 3 = 1 := (hpres49 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR49 : s49.mem.get 2319 = 3 := by
    rw [hs49eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs33R
  have hDI49 : s49.mem.get 2321 = 1 := (hpres49 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g49 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s49.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres49 (UInt16.ofNat k) n35 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s49) hs49pc hs49h hs49Z hONE49 hR49 g49
  have hrun62 : runN s 62 = runN s49 13 := runN_add_eq s 49 13 62 (by decide)
  let s62 := runN s 62
  have hs62eq : s62 = runN s49 13 := hrun62
  have hs62pc : s62.pc = 1893 := by rw [hs62eq]; exact hr.1
  have hs62h : s62.halted = false := by rw [hs62eq]; exact hr.2.1
  have hs62Z : s62.mem.get 0 = 0 := by rw [hs62eq]; exact hr.2.2.1
  have hs62I : s62.mem.get 29 = 4 := by
    rw [hs62eq, hr.2.2.2.1, hs49I]
    exact (rfl : (3 : Word) + 1 = 4)
  have hs62B : s62.mem.get 35 = s.mem.get 21 := by
    rw [hs62eq]
    exact (hr.2.2.2.2 35 (by decide) (by decide) (by decide)).trans hs49B
  have hpres62 : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s62.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs62eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres49 a haB ha18 ha30 haR ha0)
  have hONE62 : s62.mem.get 3 = 1 := (hpres62 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI62 : s62.mem.get 2321 = 1 := (hpres62 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g62 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s62.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres62 (UInt16.ofNat k) n35 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s62) hs62pc hs62h hs62Z hONE62 g62
  have hrun : s66 = runN s62 4 := runN_add_eq s 62 4 66 (by decide)
  have hsTpc : s66.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s66.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s66.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s66.mem.get 2321 = 2 := by
    rw [hrun, hn.2.2.2.1, hDI62]
    exact (rfl : (1 : Word) + 1 = 2)
  have hsTI : s66.mem.get 29 = 4 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs62I
  have hsTB : s66.mem.get 35 = s.mem.get 21 := by
    rw [hrun]; exact (hn.2.2.2.2 35 (by decide) (by decide)).trans hs62B
  have hpres : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s66.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres62 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 1` and `IDX = 4 < ROOM`: write `Q1`
at `BUF+4`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 68 steps. -/
theorem take_store_next_di1_idx4 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 1)
    (hI : s.mem.get 29 = 4)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s68 := runN s 68
    s68.pc = 1641 ∧
    s68.halted = false ∧
    s68.mem.get 0 = 0 ∧
    s68.mem.get 36 = s.mem.get 21 ∧
    s68.mem.get 29 = 5 ∧
    s68.mem.get 2321 = 2 ∧
    (∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s68.mem.get a = s.mem.get a) := by
  intro s68
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di1 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1824 := ht.1
  have hs12h : s12.halted = false := ht.2.1
  have hs12Z : s12.mem.get 0 = 0 := ht.2.2.1
  have hs12CH : s12.mem.get 30 = s.mem.get 21 := ht.2.2.2.1
  have hs12DI : s12.mem.get 2321 = 1 := ht.2.2.2.2.1
  have hpres12 := ht.2.2.2.2.2
  have hONE12 : s12.mem.get 3 = 1 := (hpres12 3 (by decide) (by decide) (by decide)).trans hONE
  have hI12 : s12.mem.get 29 = 4 := (hpres12 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem12 : s12.mem.get 28 = s.mem.get 28 := hpres12 28 (by decide) (by decide) (by decide)
  have hIlt : (s12.mem.get 29).toNat < (s12.mem.get 28).toNat := by
    rw [hI12, hRmem12]; simp; exact hRlo
  have hRhi' : (s12.mem.get 28).toNat < 32768 := by rw [hRmem12]; exact hRhi
  have g12 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s12.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres12 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s12) hs12pc hs12h hs12Z hONE12 hIlt hRhi' g12
  have hrun33 : runN s 33 = runN s12 21 := runN_add_eq s 12 21 33 (by decide)
  let s33 := runN s 33
  have hs33eq : s33 = runN s12 21 := hrun33
  have hs33pc : s33.pc = 1185 := by rw [hs33eq]; exact hhv.1
  have hs33h : s33.halted = false := by rw [hs33eq]; exact hhv.2.1
  have hs33Z : s33.mem.get 0 = 0 := by rw [hs33eq]; exact hhv.2.2.1
  have hs33R : s33.mem.get 2319 = 3 := by rw [hs33eq]; exact hhv.2.2.2.1
  have hs33I : s33.mem.get 29 = 4 := by
    rw [hs33eq, hhv.2.2.2.2.1, hI12]
  have hs33CH : s33.mem.get 30 = s.mem.get 21 := by
    rw [hs33eq, hhv.2.2.2.2.2.1, hs12CH]
  have hpres33 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s33.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs33eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres12 a ha18 ha30 ha0)
  have hONE33 : s33.mem.get 3 = 1 := (hpres33 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI33 : s33.mem.get 2321 = 1 := (hpres33 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g33 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s33.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres33 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx4 (s := s33) hs33pc hs33h hs33Z hONE33 hs33I g33
  have hrun51 : runN s 51 = runN s33 18 := runN_add_eq s 33 18 51 (by decide)
  let s51 := runN s 51
  have hs51eq : s51 = runN s33 18 := hrun51
  have hs51pc : s51.pc = 1527 := by rw [hs51eq]; exact hs.1
  have hs51h : s51.halted = false := by rw [hs51eq]; exact hs.2.1
  have hs51Z : s51.mem.get 0 = 0 := by rw [hs51eq]; exact hs.2.2.1
  have hs51B : s51.mem.get 36 = s.mem.get 21 := by
    rw [hs51eq, hs.2.2.2.1, hs33CH]
  have hs51I : s51.mem.get 29 = 4 := by rw [hs51eq]; exact hs.2.2.2.2.1
  have hpres51 : ∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s51.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs51eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres33 a ha18 ha30 haR ha0)
  have hONE51 : s51.mem.get 3 = 1 := (hpres51 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR51 : s51.mem.get 2319 = 3 := by
    rw [hs51eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs33R
  have hDI51 : s51.mem.get 2321 = 1 := (hpres51 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g51 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s51.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres51 (UInt16.ofNat k) n36 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s51) hs51pc hs51h hs51Z hONE51 hR51 g51
  have hrun64 : runN s 64 = runN s51 13 := runN_add_eq s 51 13 64 (by decide)
  let s64 := runN s 64
  have hs64eq : s64 = runN s51 13 := hrun64
  have hs64pc : s64.pc = 1893 := by rw [hs64eq]; exact hr.1
  have hs64h : s64.halted = false := by rw [hs64eq]; exact hr.2.1
  have hs64Z : s64.mem.get 0 = 0 := by rw [hs64eq]; exact hr.2.2.1
  have hs64I : s64.mem.get 29 = 5 := by
    rw [hs64eq, hr.2.2.2.1, hs51I]
    exact (rfl : (4 : Word) + 1 = 5)
  have hs64B : s64.mem.get 36 = s.mem.get 21 := by
    rw [hs64eq]
    exact (hr.2.2.2.2 36 (by decide) (by decide) (by decide)).trans hs51B
  have hpres64 : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s64.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs64eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres51 a haB ha18 ha30 haR ha0)
  have hONE64 : s64.mem.get 3 = 1 := (hpres64 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI64 : s64.mem.get 2321 = 1 := (hpres64 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g64 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s64.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres64 (UInt16.ofNat k) n36 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s64) hs64pc hs64h hs64Z hONE64 g64
  have hrun : s68 = runN s64 4 := runN_add_eq s 64 4 68 (by decide)
  have hsTpc : s68.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s68.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s68.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s68.mem.get 2321 = 2 := by
    rw [hrun, hn.2.2.2.1, hDI64]
    exact (rfl : (1 : Word) + 1 = 2)
  have hsTI : s68.mem.get 29 = 5 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs64I
  have hsTB : s68.mem.get 36 = s.mem.get 21 := by
    rw [hrun]; exact (hn.2.2.2.2 36 (by decide) (by decide)).trans hs64B
  have hpres : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s68.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres64 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 1` and `IDX = 5 < ROOM`: write `Q1`
at `BUF+5`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 70 steps. -/
theorem take_store_next_di1_idx5 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 1)
    (hI : s.mem.get 29 = 5)
    (hRlo : 5 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s70 := runN s 70
    s70.pc = 1641 ∧
    s70.halted = false ∧
    s70.mem.get 0 = 0 ∧
    s70.mem.get 37 = s.mem.get 21 ∧
    s70.mem.get 29 = 6 ∧
    s70.mem.get 2321 = 2 ∧
    (∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s70.mem.get a = s.mem.get a) := by
  intro s70
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di1 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1824 := ht.1
  have hs12h : s12.halted = false := ht.2.1
  have hs12Z : s12.mem.get 0 = 0 := ht.2.2.1
  have hs12CH : s12.mem.get 30 = s.mem.get 21 := ht.2.2.2.1
  have hs12DI : s12.mem.get 2321 = 1 := ht.2.2.2.2.1
  have hpres12 := ht.2.2.2.2.2
  have hONE12 : s12.mem.get 3 = 1 := (hpres12 3 (by decide) (by decide) (by decide)).trans hONE
  have hI12 : s12.mem.get 29 = 5 := (hpres12 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem12 : s12.mem.get 28 = s.mem.get 28 := hpres12 28 (by decide) (by decide) (by decide)
  have hIlt : (s12.mem.get 29).toNat < (s12.mem.get 28).toNat := by
    rw [hI12, hRmem12]; simp; exact hRlo
  have hRhi' : (s12.mem.get 28).toNat < 32768 := by rw [hRmem12]; exact hRhi
  have g12 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s12.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres12 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s12) hs12pc hs12h hs12Z hONE12 hIlt hRhi' g12
  have hrun33 : runN s 33 = runN s12 21 := runN_add_eq s 12 21 33 (by decide)
  let s33 := runN s 33
  have hs33eq : s33 = runN s12 21 := hrun33
  have hs33pc : s33.pc = 1185 := by rw [hs33eq]; exact hhv.1
  have hs33h : s33.halted = false := by rw [hs33eq]; exact hhv.2.1
  have hs33Z : s33.mem.get 0 = 0 := by rw [hs33eq]; exact hhv.2.2.1
  have hs33R : s33.mem.get 2319 = 3 := by rw [hs33eq]; exact hhv.2.2.2.1
  have hs33I : s33.mem.get 29 = 5 := by
    rw [hs33eq, hhv.2.2.2.2.1, hI12]
  have hs33CH : s33.mem.get 30 = s.mem.get 21 := by
    rw [hs33eq, hhv.2.2.2.2.2.1, hs12CH]
  have hpres33 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s33.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs33eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres12 a ha18 ha30 ha0)
  have hONE33 : s33.mem.get 3 = 1 := (hpres33 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI33 : s33.mem.get 2321 = 1 := (hpres33 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g33 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s33.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres33 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx5 (s := s33) hs33pc hs33h hs33Z hONE33 hs33I g33
  have hrun53 : runN s 53 = runN s33 20 := runN_add_eq s 33 20 53 (by decide)
  let s53 := runN s 53
  have hs53eq : s53 = runN s33 20 := hrun53
  have hs53pc : s53.pc = 1527 := by rw [hs53eq]; exact hs.1
  have hs53h : s53.halted = false := by rw [hs53eq]; exact hs.2.1
  have hs53Z : s53.mem.get 0 = 0 := by rw [hs53eq]; exact hs.2.2.1
  have hs53B : s53.mem.get 37 = s.mem.get 21 := by
    rw [hs53eq, hs.2.2.2.1, hs33CH]
  have hs53I : s53.mem.get 29 = 5 := by rw [hs53eq]; exact hs.2.2.2.2.1
  have hpres53 : ∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s53.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs53eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres33 a ha18 ha30 haR ha0)
  have hONE53 : s53.mem.get 3 = 1 := (hpres53 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR53 : s53.mem.get 2319 = 3 := by
    rw [hs53eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs33R
  have hDI53 : s53.mem.get 2321 = 1 := (hpres53 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g53 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s53.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres53 (UInt16.ofNat k) n37 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s53) hs53pc hs53h hs53Z hONE53 hR53 g53
  have hrun66 : runN s 66 = runN s53 13 := runN_add_eq s 53 13 66 (by decide)
  let s66 := runN s 66
  have hs66eq : s66 = runN s53 13 := hrun66
  have hs66pc : s66.pc = 1893 := by rw [hs66eq]; exact hr.1
  have hs66h : s66.halted = false := by rw [hs66eq]; exact hr.2.1
  have hs66Z : s66.mem.get 0 = 0 := by rw [hs66eq]; exact hr.2.2.1
  have hs66I : s66.mem.get 29 = 6 := by
    rw [hs66eq, hr.2.2.2.1, hs53I]
    exact (rfl : (5 : Word) + 1 = 6)
  have hs66B : s66.mem.get 37 = s.mem.get 21 := by
    rw [hs66eq]
    exact (hr.2.2.2.2 37 (by decide) (by decide) (by decide)).trans hs53B
  have hpres66 : ∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s66.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs66eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres53 a haB ha18 ha30 haR ha0)
  have hONE66 : s66.mem.get 3 = 1 := (hpres66 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI66 : s66.mem.get 2321 = 1 := (hpres66 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g66 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s66.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres66 (UInt16.ofNat k) n37 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s66) hs66pc hs66h hs66Z hONE66 g66
  have hrun : s70 = runN s66 4 := runN_add_eq s 66 4 70 (by decide)
  have hsTpc : s70.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s70.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s70.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s70.mem.get 2321 = 2 := by
    rw [hrun, hn.2.2.2.1, hDI66]
    exact (rfl : (1 : Word) + 1 = 2)
  have hsTI : s70.mem.get 29 = 6 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs66I
  have hsTB : s70.mem.get 37 = s.mem.get 21 := by
    rw [hrun]; exact (hn.2.2.2.2 37 (by decide) (by decide)).trans hs66B
  have hpres : ∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s70.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres66 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 2` and `IDX = 0 < ROOM`: write `Q2`
at `BUF+0`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 62 steps. -/
theorem take_store_next_di2_idx0 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 2)
    (hI : s.mem.get 29 = 0)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s62 := runN s 62
    s62.pc = 1641 ∧
    s62.halted = false ∧
    s62.mem.get 0 = 0 ∧
    s62.mem.get 32 = s.mem.get 22 ∧
    s62.mem.get 29 = 1 ∧
    s62.mem.get 2321 = 3 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s62.mem.get a = s.mem.get a) := by
  intro s62
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di2 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1824 := ht.1
  have hs14h : s14.halted = false := ht.2.1
  have hs14Z : s14.mem.get 0 = 0 := ht.2.2.1
  have hs14CH : s14.mem.get 30 = s.mem.get 22 := ht.2.2.2.1
  have hs14DI : s14.mem.get 2321 = 2 := ht.2.2.2.2.1
  have hpres14 := ht.2.2.2.2.2
  have hONE14 : s14.mem.get 3 = 1 := (hpres14 3 (by decide) (by decide) (by decide)).trans hONE
  have hI14 : s14.mem.get 29 = 0 := (hpres14 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem14 : s14.mem.get 28 = s.mem.get 28 := hpres14 28 (by decide) (by decide) (by decide)
  have hIlt : (s14.mem.get 29).toNat < (s14.mem.get 28).toNat := by
    rw [hI14, hRmem14]; simp; exact hRlo
  have hRhi' : (s14.mem.get 28).toNat < 32768 := by rw [hRmem14]; exact hRhi
  have g14 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s14.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres14 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s14) hs14pc hs14h hs14Z hONE14 hIlt hRhi' g14
  have hrun35 : runN s 35 = runN s14 21 := runN_add_eq s 14 21 35 (by decide)
  let s35 := runN s 35
  have hs35eq : s35 = runN s14 21 := hrun35
  have hs35pc : s35.pc = 1185 := by rw [hs35eq]; exact hhv.1
  have hs35h : s35.halted = false := by rw [hs35eq]; exact hhv.2.1
  have hs35Z : s35.mem.get 0 = 0 := by rw [hs35eq]; exact hhv.2.2.1
  have hs35R : s35.mem.get 2319 = 3 := by rw [hs35eq]; exact hhv.2.2.2.1
  have hs35I : s35.mem.get 29 = 0 := by
    rw [hs35eq, hhv.2.2.2.2.1, hI14]
  have hs35CH : s35.mem.get 30 = s.mem.get 22 := by
    rw [hs35eq, hhv.2.2.2.2.2.1, hs14CH]
  have hpres35 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s35.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs35eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres14 a ha18 ha30 ha0)
  have hONE35 : s35.mem.get 3 = 1 := (hpres35 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI35 : s35.mem.get 2321 = 2 := (hpres35 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g35a : ∀ k : Nat, 1185 ≤ k → k < 1200 →
      s35.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres35 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have g35b : ∀ k : Nat, 1287 ≤ k → k < 1302 →
      s35.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres35 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx0 (s := s35) hs35pc hs35h hs35Z hs35I g35a g35b
  have hrun45 : runN s 45 = runN s35 10 := runN_add_eq s 35 10 45 (by decide)
  let s45 := runN s 45
  have hs45eq : s45 = runN s35 10 := hrun45
  have hs45pc : s45.pc = 1527 := by rw [hs45eq]; exact hs.1
  have hs45h : s45.halted = false := by rw [hs45eq]; exact hs.2.1
  have hs45Z : s45.mem.get 0 = 0 := by rw [hs45eq]; exact hs.2.2.1
  have hs45B : s45.mem.get 32 = s.mem.get 22 := by
    rw [hs45eq, hs.2.2.2.1, hs35CH]
  have hs45I : s45.mem.get 29 = 0 := by rw [hs45eq]; exact hs.2.2.2.2.1
  have hpres45 : ∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s45.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs45eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres35 a ha18 ha30 haR ha0)
  have hONE45 : s45.mem.get 3 = 1 := (hpres45 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR45 : s45.mem.get 2319 = 3 := by
    rw [hs45eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs35R
  have hDI45 : s45.mem.get 2321 = 2 := (hpres45 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g45 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s45.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres45 (UInt16.ofNat k) n32 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s45) hs45pc hs45h hs45Z hONE45 hR45 g45
  have hrun58 : runN s 58 = runN s45 13 := runN_add_eq s 45 13 58 (by decide)
  let s58 := runN s 58
  have hs58eq : s58 = runN s45 13 := hrun58
  have hs58pc : s58.pc = 1893 := by rw [hs58eq]; exact hr.1
  have hs58h : s58.halted = false := by rw [hs58eq]; exact hr.2.1
  have hs58Z : s58.mem.get 0 = 0 := by rw [hs58eq]; exact hr.2.2.1
  have hs58I : s58.mem.get 29 = 1 := by
    rw [hs58eq, hr.2.2.2.1, hs45I]
    exact (rfl : (0 : Word) + 1 = 1)
  have hs58B : s58.mem.get 32 = s.mem.get 22 := by
    rw [hs58eq]
    exact (hr.2.2.2.2 32 (by decide) (by decide) (by decide)).trans hs45B
  have hpres58 : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s58.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs58eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres45 a haB ha18 ha30 haR ha0)
  have hONE58 : s58.mem.get 3 = 1 := (hpres58 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI58 : s58.mem.get 2321 = 2 := (hpres58 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g58 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s58.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres58 (UInt16.ofNat k) n32 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s58) hs58pc hs58h hs58Z hONE58 g58
  have hrun : s62 = runN s58 4 := runN_add_eq s 58 4 62 (by decide)
  have hsTpc : s62.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s62.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s62.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s62.mem.get 2321 = 3 := by
    rw [hrun, hn.2.2.2.1, hDI58]
    exact (rfl : (2 : Word) + 1 = 3)
  have hsTI : s62.mem.get 29 = 1 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs58I
  have hsTB : s62.mem.get 32 = s.mem.get 22 := by
    rw [hrun]; exact (hn.2.2.2.2 32 (by decide) (by decide)).trans hs58B
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s62.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres58 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 2` and `IDX = 1 < ROOM`: write `Q2`
at `BUF+1`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 64 steps. -/
theorem take_store_next_di2_idx1 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 2)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s64 := runN s 64
    s64.pc = 1641 ∧
    s64.halted = false ∧
    s64.mem.get 0 = 0 ∧
    s64.mem.get 33 = s.mem.get 22 ∧
    s64.mem.get 29 = 2 ∧
    s64.mem.get 2321 = 3 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s64.mem.get a = s.mem.get a) := by
  intro s64
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di2 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1824 := ht.1
  have hs14h : s14.halted = false := ht.2.1
  have hs14Z : s14.mem.get 0 = 0 := ht.2.2.1
  have hs14CH : s14.mem.get 30 = s.mem.get 22 := ht.2.2.2.1
  have hs14DI : s14.mem.get 2321 = 2 := ht.2.2.2.2.1
  have hpres14 := ht.2.2.2.2.2
  have hONE14 : s14.mem.get 3 = 1 := (hpres14 3 (by decide) (by decide) (by decide)).trans hONE
  have hI14 : s14.mem.get 29 = 1 := (hpres14 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem14 : s14.mem.get 28 = s.mem.get 28 := hpres14 28 (by decide) (by decide) (by decide)
  have hIlt : (s14.mem.get 29).toNat < (s14.mem.get 28).toNat := by
    rw [hI14, hRmem14]; simp; exact hRlo
  have hRhi' : (s14.mem.get 28).toNat < 32768 := by rw [hRmem14]; exact hRhi
  have g14 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s14.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres14 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s14) hs14pc hs14h hs14Z hONE14 hIlt hRhi' g14
  have hrun35 : runN s 35 = runN s14 21 := runN_add_eq s 14 21 35 (by decide)
  let s35 := runN s 35
  have hs35eq : s35 = runN s14 21 := hrun35
  have hs35pc : s35.pc = 1185 := by rw [hs35eq]; exact hhv.1
  have hs35h : s35.halted = false := by rw [hs35eq]; exact hhv.2.1
  have hs35Z : s35.mem.get 0 = 0 := by rw [hs35eq]; exact hhv.2.2.1
  have hs35R : s35.mem.get 2319 = 3 := by rw [hs35eq]; exact hhv.2.2.2.1
  have hs35I : s35.mem.get 29 = 1 := by
    rw [hs35eq, hhv.2.2.2.2.1, hI14]
  have hs35CH : s35.mem.get 30 = s.mem.get 22 := by
    rw [hs35eq, hhv.2.2.2.2.2.1, hs14CH]
  have hpres35 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s35.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs35eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres14 a ha18 ha30 ha0)
  have hONE35 : s35.mem.get 3 = 1 := (hpres35 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI35 : s35.mem.get 2321 = 2 := (hpres35 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g35 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s35.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres35 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx1 (s := s35) hs35pc hs35h hs35Z hONE35 hs35I g35
  have hrun47 : runN s 47 = runN s35 12 := runN_add_eq s 35 12 47 (by decide)
  let s47 := runN s 47
  have hs47eq : s47 = runN s35 12 := hrun47
  have hs47pc : s47.pc = 1527 := by rw [hs47eq]; exact hs.1
  have hs47h : s47.halted = false := by rw [hs47eq]; exact hs.2.1
  have hs47Z : s47.mem.get 0 = 0 := by rw [hs47eq]; exact hs.2.2.1
  have hs47B : s47.mem.get 33 = s.mem.get 22 := by
    rw [hs47eq, hs.2.2.2.1, hs35CH]
  have hs47I : s47.mem.get 29 = 1 := by rw [hs47eq]; exact hs.2.2.2.2.1
  have hpres47 : ∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s47.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs47eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres35 a ha18 ha30 haR ha0)
  have hONE47 : s47.mem.get 3 = 1 := (hpres47 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR47 : s47.mem.get 2319 = 3 := by
    rw [hs47eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs35R
  have hDI47 : s47.mem.get 2321 = 2 := (hpres47 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g47 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n33 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s47) hs47pc hs47h hs47Z hONE47 hR47 g47
  have hrun60 : runN s 60 = runN s47 13 := runN_add_eq s 47 13 60 (by decide)
  let s60 := runN s 60
  have hs60eq : s60 = runN s47 13 := hrun60
  have hs60pc : s60.pc = 1893 := by rw [hs60eq]; exact hr.1
  have hs60h : s60.halted = false := by rw [hs60eq]; exact hr.2.1
  have hs60Z : s60.mem.get 0 = 0 := by rw [hs60eq]; exact hr.2.2.1
  have hs60I : s60.mem.get 29 = 2 := by
    rw [hs60eq, hr.2.2.2.1, hs47I]
    exact (rfl : (1 : Word) + 1 = 2)
  have hs60B : s60.mem.get 33 = s.mem.get 22 := by
    rw [hs60eq]
    exact (hr.2.2.2.2 33 (by decide) (by decide) (by decide)).trans hs47B
  have hpres60 : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s60.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs60eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres47 a haB ha18 ha30 haR ha0)
  have hONE60 : s60.mem.get 3 = 1 := (hpres60 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI60 : s60.mem.get 2321 = 2 := (hpres60 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g60 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s60.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres60 (UInt16.ofNat k) n33 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s60) hs60pc hs60h hs60Z hONE60 g60
  have hrun : s64 = runN s60 4 := runN_add_eq s 60 4 64 (by decide)
  have hsTpc : s64.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s64.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s64.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s64.mem.get 2321 = 3 := by
    rw [hrun, hn.2.2.2.1, hDI60]
    exact (rfl : (2 : Word) + 1 = 3)
  have hsTI : s64.mem.get 29 = 2 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs60I
  have hsTB : s64.mem.get 33 = s.mem.get 22 := by
    rw [hrun]; exact (hn.2.2.2.2 33 (by decide) (by decide)).trans hs60B
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s64.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres60 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 2` and `IDX = 2 < ROOM`: write `Q2`
at `BUF+2`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 66 steps. -/
theorem take_store_next_di2_idx2 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 2)
    (hI : s.mem.get 29 = 2)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s66 := runN s 66
    s66.pc = 1641 ∧
    s66.halted = false ∧
    s66.mem.get 0 = 0 ∧
    s66.mem.get 34 = s.mem.get 22 ∧
    s66.mem.get 29 = 3 ∧
    s66.mem.get 2321 = 3 ∧
    (∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s66.mem.get a = s.mem.get a) := by
  intro s66
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di2 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1824 := ht.1
  have hs14h : s14.halted = false := ht.2.1
  have hs14Z : s14.mem.get 0 = 0 := ht.2.2.1
  have hs14CH : s14.mem.get 30 = s.mem.get 22 := ht.2.2.2.1
  have hs14DI : s14.mem.get 2321 = 2 := ht.2.2.2.2.1
  have hpres14 := ht.2.2.2.2.2
  have hONE14 : s14.mem.get 3 = 1 := (hpres14 3 (by decide) (by decide) (by decide)).trans hONE
  have hI14 : s14.mem.get 29 = 2 := (hpres14 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem14 : s14.mem.get 28 = s.mem.get 28 := hpres14 28 (by decide) (by decide) (by decide)
  have hIlt : (s14.mem.get 29).toNat < (s14.mem.get 28).toNat := by
    rw [hI14, hRmem14]; simp; exact hRlo
  have hRhi' : (s14.mem.get 28).toNat < 32768 := by rw [hRmem14]; exact hRhi
  have g14 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s14.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres14 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s14) hs14pc hs14h hs14Z hONE14 hIlt hRhi' g14
  have hrun35 : runN s 35 = runN s14 21 := runN_add_eq s 14 21 35 (by decide)
  let s35 := runN s 35
  have hs35eq : s35 = runN s14 21 := hrun35
  have hs35pc : s35.pc = 1185 := by rw [hs35eq]; exact hhv.1
  have hs35h : s35.halted = false := by rw [hs35eq]; exact hhv.2.1
  have hs35Z : s35.mem.get 0 = 0 := by rw [hs35eq]; exact hhv.2.2.1
  have hs35R : s35.mem.get 2319 = 3 := by rw [hs35eq]; exact hhv.2.2.2.1
  have hs35I : s35.mem.get 29 = 2 := by
    rw [hs35eq, hhv.2.2.2.2.1, hI14]
  have hs35CH : s35.mem.get 30 = s.mem.get 22 := by
    rw [hs35eq, hhv.2.2.2.2.2.1, hs14CH]
  have hpres35 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s35.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs35eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres14 a ha18 ha30 ha0)
  have hONE35 : s35.mem.get 3 = 1 := (hpres35 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI35 : s35.mem.get 2321 = 2 := (hpres35 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g35 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s35.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres35 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx2 (s := s35) hs35pc hs35h hs35Z hONE35 hs35I g35
  have hrun49 : runN s 49 = runN s35 14 := runN_add_eq s 35 14 49 (by decide)
  let s49 := runN s 49
  have hs49eq : s49 = runN s35 14 := hrun49
  have hs49pc : s49.pc = 1527 := by rw [hs49eq]; exact hs.1
  have hs49h : s49.halted = false := by rw [hs49eq]; exact hs.2.1
  have hs49Z : s49.mem.get 0 = 0 := by rw [hs49eq]; exact hs.2.2.1
  have hs49B : s49.mem.get 34 = s.mem.get 22 := by
    rw [hs49eq, hs.2.2.2.1, hs35CH]
  have hs49I : s49.mem.get 29 = 2 := by rw [hs49eq]; exact hs.2.2.2.2.1
  have hpres49 : ∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s49.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs49eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres35 a ha18 ha30 haR ha0)
  have hONE49 : s49.mem.get 3 = 1 := (hpres49 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR49 : s49.mem.get 2319 = 3 := by
    rw [hs49eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs35R
  have hDI49 : s49.mem.get 2321 = 2 := (hpres49 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g49 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s49.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres49 (UInt16.ofNat k) n34 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s49) hs49pc hs49h hs49Z hONE49 hR49 g49
  have hrun62 : runN s 62 = runN s49 13 := runN_add_eq s 49 13 62 (by decide)
  let s62 := runN s 62
  have hs62eq : s62 = runN s49 13 := hrun62
  have hs62pc : s62.pc = 1893 := by rw [hs62eq]; exact hr.1
  have hs62h : s62.halted = false := by rw [hs62eq]; exact hr.2.1
  have hs62Z : s62.mem.get 0 = 0 := by rw [hs62eq]; exact hr.2.2.1
  have hs62I : s62.mem.get 29 = 3 := by
    rw [hs62eq, hr.2.2.2.1, hs49I]
    exact (rfl : (2 : Word) + 1 = 3)
  have hs62B : s62.mem.get 34 = s.mem.get 22 := by
    rw [hs62eq]
    exact (hr.2.2.2.2 34 (by decide) (by decide) (by decide)).trans hs49B
  have hpres62 : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s62.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs62eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres49 a haB ha18 ha30 haR ha0)
  have hONE62 : s62.mem.get 3 = 1 := (hpres62 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI62 : s62.mem.get 2321 = 2 := (hpres62 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g62 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s62.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres62 (UInt16.ofNat k) n34 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s62) hs62pc hs62h hs62Z hONE62 g62
  have hrun : s66 = runN s62 4 := runN_add_eq s 62 4 66 (by decide)
  have hsTpc : s66.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s66.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s66.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s66.mem.get 2321 = 3 := by
    rw [hrun, hn.2.2.2.1, hDI62]
    exact (rfl : (2 : Word) + 1 = 3)
  have hsTI : s66.mem.get 29 = 3 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs62I
  have hsTB : s66.mem.get 34 = s.mem.get 22 := by
    rw [hrun]; exact (hn.2.2.2.2 34 (by decide) (by decide)).trans hs62B
  have hpres : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s66.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres62 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 2` and `IDX = 3 < ROOM`: write `Q2`
at `BUF+3`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 68 steps. -/
theorem take_store_next_di2_idx3 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 2)
    (hI : s.mem.get 29 = 3)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s68 := runN s 68
    s68.pc = 1641 ∧
    s68.halted = false ∧
    s68.mem.get 0 = 0 ∧
    s68.mem.get 35 = s.mem.get 22 ∧
    s68.mem.get 29 = 4 ∧
    s68.mem.get 2321 = 3 ∧
    (∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s68.mem.get a = s.mem.get a) := by
  intro s68
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di2 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1824 := ht.1
  have hs14h : s14.halted = false := ht.2.1
  have hs14Z : s14.mem.get 0 = 0 := ht.2.2.1
  have hs14CH : s14.mem.get 30 = s.mem.get 22 := ht.2.2.2.1
  have hs14DI : s14.mem.get 2321 = 2 := ht.2.2.2.2.1
  have hpres14 := ht.2.2.2.2.2
  have hONE14 : s14.mem.get 3 = 1 := (hpres14 3 (by decide) (by decide) (by decide)).trans hONE
  have hI14 : s14.mem.get 29 = 3 := (hpres14 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem14 : s14.mem.get 28 = s.mem.get 28 := hpres14 28 (by decide) (by decide) (by decide)
  have hIlt : (s14.mem.get 29).toNat < (s14.mem.get 28).toNat := by
    rw [hI14, hRmem14]; simp; exact hRlo
  have hRhi' : (s14.mem.get 28).toNat < 32768 := by rw [hRmem14]; exact hRhi
  have g14 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s14.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres14 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s14) hs14pc hs14h hs14Z hONE14 hIlt hRhi' g14
  have hrun35 : runN s 35 = runN s14 21 := runN_add_eq s 14 21 35 (by decide)
  let s35 := runN s 35
  have hs35eq : s35 = runN s14 21 := hrun35
  have hs35pc : s35.pc = 1185 := by rw [hs35eq]; exact hhv.1
  have hs35h : s35.halted = false := by rw [hs35eq]; exact hhv.2.1
  have hs35Z : s35.mem.get 0 = 0 := by rw [hs35eq]; exact hhv.2.2.1
  have hs35R : s35.mem.get 2319 = 3 := by rw [hs35eq]; exact hhv.2.2.2.1
  have hs35I : s35.mem.get 29 = 3 := by
    rw [hs35eq, hhv.2.2.2.2.1, hI14]
  have hs35CH : s35.mem.get 30 = s.mem.get 22 := by
    rw [hs35eq, hhv.2.2.2.2.2.1, hs14CH]
  have hpres35 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s35.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs35eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres14 a ha18 ha30 ha0)
  have hONE35 : s35.mem.get 3 = 1 := (hpres35 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI35 : s35.mem.get 2321 = 2 := (hpres35 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g35 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s35.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres35 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx3 (s := s35) hs35pc hs35h hs35Z hONE35 hs35I g35
  have hrun51 : runN s 51 = runN s35 16 := runN_add_eq s 35 16 51 (by decide)
  let s51 := runN s 51
  have hs51eq : s51 = runN s35 16 := hrun51
  have hs51pc : s51.pc = 1527 := by rw [hs51eq]; exact hs.1
  have hs51h : s51.halted = false := by rw [hs51eq]; exact hs.2.1
  have hs51Z : s51.mem.get 0 = 0 := by rw [hs51eq]; exact hs.2.2.1
  have hs51B : s51.mem.get 35 = s.mem.get 22 := by
    rw [hs51eq, hs.2.2.2.1, hs35CH]
  have hs51I : s51.mem.get 29 = 3 := by rw [hs51eq]; exact hs.2.2.2.2.1
  have hpres51 : ∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s51.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs51eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres35 a ha18 ha30 haR ha0)
  have hONE51 : s51.mem.get 3 = 1 := (hpres51 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR51 : s51.mem.get 2319 = 3 := by
    rw [hs51eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs35R
  have hDI51 : s51.mem.get 2321 = 2 := (hpres51 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g51 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s51.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres51 (UInt16.ofNat k) n35 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s51) hs51pc hs51h hs51Z hONE51 hR51 g51
  have hrun64 : runN s 64 = runN s51 13 := runN_add_eq s 51 13 64 (by decide)
  let s64 := runN s 64
  have hs64eq : s64 = runN s51 13 := hrun64
  have hs64pc : s64.pc = 1893 := by rw [hs64eq]; exact hr.1
  have hs64h : s64.halted = false := by rw [hs64eq]; exact hr.2.1
  have hs64Z : s64.mem.get 0 = 0 := by rw [hs64eq]; exact hr.2.2.1
  have hs64I : s64.mem.get 29 = 4 := by
    rw [hs64eq, hr.2.2.2.1, hs51I]
    exact (rfl : (3 : Word) + 1 = 4)
  have hs64B : s64.mem.get 35 = s.mem.get 22 := by
    rw [hs64eq]
    exact (hr.2.2.2.2 35 (by decide) (by decide) (by decide)).trans hs51B
  have hpres64 : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s64.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs64eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres51 a haB ha18 ha30 haR ha0)
  have hONE64 : s64.mem.get 3 = 1 := (hpres64 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI64 : s64.mem.get 2321 = 2 := (hpres64 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g64 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s64.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres64 (UInt16.ofNat k) n35 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s64) hs64pc hs64h hs64Z hONE64 g64
  have hrun : s68 = runN s64 4 := runN_add_eq s 64 4 68 (by decide)
  have hsTpc : s68.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s68.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s68.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s68.mem.get 2321 = 3 := by
    rw [hrun, hn.2.2.2.1, hDI64]
    exact (rfl : (2 : Word) + 1 = 3)
  have hsTI : s68.mem.get 29 = 4 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs64I
  have hsTB : s68.mem.get 35 = s.mem.get 22 := by
    rw [hrun]; exact (hn.2.2.2.2 35 (by decide) (by decide)).trans hs64B
  have hpres : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s68.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres64 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 2` and `IDX = 4 < ROOM`: write `Q2`
at `BUF+4`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 70 steps. -/
theorem take_store_next_di2_idx4 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 2)
    (hI : s.mem.get 29 = 4)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s70 := runN s 70
    s70.pc = 1641 ∧
    s70.halted = false ∧
    s70.mem.get 0 = 0 ∧
    s70.mem.get 36 = s.mem.get 22 ∧
    s70.mem.get 29 = 5 ∧
    s70.mem.get 2321 = 3 ∧
    (∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s70.mem.get a = s.mem.get a) := by
  intro s70
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di2 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1824 := ht.1
  have hs14h : s14.halted = false := ht.2.1
  have hs14Z : s14.mem.get 0 = 0 := ht.2.2.1
  have hs14CH : s14.mem.get 30 = s.mem.get 22 := ht.2.2.2.1
  have hs14DI : s14.mem.get 2321 = 2 := ht.2.2.2.2.1
  have hpres14 := ht.2.2.2.2.2
  have hONE14 : s14.mem.get 3 = 1 := (hpres14 3 (by decide) (by decide) (by decide)).trans hONE
  have hI14 : s14.mem.get 29 = 4 := (hpres14 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem14 : s14.mem.get 28 = s.mem.get 28 := hpres14 28 (by decide) (by decide) (by decide)
  have hIlt : (s14.mem.get 29).toNat < (s14.mem.get 28).toNat := by
    rw [hI14, hRmem14]; simp; exact hRlo
  have hRhi' : (s14.mem.get 28).toNat < 32768 := by rw [hRmem14]; exact hRhi
  have g14 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s14.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres14 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s14) hs14pc hs14h hs14Z hONE14 hIlt hRhi' g14
  have hrun35 : runN s 35 = runN s14 21 := runN_add_eq s 14 21 35 (by decide)
  let s35 := runN s 35
  have hs35eq : s35 = runN s14 21 := hrun35
  have hs35pc : s35.pc = 1185 := by rw [hs35eq]; exact hhv.1
  have hs35h : s35.halted = false := by rw [hs35eq]; exact hhv.2.1
  have hs35Z : s35.mem.get 0 = 0 := by rw [hs35eq]; exact hhv.2.2.1
  have hs35R : s35.mem.get 2319 = 3 := by rw [hs35eq]; exact hhv.2.2.2.1
  have hs35I : s35.mem.get 29 = 4 := by
    rw [hs35eq, hhv.2.2.2.2.1, hI14]
  have hs35CH : s35.mem.get 30 = s.mem.get 22 := by
    rw [hs35eq, hhv.2.2.2.2.2.1, hs14CH]
  have hpres35 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s35.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs35eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres14 a ha18 ha30 ha0)
  have hONE35 : s35.mem.get 3 = 1 := (hpres35 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI35 : s35.mem.get 2321 = 2 := (hpres35 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g35 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s35.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres35 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx4 (s := s35) hs35pc hs35h hs35Z hONE35 hs35I g35
  have hrun53 : runN s 53 = runN s35 18 := runN_add_eq s 35 18 53 (by decide)
  let s53 := runN s 53
  have hs53eq : s53 = runN s35 18 := hrun53
  have hs53pc : s53.pc = 1527 := by rw [hs53eq]; exact hs.1
  have hs53h : s53.halted = false := by rw [hs53eq]; exact hs.2.1
  have hs53Z : s53.mem.get 0 = 0 := by rw [hs53eq]; exact hs.2.2.1
  have hs53B : s53.mem.get 36 = s.mem.get 22 := by
    rw [hs53eq, hs.2.2.2.1, hs35CH]
  have hs53I : s53.mem.get 29 = 4 := by rw [hs53eq]; exact hs.2.2.2.2.1
  have hpres53 : ∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s53.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs53eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres35 a ha18 ha30 haR ha0)
  have hONE53 : s53.mem.get 3 = 1 := (hpres53 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR53 : s53.mem.get 2319 = 3 := by
    rw [hs53eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs35R
  have hDI53 : s53.mem.get 2321 = 2 := (hpres53 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g53 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s53.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres53 (UInt16.ofNat k) n36 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s53) hs53pc hs53h hs53Z hONE53 hR53 g53
  have hrun66 : runN s 66 = runN s53 13 := runN_add_eq s 53 13 66 (by decide)
  let s66 := runN s 66
  have hs66eq : s66 = runN s53 13 := hrun66
  have hs66pc : s66.pc = 1893 := by rw [hs66eq]; exact hr.1
  have hs66h : s66.halted = false := by rw [hs66eq]; exact hr.2.1
  have hs66Z : s66.mem.get 0 = 0 := by rw [hs66eq]; exact hr.2.2.1
  have hs66I : s66.mem.get 29 = 5 := by
    rw [hs66eq, hr.2.2.2.1, hs53I]
    exact (rfl : (4 : Word) + 1 = 5)
  have hs66B : s66.mem.get 36 = s.mem.get 22 := by
    rw [hs66eq]
    exact (hr.2.2.2.2 36 (by decide) (by decide) (by decide)).trans hs53B
  have hpres66 : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s66.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs66eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres53 a haB ha18 ha30 haR ha0)
  have hONE66 : s66.mem.get 3 = 1 := (hpres66 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI66 : s66.mem.get 2321 = 2 := (hpres66 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g66 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s66.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres66 (UInt16.ofNat k) n36 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s66) hs66pc hs66h hs66Z hONE66 g66
  have hrun : s70 = runN s66 4 := runN_add_eq s 66 4 70 (by decide)
  have hsTpc : s70.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s70.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s70.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s70.mem.get 2321 = 3 := by
    rw [hrun, hn.2.2.2.1, hDI66]
    exact (rfl : (2 : Word) + 1 = 3)
  have hsTI : s70.mem.get 29 = 5 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs66I
  have hsTB : s70.mem.get 36 = s.mem.get 22 := by
    rw [hrun]; exact (hn.2.2.2.2 36 (by decide) (by decide)).trans hs66B
  have hpres : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s70.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres66 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 2` and `IDX = 5 < ROOM`: write `Q2`
at `BUF+5`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 72 steps. -/
theorem take_store_next_di2_idx5 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 2)
    (hI : s.mem.get 29 = 5)
    (hRlo : 5 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s72 := runN s 72
    s72.pc = 1641 ∧
    s72.halted = false ∧
    s72.mem.get 0 = 0 ∧
    s72.mem.get 37 = s.mem.get 22 ∧
    s72.mem.get 29 = 6 ∧
    s72.mem.get 2321 = 3 ∧
    (∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s72.mem.get a = s.mem.get a) := by
  intro s72
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di2 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1824 := ht.1
  have hs14h : s14.halted = false := ht.2.1
  have hs14Z : s14.mem.get 0 = 0 := ht.2.2.1
  have hs14CH : s14.mem.get 30 = s.mem.get 22 := ht.2.2.2.1
  have hs14DI : s14.mem.get 2321 = 2 := ht.2.2.2.2.1
  have hpres14 := ht.2.2.2.2.2
  have hONE14 : s14.mem.get 3 = 1 := (hpres14 3 (by decide) (by decide) (by decide)).trans hONE
  have hI14 : s14.mem.get 29 = 5 := (hpres14 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem14 : s14.mem.get 28 = s.mem.get 28 := hpres14 28 (by decide) (by decide) (by decide)
  have hIlt : (s14.mem.get 29).toNat < (s14.mem.get 28).toNat := by
    rw [hI14, hRmem14]; simp; exact hRlo
  have hRhi' : (s14.mem.get 28).toNat < 32768 := by rw [hRmem14]; exact hRhi
  have g14 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s14.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres14 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s14) hs14pc hs14h hs14Z hONE14 hIlt hRhi' g14
  have hrun35 : runN s 35 = runN s14 21 := runN_add_eq s 14 21 35 (by decide)
  let s35 := runN s 35
  have hs35eq : s35 = runN s14 21 := hrun35
  have hs35pc : s35.pc = 1185 := by rw [hs35eq]; exact hhv.1
  have hs35h : s35.halted = false := by rw [hs35eq]; exact hhv.2.1
  have hs35Z : s35.mem.get 0 = 0 := by rw [hs35eq]; exact hhv.2.2.1
  have hs35R : s35.mem.get 2319 = 3 := by rw [hs35eq]; exact hhv.2.2.2.1
  have hs35I : s35.mem.get 29 = 5 := by
    rw [hs35eq, hhv.2.2.2.2.1, hI14]
  have hs35CH : s35.mem.get 30 = s.mem.get 22 := by
    rw [hs35eq, hhv.2.2.2.2.2.1, hs14CH]
  have hpres35 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s35.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs35eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres14 a ha18 ha30 ha0)
  have hONE35 : s35.mem.get 3 = 1 := (hpres35 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI35 : s35.mem.get 2321 = 2 := (hpres35 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g35 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s35.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres35 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx5 (s := s35) hs35pc hs35h hs35Z hONE35 hs35I g35
  have hrun55 : runN s 55 = runN s35 20 := runN_add_eq s 35 20 55 (by decide)
  let s55 := runN s 55
  have hs55eq : s55 = runN s35 20 := hrun55
  have hs55pc : s55.pc = 1527 := by rw [hs55eq]; exact hs.1
  have hs55h : s55.halted = false := by rw [hs55eq]; exact hs.2.1
  have hs55Z : s55.mem.get 0 = 0 := by rw [hs55eq]; exact hs.2.2.1
  have hs55B : s55.mem.get 37 = s.mem.get 22 := by
    rw [hs55eq, hs.2.2.2.1, hs35CH]
  have hs55I : s55.mem.get 29 = 5 := by rw [hs55eq]; exact hs.2.2.2.2.1
  have hpres55 : ∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s55.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs55eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres35 a ha18 ha30 haR ha0)
  have hONE55 : s55.mem.get 3 = 1 := (hpres55 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR55 : s55.mem.get 2319 = 3 := by
    rw [hs55eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs35R
  have hDI55 : s55.mem.get 2321 = 2 := (hpres55 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g55 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s55.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres55 (UInt16.ofNat k) n37 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s55) hs55pc hs55h hs55Z hONE55 hR55 g55
  have hrun68 : runN s 68 = runN s55 13 := runN_add_eq s 55 13 68 (by decide)
  let s68 := runN s 68
  have hs68eq : s68 = runN s55 13 := hrun68
  have hs68pc : s68.pc = 1893 := by rw [hs68eq]; exact hr.1
  have hs68h : s68.halted = false := by rw [hs68eq]; exact hr.2.1
  have hs68Z : s68.mem.get 0 = 0 := by rw [hs68eq]; exact hr.2.2.1
  have hs68I : s68.mem.get 29 = 6 := by
    rw [hs68eq, hr.2.2.2.1, hs55I]
    exact (rfl : (5 : Word) + 1 = 6)
  have hs68B : s68.mem.get 37 = s.mem.get 22 := by
    rw [hs68eq]
    exact (hr.2.2.2.2 37 (by decide) (by decide) (by decide)).trans hs55B
  have hpres68 : ∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s68.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs68eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres55 a haB ha18 ha30 haR ha0)
  have hONE68 : s68.mem.get 3 = 1 := (hpres68 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI68 : s68.mem.get 2321 = 2 := (hpres68 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g68 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s68.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres68 (UInt16.ofNat k) n37 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s68) hs68pc hs68h hs68Z hONE68 g68
  have hrun : s72 = runN s68 4 := runN_add_eq s 68 4 72 (by decide)
  have hsTpc : s72.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s72.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s72.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s72.mem.get 2321 = 3 := by
    rw [hrun, hn.2.2.2.1, hDI68]
    exact (rfl : (2 : Word) + 1 = 3)
  have hsTI : s72.mem.get 29 = 6 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs68I
  have hsTB : s72.mem.get 37 = s.mem.get 22 := by
    rw [hrun]; exact (hn.2.2.2.2 37 (by decide) (by decide)).trans hs68B
  have hpres : ∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s72.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres68 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 3` and `IDX = 0 < ROOM`: write `Q3`
at `BUF+0`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 64 steps. -/
theorem take_store_next_di3_idx0 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 3)
    (hI : s.mem.get 29 = 0)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s64 := runN s 64
    s64.pc = 1641 ∧
    s64.halted = false ∧
    s64.mem.get 0 = 0 ∧
    s64.mem.get 32 = s.mem.get 23 ∧
    s64.mem.get 29 = 1 ∧
    s64.mem.get 2321 = 4 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s64.mem.get a = s.mem.get a) := by
  intro s64
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di3 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1824 := ht.1
  have hs16h : s16.halted = false := ht.2.1
  have hs16Z : s16.mem.get 0 = 0 := ht.2.2.1
  have hs16CH : s16.mem.get 30 = s.mem.get 23 := ht.2.2.2.1
  have hs16DI : s16.mem.get 2321 = 3 := ht.2.2.2.2.1
  have hpres16 := ht.2.2.2.2.2
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 0 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem16 : s16.mem.get 28 = s.mem.get 28 := hpres16 28 (by decide) (by decide) (by decide)
  have hIlt : (s16.mem.get 29).toNat < (s16.mem.get 28).toNat := by
    rw [hI16, hRmem16]; simp; exact hRlo
  have hRhi' : (s16.mem.get 28).toNat < 32768 := by rw [hRmem16]; exact hRhi
  have g16 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s16) hs16pc hs16h hs16Z hONE16 hIlt hRhi' g16
  have hrun37 : runN s 37 = runN s16 21 := runN_add_eq s 16 21 37 (by decide)
  let s37 := runN s 37
  have hs37eq : s37 = runN s16 21 := hrun37
  have hs37pc : s37.pc = 1185 := by rw [hs37eq]; exact hhv.1
  have hs37h : s37.halted = false := by rw [hs37eq]; exact hhv.2.1
  have hs37Z : s37.mem.get 0 = 0 := by rw [hs37eq]; exact hhv.2.2.1
  have hs37R : s37.mem.get 2319 = 3 := by rw [hs37eq]; exact hhv.2.2.2.1
  have hs37I : s37.mem.get 29 = 0 := by
    rw [hs37eq, hhv.2.2.2.2.1, hI16]
  have hs37CH : s37.mem.get 30 = s.mem.get 23 := by
    rw [hs37eq, hhv.2.2.2.2.2.1, hs16CH]
  have hpres37 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s37.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs37eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres16 a ha18 ha30 ha0)
  have hONE37 : s37.mem.get 3 = 1 := (hpres37 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI37 : s37.mem.get 2321 = 3 := (hpres37 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g37a : ∀ k : Nat, 1185 ≤ k → k < 1200 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have g37b : ∀ k : Nat, 1287 ≤ k → k < 1302 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx0 (s := s37) hs37pc hs37h hs37Z hs37I g37a g37b
  have hrun47 : runN s 47 = runN s37 10 := runN_add_eq s 37 10 47 (by decide)
  let s47 := runN s 47
  have hs47eq : s47 = runN s37 10 := hrun47
  have hs47pc : s47.pc = 1527 := by rw [hs47eq]; exact hs.1
  have hs47h : s47.halted = false := by rw [hs47eq]; exact hs.2.1
  have hs47Z : s47.mem.get 0 = 0 := by rw [hs47eq]; exact hs.2.2.1
  have hs47B : s47.mem.get 32 = s.mem.get 23 := by
    rw [hs47eq, hs.2.2.2.1, hs37CH]
  have hs47I : s47.mem.get 29 = 0 := by rw [hs47eq]; exact hs.2.2.2.2.1
  have hpres47 : ∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s47.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs47eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres37 a ha18 ha30 haR ha0)
  have hONE47 : s47.mem.get 3 = 1 := (hpres47 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR47 : s47.mem.get 2319 = 3 := by
    rw [hs47eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs37R
  have hDI47 : s47.mem.get 2321 = 3 := (hpres47 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g47 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n32 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s47) hs47pc hs47h hs47Z hONE47 hR47 g47
  have hrun60 : runN s 60 = runN s47 13 := runN_add_eq s 47 13 60 (by decide)
  let s60 := runN s 60
  have hs60eq : s60 = runN s47 13 := hrun60
  have hs60pc : s60.pc = 1893 := by rw [hs60eq]; exact hr.1
  have hs60h : s60.halted = false := by rw [hs60eq]; exact hr.2.1
  have hs60Z : s60.mem.get 0 = 0 := by rw [hs60eq]; exact hr.2.2.1
  have hs60I : s60.mem.get 29 = 1 := by
    rw [hs60eq, hr.2.2.2.1, hs47I]
    exact (rfl : (0 : Word) + 1 = 1)
  have hs60B : s60.mem.get 32 = s.mem.get 23 := by
    rw [hs60eq]
    exact (hr.2.2.2.2 32 (by decide) (by decide) (by decide)).trans hs47B
  have hpres60 : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s60.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs60eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres47 a haB ha18 ha30 haR ha0)
  have hONE60 : s60.mem.get 3 = 1 := (hpres60 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI60 : s60.mem.get 2321 = 3 := (hpres60 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g60 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s60.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres60 (UInt16.ofNat k) n32 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s60) hs60pc hs60h hs60Z hONE60 g60
  have hrun : s64 = runN s60 4 := runN_add_eq s 60 4 64 (by decide)
  have hsTpc : s64.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s64.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s64.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s64.mem.get 2321 = 4 := by
    rw [hrun, hn.2.2.2.1, hDI60]
    exact (rfl : (3 : Word) + 1 = 4)
  have hsTI : s64.mem.get 29 = 1 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs60I
  have hsTB : s64.mem.get 32 = s.mem.get 23 := by
    rw [hrun]; exact (hn.2.2.2.2 32 (by decide) (by decide)).trans hs60B
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s64.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres60 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 3` and `IDX = 1 < ROOM`: write `Q3`
at `BUF+1`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 66 steps. -/
theorem take_store_next_di3_idx1 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 3)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s66 := runN s 66
    s66.pc = 1641 ∧
    s66.halted = false ∧
    s66.mem.get 0 = 0 ∧
    s66.mem.get 33 = s.mem.get 23 ∧
    s66.mem.get 29 = 2 ∧
    s66.mem.get 2321 = 4 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s66.mem.get a = s.mem.get a) := by
  intro s66
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di3 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1824 := ht.1
  have hs16h : s16.halted = false := ht.2.1
  have hs16Z : s16.mem.get 0 = 0 := ht.2.2.1
  have hs16CH : s16.mem.get 30 = s.mem.get 23 := ht.2.2.2.1
  have hs16DI : s16.mem.get 2321 = 3 := ht.2.2.2.2.1
  have hpres16 := ht.2.2.2.2.2
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 1 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem16 : s16.mem.get 28 = s.mem.get 28 := hpres16 28 (by decide) (by decide) (by decide)
  have hIlt : (s16.mem.get 29).toNat < (s16.mem.get 28).toNat := by
    rw [hI16, hRmem16]; simp; exact hRlo
  have hRhi' : (s16.mem.get 28).toNat < 32768 := by rw [hRmem16]; exact hRhi
  have g16 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s16) hs16pc hs16h hs16Z hONE16 hIlt hRhi' g16
  have hrun37 : runN s 37 = runN s16 21 := runN_add_eq s 16 21 37 (by decide)
  let s37 := runN s 37
  have hs37eq : s37 = runN s16 21 := hrun37
  have hs37pc : s37.pc = 1185 := by rw [hs37eq]; exact hhv.1
  have hs37h : s37.halted = false := by rw [hs37eq]; exact hhv.2.1
  have hs37Z : s37.mem.get 0 = 0 := by rw [hs37eq]; exact hhv.2.2.1
  have hs37R : s37.mem.get 2319 = 3 := by rw [hs37eq]; exact hhv.2.2.2.1
  have hs37I : s37.mem.get 29 = 1 := by
    rw [hs37eq, hhv.2.2.2.2.1, hI16]
  have hs37CH : s37.mem.get 30 = s.mem.get 23 := by
    rw [hs37eq, hhv.2.2.2.2.2.1, hs16CH]
  have hpres37 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s37.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs37eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres16 a ha18 ha30 ha0)
  have hONE37 : s37.mem.get 3 = 1 := (hpres37 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI37 : s37.mem.get 2321 = 3 := (hpres37 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g37 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx1 (s := s37) hs37pc hs37h hs37Z hONE37 hs37I g37
  have hrun49 : runN s 49 = runN s37 12 := runN_add_eq s 37 12 49 (by decide)
  let s49 := runN s 49
  have hs49eq : s49 = runN s37 12 := hrun49
  have hs49pc : s49.pc = 1527 := by rw [hs49eq]; exact hs.1
  have hs49h : s49.halted = false := by rw [hs49eq]; exact hs.2.1
  have hs49Z : s49.mem.get 0 = 0 := by rw [hs49eq]; exact hs.2.2.1
  have hs49B : s49.mem.get 33 = s.mem.get 23 := by
    rw [hs49eq, hs.2.2.2.1, hs37CH]
  have hs49I : s49.mem.get 29 = 1 := by rw [hs49eq]; exact hs.2.2.2.2.1
  have hpres49 : ∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s49.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs49eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres37 a ha18 ha30 haR ha0)
  have hONE49 : s49.mem.get 3 = 1 := (hpres49 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR49 : s49.mem.get 2319 = 3 := by
    rw [hs49eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs37R
  have hDI49 : s49.mem.get 2321 = 3 := (hpres49 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g49 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s49.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres49 (UInt16.ofNat k) n33 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s49) hs49pc hs49h hs49Z hONE49 hR49 g49
  have hrun62 : runN s 62 = runN s49 13 := runN_add_eq s 49 13 62 (by decide)
  let s62 := runN s 62
  have hs62eq : s62 = runN s49 13 := hrun62
  have hs62pc : s62.pc = 1893 := by rw [hs62eq]; exact hr.1
  have hs62h : s62.halted = false := by rw [hs62eq]; exact hr.2.1
  have hs62Z : s62.mem.get 0 = 0 := by rw [hs62eq]; exact hr.2.2.1
  have hs62I : s62.mem.get 29 = 2 := by
    rw [hs62eq, hr.2.2.2.1, hs49I]
    exact (rfl : (1 : Word) + 1 = 2)
  have hs62B : s62.mem.get 33 = s.mem.get 23 := by
    rw [hs62eq]
    exact (hr.2.2.2.2 33 (by decide) (by decide) (by decide)).trans hs49B
  have hpres62 : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s62.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs62eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres49 a haB ha18 ha30 haR ha0)
  have hONE62 : s62.mem.get 3 = 1 := (hpres62 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI62 : s62.mem.get 2321 = 3 := (hpres62 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g62 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s62.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres62 (UInt16.ofNat k) n33 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s62) hs62pc hs62h hs62Z hONE62 g62
  have hrun : s66 = runN s62 4 := runN_add_eq s 62 4 66 (by decide)
  have hsTpc : s66.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s66.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s66.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s66.mem.get 2321 = 4 := by
    rw [hrun, hn.2.2.2.1, hDI62]
    exact (rfl : (3 : Word) + 1 = 4)
  have hsTI : s66.mem.get 29 = 2 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs62I
  have hsTB : s66.mem.get 33 = s.mem.get 23 := by
    rw [hrun]; exact (hn.2.2.2.2 33 (by decide) (by decide)).trans hs62B
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s66.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres62 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 3` and `IDX = 2 < ROOM`: write `Q3`
at `BUF+2`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 68 steps. -/
theorem take_store_next_di3_idx2 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 3)
    (hI : s.mem.get 29 = 2)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s68 := runN s 68
    s68.pc = 1641 ∧
    s68.halted = false ∧
    s68.mem.get 0 = 0 ∧
    s68.mem.get 34 = s.mem.get 23 ∧
    s68.mem.get 29 = 3 ∧
    s68.mem.get 2321 = 4 ∧
    (∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s68.mem.get a = s.mem.get a) := by
  intro s68
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di3 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1824 := ht.1
  have hs16h : s16.halted = false := ht.2.1
  have hs16Z : s16.mem.get 0 = 0 := ht.2.2.1
  have hs16CH : s16.mem.get 30 = s.mem.get 23 := ht.2.2.2.1
  have hs16DI : s16.mem.get 2321 = 3 := ht.2.2.2.2.1
  have hpres16 := ht.2.2.2.2.2
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 2 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem16 : s16.mem.get 28 = s.mem.get 28 := hpres16 28 (by decide) (by decide) (by decide)
  have hIlt : (s16.mem.get 29).toNat < (s16.mem.get 28).toNat := by
    rw [hI16, hRmem16]; simp; exact hRlo
  have hRhi' : (s16.mem.get 28).toNat < 32768 := by rw [hRmem16]; exact hRhi
  have g16 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s16) hs16pc hs16h hs16Z hONE16 hIlt hRhi' g16
  have hrun37 : runN s 37 = runN s16 21 := runN_add_eq s 16 21 37 (by decide)
  let s37 := runN s 37
  have hs37eq : s37 = runN s16 21 := hrun37
  have hs37pc : s37.pc = 1185 := by rw [hs37eq]; exact hhv.1
  have hs37h : s37.halted = false := by rw [hs37eq]; exact hhv.2.1
  have hs37Z : s37.mem.get 0 = 0 := by rw [hs37eq]; exact hhv.2.2.1
  have hs37R : s37.mem.get 2319 = 3 := by rw [hs37eq]; exact hhv.2.2.2.1
  have hs37I : s37.mem.get 29 = 2 := by
    rw [hs37eq, hhv.2.2.2.2.1, hI16]
  have hs37CH : s37.mem.get 30 = s.mem.get 23 := by
    rw [hs37eq, hhv.2.2.2.2.2.1, hs16CH]
  have hpres37 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s37.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs37eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres16 a ha18 ha30 ha0)
  have hONE37 : s37.mem.get 3 = 1 := (hpres37 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI37 : s37.mem.get 2321 = 3 := (hpres37 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g37 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx2 (s := s37) hs37pc hs37h hs37Z hONE37 hs37I g37
  have hrun51 : runN s 51 = runN s37 14 := runN_add_eq s 37 14 51 (by decide)
  let s51 := runN s 51
  have hs51eq : s51 = runN s37 14 := hrun51
  have hs51pc : s51.pc = 1527 := by rw [hs51eq]; exact hs.1
  have hs51h : s51.halted = false := by rw [hs51eq]; exact hs.2.1
  have hs51Z : s51.mem.get 0 = 0 := by rw [hs51eq]; exact hs.2.2.1
  have hs51B : s51.mem.get 34 = s.mem.get 23 := by
    rw [hs51eq, hs.2.2.2.1, hs37CH]
  have hs51I : s51.mem.get 29 = 2 := by rw [hs51eq]; exact hs.2.2.2.2.1
  have hpres51 : ∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s51.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs51eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres37 a ha18 ha30 haR ha0)
  have hONE51 : s51.mem.get 3 = 1 := (hpres51 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR51 : s51.mem.get 2319 = 3 := by
    rw [hs51eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs37R
  have hDI51 : s51.mem.get 2321 = 3 := (hpres51 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g51 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s51.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres51 (UInt16.ofNat k) n34 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s51) hs51pc hs51h hs51Z hONE51 hR51 g51
  have hrun64 : runN s 64 = runN s51 13 := runN_add_eq s 51 13 64 (by decide)
  let s64 := runN s 64
  have hs64eq : s64 = runN s51 13 := hrun64
  have hs64pc : s64.pc = 1893 := by rw [hs64eq]; exact hr.1
  have hs64h : s64.halted = false := by rw [hs64eq]; exact hr.2.1
  have hs64Z : s64.mem.get 0 = 0 := by rw [hs64eq]; exact hr.2.2.1
  have hs64I : s64.mem.get 29 = 3 := by
    rw [hs64eq, hr.2.2.2.1, hs51I]
    exact (rfl : (2 : Word) + 1 = 3)
  have hs64B : s64.mem.get 34 = s.mem.get 23 := by
    rw [hs64eq]
    exact (hr.2.2.2.2 34 (by decide) (by decide) (by decide)).trans hs51B
  have hpres64 : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s64.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs64eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres51 a haB ha18 ha30 haR ha0)
  have hONE64 : s64.mem.get 3 = 1 := (hpres64 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI64 : s64.mem.get 2321 = 3 := (hpres64 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g64 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s64.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres64 (UInt16.ofNat k) n34 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s64) hs64pc hs64h hs64Z hONE64 g64
  have hrun : s68 = runN s64 4 := runN_add_eq s 64 4 68 (by decide)
  have hsTpc : s68.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s68.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s68.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s68.mem.get 2321 = 4 := by
    rw [hrun, hn.2.2.2.1, hDI64]
    exact (rfl : (3 : Word) + 1 = 4)
  have hsTI : s68.mem.get 29 = 3 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs64I
  have hsTB : s68.mem.get 34 = s.mem.get 23 := by
    rw [hrun]; exact (hn.2.2.2.2 34 (by decide) (by decide)).trans hs64B
  have hpres : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s68.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres64 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 3` and `IDX = 3 < ROOM`: write `Q3`
at `BUF+3`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 70 steps. -/
theorem take_store_next_di3_idx3 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 3)
    (hI : s.mem.get 29 = 3)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s70 := runN s 70
    s70.pc = 1641 ∧
    s70.halted = false ∧
    s70.mem.get 0 = 0 ∧
    s70.mem.get 35 = s.mem.get 23 ∧
    s70.mem.get 29 = 4 ∧
    s70.mem.get 2321 = 4 ∧
    (∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s70.mem.get a = s.mem.get a) := by
  intro s70
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di3 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1824 := ht.1
  have hs16h : s16.halted = false := ht.2.1
  have hs16Z : s16.mem.get 0 = 0 := ht.2.2.1
  have hs16CH : s16.mem.get 30 = s.mem.get 23 := ht.2.2.2.1
  have hs16DI : s16.mem.get 2321 = 3 := ht.2.2.2.2.1
  have hpres16 := ht.2.2.2.2.2
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 3 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem16 : s16.mem.get 28 = s.mem.get 28 := hpres16 28 (by decide) (by decide) (by decide)
  have hIlt : (s16.mem.get 29).toNat < (s16.mem.get 28).toNat := by
    rw [hI16, hRmem16]; simp; exact hRlo
  have hRhi' : (s16.mem.get 28).toNat < 32768 := by rw [hRmem16]; exact hRhi
  have g16 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s16) hs16pc hs16h hs16Z hONE16 hIlt hRhi' g16
  have hrun37 : runN s 37 = runN s16 21 := runN_add_eq s 16 21 37 (by decide)
  let s37 := runN s 37
  have hs37eq : s37 = runN s16 21 := hrun37
  have hs37pc : s37.pc = 1185 := by rw [hs37eq]; exact hhv.1
  have hs37h : s37.halted = false := by rw [hs37eq]; exact hhv.2.1
  have hs37Z : s37.mem.get 0 = 0 := by rw [hs37eq]; exact hhv.2.2.1
  have hs37R : s37.mem.get 2319 = 3 := by rw [hs37eq]; exact hhv.2.2.2.1
  have hs37I : s37.mem.get 29 = 3 := by
    rw [hs37eq, hhv.2.2.2.2.1, hI16]
  have hs37CH : s37.mem.get 30 = s.mem.get 23 := by
    rw [hs37eq, hhv.2.2.2.2.2.1, hs16CH]
  have hpres37 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s37.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs37eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres16 a ha18 ha30 ha0)
  have hONE37 : s37.mem.get 3 = 1 := (hpres37 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI37 : s37.mem.get 2321 = 3 := (hpres37 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g37 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx3 (s := s37) hs37pc hs37h hs37Z hONE37 hs37I g37
  have hrun53 : runN s 53 = runN s37 16 := runN_add_eq s 37 16 53 (by decide)
  let s53 := runN s 53
  have hs53eq : s53 = runN s37 16 := hrun53
  have hs53pc : s53.pc = 1527 := by rw [hs53eq]; exact hs.1
  have hs53h : s53.halted = false := by rw [hs53eq]; exact hs.2.1
  have hs53Z : s53.mem.get 0 = 0 := by rw [hs53eq]; exact hs.2.2.1
  have hs53B : s53.mem.get 35 = s.mem.get 23 := by
    rw [hs53eq, hs.2.2.2.1, hs37CH]
  have hs53I : s53.mem.get 29 = 3 := by rw [hs53eq]; exact hs.2.2.2.2.1
  have hpres53 : ∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s53.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs53eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres37 a ha18 ha30 haR ha0)
  have hONE53 : s53.mem.get 3 = 1 := (hpres53 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR53 : s53.mem.get 2319 = 3 := by
    rw [hs53eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs37R
  have hDI53 : s53.mem.get 2321 = 3 := (hpres53 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g53 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s53.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres53 (UInt16.ofNat k) n35 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s53) hs53pc hs53h hs53Z hONE53 hR53 g53
  have hrun66 : runN s 66 = runN s53 13 := runN_add_eq s 53 13 66 (by decide)
  let s66 := runN s 66
  have hs66eq : s66 = runN s53 13 := hrun66
  have hs66pc : s66.pc = 1893 := by rw [hs66eq]; exact hr.1
  have hs66h : s66.halted = false := by rw [hs66eq]; exact hr.2.1
  have hs66Z : s66.mem.get 0 = 0 := by rw [hs66eq]; exact hr.2.2.1
  have hs66I : s66.mem.get 29 = 4 := by
    rw [hs66eq, hr.2.2.2.1, hs53I]
    exact (rfl : (3 : Word) + 1 = 4)
  have hs66B : s66.mem.get 35 = s.mem.get 23 := by
    rw [hs66eq]
    exact (hr.2.2.2.2 35 (by decide) (by decide) (by decide)).trans hs53B
  have hpres66 : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s66.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs66eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres53 a haB ha18 ha30 haR ha0)
  have hONE66 : s66.mem.get 3 = 1 := (hpres66 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI66 : s66.mem.get 2321 = 3 := (hpres66 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g66 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s66.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres66 (UInt16.ofNat k) n35 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s66) hs66pc hs66h hs66Z hONE66 g66
  have hrun : s70 = runN s66 4 := runN_add_eq s 66 4 70 (by decide)
  have hsTpc : s70.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s70.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s70.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s70.mem.get 2321 = 4 := by
    rw [hrun, hn.2.2.2.1, hDI66]
    exact (rfl : (3 : Word) + 1 = 4)
  have hsTI : s70.mem.get 29 = 4 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs66I
  have hsTB : s70.mem.get 35 = s.mem.get 23 := by
    rw [hrun]; exact (hn.2.2.2.2 35 (by decide) (by decide)).trans hs66B
  have hpres : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s70.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres66 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 3` and `IDX = 4 < ROOM`: write `Q3`
at `BUF+4`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 72 steps. -/
theorem take_store_next_di3_idx4 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 3)
    (hI : s.mem.get 29 = 4)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s72 := runN s 72
    s72.pc = 1641 ∧
    s72.halted = false ∧
    s72.mem.get 0 = 0 ∧
    s72.mem.get 36 = s.mem.get 23 ∧
    s72.mem.get 29 = 5 ∧
    s72.mem.get 2321 = 4 ∧
    (∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s72.mem.get a = s.mem.get a) := by
  intro s72
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di3 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1824 := ht.1
  have hs16h : s16.halted = false := ht.2.1
  have hs16Z : s16.mem.get 0 = 0 := ht.2.2.1
  have hs16CH : s16.mem.get 30 = s.mem.get 23 := ht.2.2.2.1
  have hs16DI : s16.mem.get 2321 = 3 := ht.2.2.2.2.1
  have hpres16 := ht.2.2.2.2.2
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 4 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem16 : s16.mem.get 28 = s.mem.get 28 := hpres16 28 (by decide) (by decide) (by decide)
  have hIlt : (s16.mem.get 29).toNat < (s16.mem.get 28).toNat := by
    rw [hI16, hRmem16]; simp; exact hRlo
  have hRhi' : (s16.mem.get 28).toNat < 32768 := by rw [hRmem16]; exact hRhi
  have g16 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s16) hs16pc hs16h hs16Z hONE16 hIlt hRhi' g16
  have hrun37 : runN s 37 = runN s16 21 := runN_add_eq s 16 21 37 (by decide)
  let s37 := runN s 37
  have hs37eq : s37 = runN s16 21 := hrun37
  have hs37pc : s37.pc = 1185 := by rw [hs37eq]; exact hhv.1
  have hs37h : s37.halted = false := by rw [hs37eq]; exact hhv.2.1
  have hs37Z : s37.mem.get 0 = 0 := by rw [hs37eq]; exact hhv.2.2.1
  have hs37R : s37.mem.get 2319 = 3 := by rw [hs37eq]; exact hhv.2.2.2.1
  have hs37I : s37.mem.get 29 = 4 := by
    rw [hs37eq, hhv.2.2.2.2.1, hI16]
  have hs37CH : s37.mem.get 30 = s.mem.get 23 := by
    rw [hs37eq, hhv.2.2.2.2.2.1, hs16CH]
  have hpres37 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s37.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs37eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres16 a ha18 ha30 ha0)
  have hONE37 : s37.mem.get 3 = 1 := (hpres37 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI37 : s37.mem.get 2321 = 3 := (hpres37 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g37 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx4 (s := s37) hs37pc hs37h hs37Z hONE37 hs37I g37
  have hrun55 : runN s 55 = runN s37 18 := runN_add_eq s 37 18 55 (by decide)
  let s55 := runN s 55
  have hs55eq : s55 = runN s37 18 := hrun55
  have hs55pc : s55.pc = 1527 := by rw [hs55eq]; exact hs.1
  have hs55h : s55.halted = false := by rw [hs55eq]; exact hs.2.1
  have hs55Z : s55.mem.get 0 = 0 := by rw [hs55eq]; exact hs.2.2.1
  have hs55B : s55.mem.get 36 = s.mem.get 23 := by
    rw [hs55eq, hs.2.2.2.1, hs37CH]
  have hs55I : s55.mem.get 29 = 4 := by rw [hs55eq]; exact hs.2.2.2.2.1
  have hpres55 : ∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s55.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs55eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres37 a ha18 ha30 haR ha0)
  have hONE55 : s55.mem.get 3 = 1 := (hpres55 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR55 : s55.mem.get 2319 = 3 := by
    rw [hs55eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs37R
  have hDI55 : s55.mem.get 2321 = 3 := (hpres55 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g55 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s55.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres55 (UInt16.ofNat k) n36 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s55) hs55pc hs55h hs55Z hONE55 hR55 g55
  have hrun68 : runN s 68 = runN s55 13 := runN_add_eq s 55 13 68 (by decide)
  let s68 := runN s 68
  have hs68eq : s68 = runN s55 13 := hrun68
  have hs68pc : s68.pc = 1893 := by rw [hs68eq]; exact hr.1
  have hs68h : s68.halted = false := by rw [hs68eq]; exact hr.2.1
  have hs68Z : s68.mem.get 0 = 0 := by rw [hs68eq]; exact hr.2.2.1
  have hs68I : s68.mem.get 29 = 5 := by
    rw [hs68eq, hr.2.2.2.1, hs55I]
    exact (rfl : (4 : Word) + 1 = 5)
  have hs68B : s68.mem.get 36 = s.mem.get 23 := by
    rw [hs68eq]
    exact (hr.2.2.2.2 36 (by decide) (by decide) (by decide)).trans hs55B
  have hpres68 : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s68.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs68eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres55 a haB ha18 ha30 haR ha0)
  have hONE68 : s68.mem.get 3 = 1 := (hpres68 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI68 : s68.mem.get 2321 = 3 := (hpres68 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g68 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s68.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres68 (UInt16.ofNat k) n36 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s68) hs68pc hs68h hs68Z hONE68 g68
  have hrun : s72 = runN s68 4 := runN_add_eq s 68 4 72 (by decide)
  have hsTpc : s72.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s72.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s72.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s72.mem.get 2321 = 4 := by
    rw [hrun, hn.2.2.2.1, hDI68]
    exact (rfl : (3 : Word) + 1 = 4)
  have hsTI : s72.mem.get 29 = 5 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs68I
  have hsTB : s72.mem.get 36 = s.mem.get 23 := by
    rw [hrun]; exact (hn.2.2.2.2 36 (by decide) (by decide)).trans hs68B
  have hpres : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s72.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres68 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 3` and `IDX = 5 < ROOM`: write `Q3`
at `BUF+5`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 74 steps. -/
theorem take_store_next_di3_idx5 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 3)
    (hI : s.mem.get 29 = 5)
    (hRlo : 5 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s74 := runN s 74
    s74.pc = 1641 ∧
    s74.halted = false ∧
    s74.mem.get 0 = 0 ∧
    s74.mem.get 37 = s.mem.get 23 ∧
    s74.mem.get 29 = 6 ∧
    s74.mem.get 2321 = 4 ∧
    (∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s74.mem.get a = s.mem.get a) := by
  intro s74
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di3 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1824 := ht.1
  have hs16h : s16.halted = false := ht.2.1
  have hs16Z : s16.mem.get 0 = 0 := ht.2.2.1
  have hs16CH : s16.mem.get 30 = s.mem.get 23 := ht.2.2.2.1
  have hs16DI : s16.mem.get 2321 = 3 := ht.2.2.2.2.1
  have hpres16 := ht.2.2.2.2.2
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 5 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem16 : s16.mem.get 28 = s.mem.get 28 := hpres16 28 (by decide) (by decide) (by decide)
  have hIlt : (s16.mem.get 29).toNat < (s16.mem.get 28).toNat := by
    rw [hI16, hRmem16]; simp; exact hRlo
  have hRhi' : (s16.mem.get 28).toNat < 32768 := by rw [hRmem16]; exact hRhi
  have g16 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s16) hs16pc hs16h hs16Z hONE16 hIlt hRhi' g16
  have hrun37 : runN s 37 = runN s16 21 := runN_add_eq s 16 21 37 (by decide)
  let s37 := runN s 37
  have hs37eq : s37 = runN s16 21 := hrun37
  have hs37pc : s37.pc = 1185 := by rw [hs37eq]; exact hhv.1
  have hs37h : s37.halted = false := by rw [hs37eq]; exact hhv.2.1
  have hs37Z : s37.mem.get 0 = 0 := by rw [hs37eq]; exact hhv.2.2.1
  have hs37R : s37.mem.get 2319 = 3 := by rw [hs37eq]; exact hhv.2.2.2.1
  have hs37I : s37.mem.get 29 = 5 := by
    rw [hs37eq, hhv.2.2.2.2.1, hI16]
  have hs37CH : s37.mem.get 30 = s.mem.get 23 := by
    rw [hs37eq, hhv.2.2.2.2.2.1, hs16CH]
  have hpres37 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s37.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs37eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres16 a ha18 ha30 ha0)
  have hONE37 : s37.mem.get 3 = 1 := (hpres37 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI37 : s37.mem.get 2321 = 3 := (hpres37 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g37 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx5 (s := s37) hs37pc hs37h hs37Z hONE37 hs37I g37
  have hrun57 : runN s 57 = runN s37 20 := runN_add_eq s 37 20 57 (by decide)
  let s57 := runN s 57
  have hs57eq : s57 = runN s37 20 := hrun57
  have hs57pc : s57.pc = 1527 := by rw [hs57eq]; exact hs.1
  have hs57h : s57.halted = false := by rw [hs57eq]; exact hs.2.1
  have hs57Z : s57.mem.get 0 = 0 := by rw [hs57eq]; exact hs.2.2.1
  have hs57B : s57.mem.get 37 = s.mem.get 23 := by
    rw [hs57eq, hs.2.2.2.1, hs37CH]
  have hs57I : s57.mem.get 29 = 5 := by rw [hs57eq]; exact hs.2.2.2.2.1
  have hpres57 : ∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s57.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs57eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres37 a ha18 ha30 haR ha0)
  have hONE57 : s57.mem.get 3 = 1 := (hpres57 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR57 : s57.mem.get 2319 = 3 := by
    rw [hs57eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs37R
  have hDI57 : s57.mem.get 2321 = 3 := (hpres57 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g57 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s57.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres57 (UInt16.ofNat k) n37 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s57) hs57pc hs57h hs57Z hONE57 hR57 g57
  have hrun70 : runN s 70 = runN s57 13 := runN_add_eq s 57 13 70 (by decide)
  let s70 := runN s 70
  have hs70eq : s70 = runN s57 13 := hrun70
  have hs70pc : s70.pc = 1893 := by rw [hs70eq]; exact hr.1
  have hs70h : s70.halted = false := by rw [hs70eq]; exact hr.2.1
  have hs70Z : s70.mem.get 0 = 0 := by rw [hs70eq]; exact hr.2.2.1
  have hs70I : s70.mem.get 29 = 6 := by
    rw [hs70eq, hr.2.2.2.1, hs57I]
    exact (rfl : (5 : Word) + 1 = 6)
  have hs70B : s70.mem.get 37 = s.mem.get 23 := by
    rw [hs70eq]
    exact (hr.2.2.2.2 37 (by decide) (by decide) (by decide)).trans hs57B
  have hpres70 : ∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s70.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs70eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres57 a haB ha18 ha30 haR ha0)
  have hONE70 : s70.mem.get 3 = 1 := (hpres70 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI70 : s70.mem.get 2321 = 3 := (hpres70 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g70 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s70.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres70 (UInt16.ofNat k) n37 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s70) hs70pc hs70h hs70Z hONE70 g70
  have hrun : s74 = runN s70 4 := runN_add_eq s 70 4 74 (by decide)
  have hsTpc : s74.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s74.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s74.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s74.mem.get 2321 = 4 := by
    rw [hrun, hn.2.2.2.1, hDI70]
    exact (rfl : (3 : Word) + 1 = 4)
  have hsTI : s74.mem.get 29 = 6 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs70I
  have hsTB : s74.mem.get 37 = s.mem.get 23 := by
    rw [hrun]; exact (hn.2.2.2.2 37 (by decide) (by decide)).trans hs70B
  have hpres : ∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s74.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres70 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 4` and `IDX = 0 < ROOM`: write `Q4`
at `BUF+0`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 64 steps. -/
theorem take_store_next_di4_idx0 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 4)
    (hI : s.mem.get 29 = 0)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s64 := runN s 64
    s64.pc = 1641 ∧
    s64.halted = false ∧
    s64.mem.get 0 = 0 ∧
    s64.mem.get 32 = s.mem.get 24 ∧
    s64.mem.get 29 = 1 ∧
    s64.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s64.mem.get a = s.mem.get a) := by
  intro s64
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di4 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1824 := ht.1
  have hs16h : s16.halted = false := ht.2.1
  have hs16Z : s16.mem.get 0 = 0 := ht.2.2.1
  have hs16CH : s16.mem.get 30 = s.mem.get 24 := ht.2.2.2.1
  have hs16DI : s16.mem.get 2321 = 4 := ht.2.2.2.2.1
  have hpres16 := ht.2.2.2.2.2
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 0 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem16 : s16.mem.get 28 = s.mem.get 28 := hpres16 28 (by decide) (by decide) (by decide)
  have hIlt : (s16.mem.get 29).toNat < (s16.mem.get 28).toNat := by
    rw [hI16, hRmem16]; simp; exact hRlo
  have hRhi' : (s16.mem.get 28).toNat < 32768 := by rw [hRmem16]; exact hRhi
  have g16 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s16) hs16pc hs16h hs16Z hONE16 hIlt hRhi' g16
  have hrun37 : runN s 37 = runN s16 21 := runN_add_eq s 16 21 37 (by decide)
  let s37 := runN s 37
  have hs37eq : s37 = runN s16 21 := hrun37
  have hs37pc : s37.pc = 1185 := by rw [hs37eq]; exact hhv.1
  have hs37h : s37.halted = false := by rw [hs37eq]; exact hhv.2.1
  have hs37Z : s37.mem.get 0 = 0 := by rw [hs37eq]; exact hhv.2.2.1
  have hs37R : s37.mem.get 2319 = 3 := by rw [hs37eq]; exact hhv.2.2.2.1
  have hs37I : s37.mem.get 29 = 0 := by
    rw [hs37eq, hhv.2.2.2.2.1, hI16]
  have hs37CH : s37.mem.get 30 = s.mem.get 24 := by
    rw [hs37eq, hhv.2.2.2.2.2.1, hs16CH]
  have hpres37 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s37.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs37eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres16 a ha18 ha30 ha0)
  have hONE37 : s37.mem.get 3 = 1 := (hpres37 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI37 : s37.mem.get 2321 = 4 := (hpres37 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g37a : ∀ k : Nat, 1185 ≤ k → k < 1200 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have g37b : ∀ k : Nat, 1287 ≤ k → k < 1302 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx0 (s := s37) hs37pc hs37h hs37Z hs37I g37a g37b
  have hrun47 : runN s 47 = runN s37 10 := runN_add_eq s 37 10 47 (by decide)
  let s47 := runN s 47
  have hs47eq : s47 = runN s37 10 := hrun47
  have hs47pc : s47.pc = 1527 := by rw [hs47eq]; exact hs.1
  have hs47h : s47.halted = false := by rw [hs47eq]; exact hs.2.1
  have hs47Z : s47.mem.get 0 = 0 := by rw [hs47eq]; exact hs.2.2.1
  have hs47B : s47.mem.get 32 = s.mem.get 24 := by
    rw [hs47eq, hs.2.2.2.1, hs37CH]
  have hs47I : s47.mem.get 29 = 0 := by rw [hs47eq]; exact hs.2.2.2.2.1
  have hpres47 : ∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s47.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs47eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres37 a ha18 ha30 haR ha0)
  have hONE47 : s47.mem.get 3 = 1 := (hpres47 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR47 : s47.mem.get 2319 = 3 := by
    rw [hs47eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs37R
  have hDI47 : s47.mem.get 2321 = 4 := (hpres47 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g47 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n32 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s47) hs47pc hs47h hs47Z hONE47 hR47 g47
  have hrun60 : runN s 60 = runN s47 13 := runN_add_eq s 47 13 60 (by decide)
  let s60 := runN s 60
  have hs60eq : s60 = runN s47 13 := hrun60
  have hs60pc : s60.pc = 1893 := by rw [hs60eq]; exact hr.1
  have hs60h : s60.halted = false := by rw [hs60eq]; exact hr.2.1
  have hs60Z : s60.mem.get 0 = 0 := by rw [hs60eq]; exact hr.2.2.1
  have hs60I : s60.mem.get 29 = 1 := by
    rw [hs60eq, hr.2.2.2.1, hs47I]
    exact (rfl : (0 : Word) + 1 = 1)
  have hs60B : s60.mem.get 32 = s.mem.get 24 := by
    rw [hs60eq]
    exact (hr.2.2.2.2 32 (by decide) (by decide) (by decide)).trans hs47B
  have hpres60 : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s60.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs60eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres47 a haB ha18 ha30 haR ha0)
  have hONE60 : s60.mem.get 3 = 1 := (hpres60 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI60 : s60.mem.get 2321 = 4 := (hpres60 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g60 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s60.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres60 (UInt16.ofNat k) n32 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s60) hs60pc hs60h hs60Z hONE60 g60
  have hrun : s64 = runN s60 4 := runN_add_eq s 60 4 64 (by decide)
  have hsTpc : s64.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s64.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s64.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s64.mem.get 2321 = 5 := by
    rw [hrun, hn.2.2.2.1, hDI60]
    exact (rfl : (4 : Word) + 1 = 5)
  have hsTI : s64.mem.get 29 = 1 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs60I
  have hsTB : s64.mem.get 32 = s.mem.get 24 := by
    rw [hrun]; exact (hn.2.2.2.2 32 (by decide) (by decide)).trans hs60B
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s64.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres60 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 4` and `IDX = 1 < ROOM`: write `Q4`
at `BUF+1`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 66 steps. -/
theorem take_store_next_di4_idx1 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 4)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s66 := runN s 66
    s66.pc = 1641 ∧
    s66.halted = false ∧
    s66.mem.get 0 = 0 ∧
    s66.mem.get 33 = s.mem.get 24 ∧
    s66.mem.get 29 = 2 ∧
    s66.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s66.mem.get a = s.mem.get a) := by
  intro s66
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di4 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1824 := ht.1
  have hs16h : s16.halted = false := ht.2.1
  have hs16Z : s16.mem.get 0 = 0 := ht.2.2.1
  have hs16CH : s16.mem.get 30 = s.mem.get 24 := ht.2.2.2.1
  have hs16DI : s16.mem.get 2321 = 4 := ht.2.2.2.2.1
  have hpres16 := ht.2.2.2.2.2
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 1 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem16 : s16.mem.get 28 = s.mem.get 28 := hpres16 28 (by decide) (by decide) (by decide)
  have hIlt : (s16.mem.get 29).toNat < (s16.mem.get 28).toNat := by
    rw [hI16, hRmem16]; simp; exact hRlo
  have hRhi' : (s16.mem.get 28).toNat < 32768 := by rw [hRmem16]; exact hRhi
  have g16 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s16) hs16pc hs16h hs16Z hONE16 hIlt hRhi' g16
  have hrun37 : runN s 37 = runN s16 21 := runN_add_eq s 16 21 37 (by decide)
  let s37 := runN s 37
  have hs37eq : s37 = runN s16 21 := hrun37
  have hs37pc : s37.pc = 1185 := by rw [hs37eq]; exact hhv.1
  have hs37h : s37.halted = false := by rw [hs37eq]; exact hhv.2.1
  have hs37Z : s37.mem.get 0 = 0 := by rw [hs37eq]; exact hhv.2.2.1
  have hs37R : s37.mem.get 2319 = 3 := by rw [hs37eq]; exact hhv.2.2.2.1
  have hs37I : s37.mem.get 29 = 1 := by
    rw [hs37eq, hhv.2.2.2.2.1, hI16]
  have hs37CH : s37.mem.get 30 = s.mem.get 24 := by
    rw [hs37eq, hhv.2.2.2.2.2.1, hs16CH]
  have hpres37 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s37.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs37eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres16 a ha18 ha30 ha0)
  have hONE37 : s37.mem.get 3 = 1 := (hpres37 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI37 : s37.mem.get 2321 = 4 := (hpres37 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g37 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx1 (s := s37) hs37pc hs37h hs37Z hONE37 hs37I g37
  have hrun49 : runN s 49 = runN s37 12 := runN_add_eq s 37 12 49 (by decide)
  let s49 := runN s 49
  have hs49eq : s49 = runN s37 12 := hrun49
  have hs49pc : s49.pc = 1527 := by rw [hs49eq]; exact hs.1
  have hs49h : s49.halted = false := by rw [hs49eq]; exact hs.2.1
  have hs49Z : s49.mem.get 0 = 0 := by rw [hs49eq]; exact hs.2.2.1
  have hs49B : s49.mem.get 33 = s.mem.get 24 := by
    rw [hs49eq, hs.2.2.2.1, hs37CH]
  have hs49I : s49.mem.get 29 = 1 := by rw [hs49eq]; exact hs.2.2.2.2.1
  have hpres49 : ∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s49.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs49eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres37 a ha18 ha30 haR ha0)
  have hONE49 : s49.mem.get 3 = 1 := (hpres49 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR49 : s49.mem.get 2319 = 3 := by
    rw [hs49eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs37R
  have hDI49 : s49.mem.get 2321 = 4 := (hpres49 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g49 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s49.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres49 (UInt16.ofNat k) n33 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s49) hs49pc hs49h hs49Z hONE49 hR49 g49
  have hrun62 : runN s 62 = runN s49 13 := runN_add_eq s 49 13 62 (by decide)
  let s62 := runN s 62
  have hs62eq : s62 = runN s49 13 := hrun62
  have hs62pc : s62.pc = 1893 := by rw [hs62eq]; exact hr.1
  have hs62h : s62.halted = false := by rw [hs62eq]; exact hr.2.1
  have hs62Z : s62.mem.get 0 = 0 := by rw [hs62eq]; exact hr.2.2.1
  have hs62I : s62.mem.get 29 = 2 := by
    rw [hs62eq, hr.2.2.2.1, hs49I]
    exact (rfl : (1 : Word) + 1 = 2)
  have hs62B : s62.mem.get 33 = s.mem.get 24 := by
    rw [hs62eq]
    exact (hr.2.2.2.2 33 (by decide) (by decide) (by decide)).trans hs49B
  have hpres62 : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s62.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs62eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres49 a haB ha18 ha30 haR ha0)
  have hONE62 : s62.mem.get 3 = 1 := (hpres62 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI62 : s62.mem.get 2321 = 4 := (hpres62 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g62 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s62.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres62 (UInt16.ofNat k) n33 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s62) hs62pc hs62h hs62Z hONE62 g62
  have hrun : s66 = runN s62 4 := runN_add_eq s 62 4 66 (by decide)
  have hsTpc : s66.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s66.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s66.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s66.mem.get 2321 = 5 := by
    rw [hrun, hn.2.2.2.1, hDI62]
    exact (rfl : (4 : Word) + 1 = 5)
  have hsTI : s66.mem.get 29 = 2 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs62I
  have hsTB : s66.mem.get 33 = s.mem.get 24 := by
    rw [hrun]; exact (hn.2.2.2.2 33 (by decide) (by decide)).trans hs62B
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s66.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres62 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 4` and `IDX = 2 < ROOM`: write `Q4`
at `BUF+2`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 68 steps. -/
theorem take_store_next_di4_idx2 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 4)
    (hI : s.mem.get 29 = 2)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s68 := runN s 68
    s68.pc = 1641 ∧
    s68.halted = false ∧
    s68.mem.get 0 = 0 ∧
    s68.mem.get 34 = s.mem.get 24 ∧
    s68.mem.get 29 = 3 ∧
    s68.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s68.mem.get a = s.mem.get a) := by
  intro s68
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di4 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1824 := ht.1
  have hs16h : s16.halted = false := ht.2.1
  have hs16Z : s16.mem.get 0 = 0 := ht.2.2.1
  have hs16CH : s16.mem.get 30 = s.mem.get 24 := ht.2.2.2.1
  have hs16DI : s16.mem.get 2321 = 4 := ht.2.2.2.2.1
  have hpres16 := ht.2.2.2.2.2
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 2 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem16 : s16.mem.get 28 = s.mem.get 28 := hpres16 28 (by decide) (by decide) (by decide)
  have hIlt : (s16.mem.get 29).toNat < (s16.mem.get 28).toNat := by
    rw [hI16, hRmem16]; simp; exact hRlo
  have hRhi' : (s16.mem.get 28).toNat < 32768 := by rw [hRmem16]; exact hRhi
  have g16 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s16) hs16pc hs16h hs16Z hONE16 hIlt hRhi' g16
  have hrun37 : runN s 37 = runN s16 21 := runN_add_eq s 16 21 37 (by decide)
  let s37 := runN s 37
  have hs37eq : s37 = runN s16 21 := hrun37
  have hs37pc : s37.pc = 1185 := by rw [hs37eq]; exact hhv.1
  have hs37h : s37.halted = false := by rw [hs37eq]; exact hhv.2.1
  have hs37Z : s37.mem.get 0 = 0 := by rw [hs37eq]; exact hhv.2.2.1
  have hs37R : s37.mem.get 2319 = 3 := by rw [hs37eq]; exact hhv.2.2.2.1
  have hs37I : s37.mem.get 29 = 2 := by
    rw [hs37eq, hhv.2.2.2.2.1, hI16]
  have hs37CH : s37.mem.get 30 = s.mem.get 24 := by
    rw [hs37eq, hhv.2.2.2.2.2.1, hs16CH]
  have hpres37 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s37.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs37eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres16 a ha18 ha30 ha0)
  have hONE37 : s37.mem.get 3 = 1 := (hpres37 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI37 : s37.mem.get 2321 = 4 := (hpres37 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g37 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx2 (s := s37) hs37pc hs37h hs37Z hONE37 hs37I g37
  have hrun51 : runN s 51 = runN s37 14 := runN_add_eq s 37 14 51 (by decide)
  let s51 := runN s 51
  have hs51eq : s51 = runN s37 14 := hrun51
  have hs51pc : s51.pc = 1527 := by rw [hs51eq]; exact hs.1
  have hs51h : s51.halted = false := by rw [hs51eq]; exact hs.2.1
  have hs51Z : s51.mem.get 0 = 0 := by rw [hs51eq]; exact hs.2.2.1
  have hs51B : s51.mem.get 34 = s.mem.get 24 := by
    rw [hs51eq, hs.2.2.2.1, hs37CH]
  have hs51I : s51.mem.get 29 = 2 := by rw [hs51eq]; exact hs.2.2.2.2.1
  have hpres51 : ∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s51.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs51eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres37 a ha18 ha30 haR ha0)
  have hONE51 : s51.mem.get 3 = 1 := (hpres51 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR51 : s51.mem.get 2319 = 3 := by
    rw [hs51eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs37R
  have hDI51 : s51.mem.get 2321 = 4 := (hpres51 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g51 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s51.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres51 (UInt16.ofNat k) n34 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s51) hs51pc hs51h hs51Z hONE51 hR51 g51
  have hrun64 : runN s 64 = runN s51 13 := runN_add_eq s 51 13 64 (by decide)
  let s64 := runN s 64
  have hs64eq : s64 = runN s51 13 := hrun64
  have hs64pc : s64.pc = 1893 := by rw [hs64eq]; exact hr.1
  have hs64h : s64.halted = false := by rw [hs64eq]; exact hr.2.1
  have hs64Z : s64.mem.get 0 = 0 := by rw [hs64eq]; exact hr.2.2.1
  have hs64I : s64.mem.get 29 = 3 := by
    rw [hs64eq, hr.2.2.2.1, hs51I]
    exact (rfl : (2 : Word) + 1 = 3)
  have hs64B : s64.mem.get 34 = s.mem.get 24 := by
    rw [hs64eq]
    exact (hr.2.2.2.2 34 (by decide) (by decide) (by decide)).trans hs51B
  have hpres64 : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s64.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs64eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres51 a haB ha18 ha30 haR ha0)
  have hONE64 : s64.mem.get 3 = 1 := (hpres64 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI64 : s64.mem.get 2321 = 4 := (hpres64 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g64 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s64.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres64 (UInt16.ofNat k) n34 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s64) hs64pc hs64h hs64Z hONE64 g64
  have hrun : s68 = runN s64 4 := runN_add_eq s 64 4 68 (by decide)
  have hsTpc : s68.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s68.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s68.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s68.mem.get 2321 = 5 := by
    rw [hrun, hn.2.2.2.1, hDI64]
    exact (rfl : (4 : Word) + 1 = 5)
  have hsTI : s68.mem.get 29 = 3 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs64I
  have hsTB : s68.mem.get 34 = s.mem.get 24 := by
    rw [hrun]; exact (hn.2.2.2.2 34 (by decide) (by decide)).trans hs64B
  have hpres : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s68.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres64 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 4` and `IDX = 3 < ROOM`: write `Q4`
at `BUF+3`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 70 steps. -/
theorem take_store_next_di4_idx3 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 4)
    (hI : s.mem.get 29 = 3)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s70 := runN s 70
    s70.pc = 1641 ∧
    s70.halted = false ∧
    s70.mem.get 0 = 0 ∧
    s70.mem.get 35 = s.mem.get 24 ∧
    s70.mem.get 29 = 4 ∧
    s70.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s70.mem.get a = s.mem.get a) := by
  intro s70
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di4 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1824 := ht.1
  have hs16h : s16.halted = false := ht.2.1
  have hs16Z : s16.mem.get 0 = 0 := ht.2.2.1
  have hs16CH : s16.mem.get 30 = s.mem.get 24 := ht.2.2.2.1
  have hs16DI : s16.mem.get 2321 = 4 := ht.2.2.2.2.1
  have hpres16 := ht.2.2.2.2.2
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 3 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem16 : s16.mem.get 28 = s.mem.get 28 := hpres16 28 (by decide) (by decide) (by decide)
  have hIlt : (s16.mem.get 29).toNat < (s16.mem.get 28).toNat := by
    rw [hI16, hRmem16]; simp; exact hRlo
  have hRhi' : (s16.mem.get 28).toNat < 32768 := by rw [hRmem16]; exact hRhi
  have g16 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s16) hs16pc hs16h hs16Z hONE16 hIlt hRhi' g16
  have hrun37 : runN s 37 = runN s16 21 := runN_add_eq s 16 21 37 (by decide)
  let s37 := runN s 37
  have hs37eq : s37 = runN s16 21 := hrun37
  have hs37pc : s37.pc = 1185 := by rw [hs37eq]; exact hhv.1
  have hs37h : s37.halted = false := by rw [hs37eq]; exact hhv.2.1
  have hs37Z : s37.mem.get 0 = 0 := by rw [hs37eq]; exact hhv.2.2.1
  have hs37R : s37.mem.get 2319 = 3 := by rw [hs37eq]; exact hhv.2.2.2.1
  have hs37I : s37.mem.get 29 = 3 := by
    rw [hs37eq, hhv.2.2.2.2.1, hI16]
  have hs37CH : s37.mem.get 30 = s.mem.get 24 := by
    rw [hs37eq, hhv.2.2.2.2.2.1, hs16CH]
  have hpres37 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s37.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs37eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres16 a ha18 ha30 ha0)
  have hONE37 : s37.mem.get 3 = 1 := (hpres37 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI37 : s37.mem.get 2321 = 4 := (hpres37 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g37 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx3 (s := s37) hs37pc hs37h hs37Z hONE37 hs37I g37
  have hrun53 : runN s 53 = runN s37 16 := runN_add_eq s 37 16 53 (by decide)
  let s53 := runN s 53
  have hs53eq : s53 = runN s37 16 := hrun53
  have hs53pc : s53.pc = 1527 := by rw [hs53eq]; exact hs.1
  have hs53h : s53.halted = false := by rw [hs53eq]; exact hs.2.1
  have hs53Z : s53.mem.get 0 = 0 := by rw [hs53eq]; exact hs.2.2.1
  have hs53B : s53.mem.get 35 = s.mem.get 24 := by
    rw [hs53eq, hs.2.2.2.1, hs37CH]
  have hs53I : s53.mem.get 29 = 3 := by rw [hs53eq]; exact hs.2.2.2.2.1
  have hpres53 : ∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s53.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs53eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres37 a ha18 ha30 haR ha0)
  have hONE53 : s53.mem.get 3 = 1 := (hpres53 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR53 : s53.mem.get 2319 = 3 := by
    rw [hs53eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs37R
  have hDI53 : s53.mem.get 2321 = 4 := (hpres53 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g53 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s53.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres53 (UInt16.ofNat k) n35 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s53) hs53pc hs53h hs53Z hONE53 hR53 g53
  have hrun66 : runN s 66 = runN s53 13 := runN_add_eq s 53 13 66 (by decide)
  let s66 := runN s 66
  have hs66eq : s66 = runN s53 13 := hrun66
  have hs66pc : s66.pc = 1893 := by rw [hs66eq]; exact hr.1
  have hs66h : s66.halted = false := by rw [hs66eq]; exact hr.2.1
  have hs66Z : s66.mem.get 0 = 0 := by rw [hs66eq]; exact hr.2.2.1
  have hs66I : s66.mem.get 29 = 4 := by
    rw [hs66eq, hr.2.2.2.1, hs53I]
    exact (rfl : (3 : Word) + 1 = 4)
  have hs66B : s66.mem.get 35 = s.mem.get 24 := by
    rw [hs66eq]
    exact (hr.2.2.2.2 35 (by decide) (by decide) (by decide)).trans hs53B
  have hpres66 : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s66.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs66eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres53 a haB ha18 ha30 haR ha0)
  have hONE66 : s66.mem.get 3 = 1 := (hpres66 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI66 : s66.mem.get 2321 = 4 := (hpres66 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g66 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s66.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres66 (UInt16.ofNat k) n35 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s66) hs66pc hs66h hs66Z hONE66 g66
  have hrun : s70 = runN s66 4 := runN_add_eq s 66 4 70 (by decide)
  have hsTpc : s70.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s70.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s70.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s70.mem.get 2321 = 5 := by
    rw [hrun, hn.2.2.2.1, hDI66]
    exact (rfl : (4 : Word) + 1 = 5)
  have hsTI : s70.mem.get 29 = 4 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs66I
  have hsTB : s70.mem.get 35 = s.mem.get 24 := by
    rw [hrun]; exact (hn.2.2.2.2 35 (by decide) (by decide)).trans hs66B
  have hpres : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s70.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres66 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 4` and `IDX = 4 < ROOM`: write `Q4`
at `BUF+4`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 72 steps. -/
theorem take_store_next_di4_idx4 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 4)
    (hI : s.mem.get 29 = 4)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s72 := runN s 72
    s72.pc = 1641 ∧
    s72.halted = false ∧
    s72.mem.get 0 = 0 ∧
    s72.mem.get 36 = s.mem.get 24 ∧
    s72.mem.get 29 = 5 ∧
    s72.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s72.mem.get a = s.mem.get a) := by
  intro s72
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di4 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1824 := ht.1
  have hs16h : s16.halted = false := ht.2.1
  have hs16Z : s16.mem.get 0 = 0 := ht.2.2.1
  have hs16CH : s16.mem.get 30 = s.mem.get 24 := ht.2.2.2.1
  have hs16DI : s16.mem.get 2321 = 4 := ht.2.2.2.2.1
  have hpres16 := ht.2.2.2.2.2
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 4 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem16 : s16.mem.get 28 = s.mem.get 28 := hpres16 28 (by decide) (by decide) (by decide)
  have hIlt : (s16.mem.get 29).toNat < (s16.mem.get 28).toNat := by
    rw [hI16, hRmem16]; simp; exact hRlo
  have hRhi' : (s16.mem.get 28).toNat < 32768 := by rw [hRmem16]; exact hRhi
  have g16 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s16) hs16pc hs16h hs16Z hONE16 hIlt hRhi' g16
  have hrun37 : runN s 37 = runN s16 21 := runN_add_eq s 16 21 37 (by decide)
  let s37 := runN s 37
  have hs37eq : s37 = runN s16 21 := hrun37
  have hs37pc : s37.pc = 1185 := by rw [hs37eq]; exact hhv.1
  have hs37h : s37.halted = false := by rw [hs37eq]; exact hhv.2.1
  have hs37Z : s37.mem.get 0 = 0 := by rw [hs37eq]; exact hhv.2.2.1
  have hs37R : s37.mem.get 2319 = 3 := by rw [hs37eq]; exact hhv.2.2.2.1
  have hs37I : s37.mem.get 29 = 4 := by
    rw [hs37eq, hhv.2.2.2.2.1, hI16]
  have hs37CH : s37.mem.get 30 = s.mem.get 24 := by
    rw [hs37eq, hhv.2.2.2.2.2.1, hs16CH]
  have hpres37 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s37.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs37eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres16 a ha18 ha30 ha0)
  have hONE37 : s37.mem.get 3 = 1 := (hpres37 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI37 : s37.mem.get 2321 = 4 := (hpres37 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g37 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx4 (s := s37) hs37pc hs37h hs37Z hONE37 hs37I g37
  have hrun55 : runN s 55 = runN s37 18 := runN_add_eq s 37 18 55 (by decide)
  let s55 := runN s 55
  have hs55eq : s55 = runN s37 18 := hrun55
  have hs55pc : s55.pc = 1527 := by rw [hs55eq]; exact hs.1
  have hs55h : s55.halted = false := by rw [hs55eq]; exact hs.2.1
  have hs55Z : s55.mem.get 0 = 0 := by rw [hs55eq]; exact hs.2.2.1
  have hs55B : s55.mem.get 36 = s.mem.get 24 := by
    rw [hs55eq, hs.2.2.2.1, hs37CH]
  have hs55I : s55.mem.get 29 = 4 := by rw [hs55eq]; exact hs.2.2.2.2.1
  have hpres55 : ∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s55.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs55eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres37 a ha18 ha30 haR ha0)
  have hONE55 : s55.mem.get 3 = 1 := (hpres55 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR55 : s55.mem.get 2319 = 3 := by
    rw [hs55eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs37R
  have hDI55 : s55.mem.get 2321 = 4 := (hpres55 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g55 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s55.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres55 (UInt16.ofNat k) n36 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s55) hs55pc hs55h hs55Z hONE55 hR55 g55
  have hrun68 : runN s 68 = runN s55 13 := runN_add_eq s 55 13 68 (by decide)
  let s68 := runN s 68
  have hs68eq : s68 = runN s55 13 := hrun68
  have hs68pc : s68.pc = 1893 := by rw [hs68eq]; exact hr.1
  have hs68h : s68.halted = false := by rw [hs68eq]; exact hr.2.1
  have hs68Z : s68.mem.get 0 = 0 := by rw [hs68eq]; exact hr.2.2.1
  have hs68I : s68.mem.get 29 = 5 := by
    rw [hs68eq, hr.2.2.2.1, hs55I]
    exact (rfl : (4 : Word) + 1 = 5)
  have hs68B : s68.mem.get 36 = s.mem.get 24 := by
    rw [hs68eq]
    exact (hr.2.2.2.2 36 (by decide) (by decide) (by decide)).trans hs55B
  have hpres68 : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s68.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs68eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres55 a haB ha18 ha30 haR ha0)
  have hONE68 : s68.mem.get 3 = 1 := (hpres68 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI68 : s68.mem.get 2321 = 4 := (hpres68 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g68 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s68.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres68 (UInt16.ofNat k) n36 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s68) hs68pc hs68h hs68Z hONE68 g68
  have hrun : s72 = runN s68 4 := runN_add_eq s 68 4 72 (by decide)
  have hsTpc : s72.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s72.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s72.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s72.mem.get 2321 = 5 := by
    rw [hrun, hn.2.2.2.1, hDI68]
    exact (rfl : (4 : Word) + 1 = 5)
  have hsTI : s72.mem.get 29 = 5 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs68I
  have hsTB : s72.mem.get 36 = s.mem.get 24 := by
    rw [hrun]; exact (hn.2.2.2.2 36 (by decide) (by decide)).trans hs68B
  have hpres : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s72.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres68 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩


/-- From `TAKE_DIG` with `DI = 4` and `IDX = 5 < ROOM`: write `Q4`
at `BUF+5`, increment `IDX` and `DI`, and return to `DIG_LOOP`. 74 steps. -/
theorem take_store_next_di4_idx5 {s : Machine}
    (hpc : s.pc = 1716)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hDI : s.mem.get 2321 = 4)
    (hI : s.mem.get 29 = 5)
    (hRlo : 5 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s74 := runN s 74
    s74.pc = 1641 ∧
    s74.halted = false ∧
    s74.mem.get 0 = 0 ∧
    s74.mem.get 37 = s.mem.get 24 ∧
    s74.mem.get 29 = 6 ∧
    s74.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s74.mem.get a = s.mem.get a) := by
  intro s74
  have hs0pc : s.pc = 1716 := hpc
  have hs0h : s.halted = false := hh
  have hs0Z : s.mem.get 0 = 0 := hZ
  have ht := take_dig_di4 (s := s) hs0pc hs0h hs0Z hONE hDI
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1824 := ht.1
  have hs16h : s16.halted = false := ht.2.1
  have hs16Z : s16.mem.get 0 = 0 := ht.2.2.1
  have hs16CH : s16.mem.get 30 = s.mem.get 24 := ht.2.2.2.1
  have hs16DI : s16.mem.get 2321 = 4 := ht.2.2.2.2.1
  have hpres16 := ht.2.2.2.2.2
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 5 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hRmem16 : s16.mem.get 28 = s.mem.get 28 := hpres16 28 (by decide) (by decide) (by decide)
  have hIlt : (s16.mem.get 29).toNat < (s16.mem.get 28).toNat := by
    rw [hI16, hRmem16]; simp; exact hRlo
  have hRhi' : (s16.mem.get 28).toNat < 32768 := by rw [hRmem16]; exact hRhi
  have g16 : ∀ k : Nat, 1824 ≤ k → k < 1893 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcodeE k (by omega) (by omega))
  have hhv := have_ch_to_store (s := s16) hs16pc hs16h hs16Z hONE16 hIlt hRhi' g16
  have hrun37 : runN s 37 = runN s16 21 := runN_add_eq s 16 21 37 (by decide)
  let s37 := runN s 37
  have hs37eq : s37 = runN s16 21 := hrun37
  have hs37pc : s37.pc = 1185 := by rw [hs37eq]; exact hhv.1
  have hs37h : s37.halted = false := by rw [hs37eq]; exact hhv.2.1
  have hs37Z : s37.mem.get 0 = 0 := by rw [hs37eq]; exact hhv.2.2.1
  have hs37R : s37.mem.get 2319 = 3 := by rw [hs37eq]; exact hhv.2.2.2.1
  have hs37I : s37.mem.get 29 = 5 := by
    rw [hs37eq, hhv.2.2.2.2.1, hI16]
  have hs37CH : s37.mem.get 30 = s.mem.get 24 := by
    rw [hs37eq, hhv.2.2.2.2.2.1, hs16CH]
  have hpres37 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → s37.mem.get a = s.mem.get a := by
    intro a ha18 ha30 haR ha0
    rw [hs37eq]
    exact (hhv.2.2.2.2.2.2 a ha18 haR ha0).trans (hpres16 a ha18 ha30 ha0)
  have hONE37 : s37.mem.get 3 = 1 := (hpres37 3 (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI37 : s37.mem.get 2321 = 4 := (hpres37 2321 (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g37 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s37.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres37 (UInt16.ofNat k) n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hs := store_ch_idx5 (s := s37) hs37pc hs37h hs37Z hONE37 hs37I g37
  have hrun57 : runN s 57 = runN s37 20 := runN_add_eq s 37 20 57 (by decide)
  let s57 := runN s 57
  have hs57eq : s57 = runN s37 20 := hrun57
  have hs57pc : s57.pc = 1527 := by rw [hs57eq]; exact hs.1
  have hs57h : s57.halted = false := by rw [hs57eq]; exact hs.2.1
  have hs57Z : s57.mem.get 0 = 0 := by rw [hs57eq]; exact hs.2.2.1
  have hs57B : s57.mem.get 37 = s.mem.get 24 := by
    rw [hs57eq, hs.2.2.2.1, hs37CH]
  have hs57I : s57.mem.get 29 = 5 := by rw [hs57eq]; exact hs.2.2.2.2.1
  have hpres57 : ∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s57.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 haR ha0
    rw [hs57eq]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres37 a ha18 ha30 haR ha0)
  have hONE57 : s57.mem.get 3 = 1 := (hpres57 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hR57 : s57.mem.get 2319 = 3 := by
    rw [hs57eq]
    exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hs37R
  have hDI57 : s57.mem.get 2321 = 4 := (hpres57 2321 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g57 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s57.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres57 (UInt16.ofNat k) n37 n18 n30 n2319 n0).trans (hcodeS k (by omega) (by omega))
  have hr := stored_ret_dig (s := s57) hs57pc hs57h hs57Z hONE57 hR57 g57
  have hrun70 : runN s 70 = runN s57 13 := runN_add_eq s 57 13 70 (by decide)
  let s70 := runN s 70
  have hs70eq : s70 = runN s57 13 := hrun70
  have hs70pc : s70.pc = 1893 := by rw [hs70eq]; exact hr.1
  have hs70h : s70.halted = false := by rw [hs70eq]; exact hr.2.1
  have hs70Z : s70.mem.get 0 = 0 := by rw [hs70eq]; exact hr.2.2.1
  have hs70I : s70.mem.get 29 = 6 := by
    rw [hs70eq, hr.2.2.2.1, hs57I]
    exact (rfl : (5 : Word) + 1 = 6)
  have hs70B : s70.mem.get 37 = s.mem.get 24 := by
    rw [hs70eq]
    exact (hr.2.2.2.2 37 (by decide) (by decide) (by decide)).trans hs57B
  have hpres70 : ∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s70.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR ha0
    rw [hs70eq]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres57 a haB ha18 ha30 haR ha0)
  have hONE70 : s70.mem.get 3 = 1 := (hpres70 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hDI70 : s70.mem.get 2321 = 4 := (hpres70 2321 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hDI
  have g70 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s70.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres70 (UInt16.ofNat k) n37 n29 n18 n30 n2319 n0).trans (hcodeE k (by omega) (by omega))
  have hn := dig_next (s := s70) hs70pc hs70h hs70Z hONE70 g70
  have hrun : s74 = runN s70 4 := runN_add_eq s 70 4 74 (by decide)
  have hsTpc : s74.pc = 1641 := by rw [hrun]; exact hn.1
  have hsTh : s74.halted = false := by rw [hrun]; exact hn.2.1
  have hsTZ : s74.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hsTDI : s74.mem.get 2321 = 5 := by
    rw [hrun, hn.2.2.2.1, hDI70]
    exact (rfl : (4 : Word) + 1 = 5)
  have hsTI : s74.mem.get 29 = 6 := by
    rw [hrun]; exact (hn.2.2.2.2 29 (by decide) (by decide)).trans hs70I
  have hsTB : s74.mem.get 37 = s.mem.get 24 := by
    rw [hrun]; exact (hn.2.2.2.2 37 (by decide) (by decide)).trans hs70B
  have hpres : ∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s74.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres70 a haB ha29 ha18 ha30 haR ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `DI < SK` and `DI < 5`: skip the place and return to
`DIG_LOOP` with `DI += 1`. 25 steps. -/
theorem skip_next {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDIlt5 : (s.mem.get 2321).toNat < 5)
    (hDIltSK : (s.mem.get 2321).toNat < (s.mem.get 2320).toNat)
    (hSKhi : (s.mem.get 2320).toNat < 32768)
    (hcode : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s25 := runN s 25
    s25.pc = 1641 ∧
    s25.halted = false ∧
    s25.mem.get 0 = 0 ∧
    s25.mem.get 2321 = s.mem.get 2321 + 1 ∧
    (∀ a, a ≠ 18 → a ≠ 2321 → a ≠ 0 → s25.mem.get a = s.mem.get a) := by
  intro s25
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcode k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = s.mem.get 2321 := hb.2.2.2.1
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hDIltSK10 : (s10.mem.get 2321).toNat < (s10.mem.get 2320).toNat := by
    rw [hs10DI, hSK10]; exact hDIltSK
  have hSKhi10 : (s10.mem.get 2320).toNat < 32768 := by rw [hSK10]; exact hSKhi
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1716 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hsk := dig_body_skip (s := s10) hs10pc hs10h hs10Z hONE10 hDIltSK10 hSKhi10 g10
  have hrun21 : runN s 21 = runN s10 11 := runN_add_eq s 10 11 21 (by decide)
  let s21 := runN s 21
  have hs21eq : s21 = runN s10 11 := hrun21
  have hs21pc : s21.pc = 1893 := by rw [hs21eq]; exact hsk.1
  have hs21h : s21.halted = false := by rw [hs21eq]; exact hsk.2.1
  have hs21Z : s21.mem.get 0 = 0 := by rw [hs21eq]; exact hsk.2.2.1
  have hs21DI : s21.mem.get 2321 = s.mem.get 2321 := by
    rw [hs21eq, hsk.2.2.2.1, hs10DI]
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs21eq]; exact (hsk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE21 : s21.mem.get 3 = 1 := (hpres21 3 (by decide) (by decide)).trans hONE
  have g21 : ∀ k : Nat, 1893 ≤ k → k < 1905 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hn := dig_next (s := s21) hs21pc hs21h hs21Z hONE21 g21
  have hrun : s25 = runN s21 4 := runN_add_eq s 21 4 25 (by decide)
  have hs25pc : s25.pc = 1641 := by rw [hrun]; exact hn.1
  have hs25h : s25.halted = false := by rw [hrun]; exact hn.2.1
  have hs25Z : s25.mem.get 0 = 0 := by rw [hrun]; exact hn.2.2.1
  have hs25DI : s25.mem.get 2321 = s.mem.get 2321 + 1 := by
    rw [hrun, hn.2.2.2.1, hs21DI]
  have hpres : ∀ a, a ≠ 18 → a ≠ 2321 → a ≠ 0 → s25.mem.get a = s.mem.get a := by
    intro a ha18 haDI ha0
    rw [hrun]
    exact (hn.2.2.2.2 a haDI ha0).trans (hpres21 a ha18 ha0)
  exact ⟨hs25pc, hs25h, hs25Z, hs25DI, hpres⟩

end IntFmt
