/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

`AFTER_DIGS` / `WRITE_NUL` / `DONE` block lemmas on the assembled image.
Not end-to-end correctness.
-/

import IntFmt.EmitNdig

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000


private theorem cell1904 (off : Nat) (h : off < 16) :
    intfmtImage[1904 + off]! = decChunk119[off]! :=
  extract_chunk 1904 decChunk119 image_chunk119 off h (by decide)


private theorem cell1920 (off : Nat) (h : off < 16) :
    intfmtImage[1920 + off]! = decChunk120[off]! :=
  extract_chunk 1920 decChunk120 image_chunk120 off h (by decide)


private theorem cell1936 (off : Nat) (h : off < 16) :
    intfmtImage[1936 + off]! = decChunk121[off]! :=
  extract_chunk 1936 decChunk121 image_chunk121 off h (by decide)


private theorem cell1952 (off : Nat) (h : off < 16) :
    intfmtImage[1952 + off]! = decChunk122[off]! :=
  extract_chunk 1952 decChunk122 image_chunk122 off h (by decide)


private theorem cell1968 (off : Nat) (h : off < 16) :
    intfmtImage[1968 + off]! = decChunk123[off]! :=
  extract_chunk 1968 decChunk123 image_chunk123 off h (by decide)


private theorem cell1984 (off : Nat) (h : off < 16) :
    intfmtImage[1984 + off]! = decChunk124[off]! :=
  extract_chunk 1984 decChunk124 image_chunk124 off h (by decide)


private theorem cell2000 (off : Nat) (h : off < 16) :
    intfmtImage[2000 + off]! = decChunk125[off]! :=
  extract_chunk 2000 decChunk125 image_chunk125 off h (by decide)


private theorem cell2016 (off : Nat) (h : off < 16) :
    intfmtImage[2016 + off]! = decChunk126[off]! :=
  extract_chunk 2016 decChunk126 image_chunk126 off h (by decide)


private theorem cell2032 (off : Nat) (h : off < 16) :
    intfmtImage[2032 + off]! = decChunk127[off]! :=
  extract_chunk 2032 decChunk127 image_chunk127 off h (by decide)


private theorem cell2048 (off : Nat) (h : off < 16) :
    intfmtImage[2048 + off]! = decChunk128[off]! :=
  extract_chunk 2048 decChunk128 image_chunk128 off h (by decide)


private theorem cell2064 (off : Nat) (h : off < 16) :
    intfmtImage[2064 + off]! = decChunk129[off]! :=
  extract_chunk 2064 decChunk129 image_chunk129 off h (by decide)


private theorem cell2080 (off : Nat) (h : off < 16) :
    intfmtImage[2080 + off]! = decChunk130[off]! :=
  extract_chunk 2080 decChunk130 image_chunk130 off h (by decide)


private theorem cell2096 (off : Nat) (h : off < 16) :
    intfmtImage[2096 + off]! = decChunk131[off]! :=
  extract_chunk 2096 decChunk131 image_chunk131 off h (by decide)


private theorem cell2112 (off : Nat) (h : off < 16) :
    intfmtImage[2112 + off]! = decChunk132[off]! :=
  extract_chunk 2112 decChunk132 image_chunk132 off h (by decide)


private theorem cell2128 (off : Nat) (h : off < 16) :
    intfmtImage[2128 + off]! = decChunk133[off]! :=
  extract_chunk 2128 decChunk133 image_chunk133 off h (by decide)


private theorem cell2144 (off : Nat) (h : off < 16) :
    intfmtImage[2144 + off]! = decChunk134[off]! :=
  extract_chunk 2144 decChunk134 image_chunk134 off h (by decide)


private theorem cell2160 (off : Nat) (h : off < 16) :
    intfmtImage[2160 + off]! = decChunk135[off]! :=
  extract_chunk 2160 decChunk135 image_chunk135 off h (by decide)


private theorem cell2176 (off : Nat) (h : off < 16) :
    intfmtImage[2176 + off]! = decChunk136[off]! :=
  extract_chunk 2176 decChunk136 image_chunk136 off h (by decide)


private theorem cell2192 (off : Nat) (h : off < 16) :
    intfmtImage[2192 + off]! = decChunk137[off]! :=
  extract_chunk 2192 decChunk137 image_chunk137 off h (by decide)


private theorem cell2208 (off : Nat) (h : off < 16) :
    intfmtImage[2208 + off]! = decChunk138[off]! :=
  extract_chunk 2208 decChunk138 image_chunk138 off h (by decide)


private theorem cell2224 (off : Nat) (h : off < 16) :
    intfmtImage[2224 + off]! = decChunk139[off]! :=
  extract_chunk 2224 decChunk139 image_chunk139 off h (by decide)


private theorem cell2240 (off : Nat) (h : off < 16) :
    intfmtImage[2240 + off]! = decChunk140[off]! :=
  extract_chunk 2240 decChunk140 image_chunk140 off h (by decide)


private theorem cell2256 (off : Nat) (h : off < 16) :
    intfmtImage[2256 + off]! = decChunk141[off]! :=
  extract_chunk 2256 decChunk141 image_chunk141 off h (by decide)


private theorem cell2272 (off : Nat) (h : off < 16) :
    intfmtImage[2272 + off]! = decChunk142[off]! :=
  extract_chunk 2272 decChunk142 image_chunk142 off h (by decide)


private theorem cell2288 (off : Nat) (h : off < 16) :
    intfmtImage[2288 + off]! = decChunk143[off]! :=
  extract_chunk 2288 decChunk143 image_chunk143 off h (by decide)


private theorem cell2304 (off : Nat) (h : off < 16) :
    intfmtImage[2304 + off]! = decChunk144[off]! :=
  extract_chunk 2304 decChunk144 image_chunk144 off h (by decide)

/-- MOV LEN T at AFTER_DIGS (pc 1905). -/
theorem wn_mov_LEN_T_1905 {s : Machine}
    (hpc : s.pc = 1905)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1905 ≤ k → k < 1917 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1917 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 16 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 16 = s.mem.get 16 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1905 :=
    hpc.trans (rfl : (1905 : Word) = UInt16.ofNat 1905)
  have g (k : Nat) (h1 : 1905 ≤ k) (h2 : k < 1917) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1905 + off) :=
    word_pc_off 1905 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk119[1]! = 18 := rfl
    exact (g 1905 (by decide) (by decide)).trans ((cell1904 1 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk119[2]! = 18 := rfl
    exact (g 1906 (by decide) (by decide)).trans ((cell1904 2 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk119[3]! = 1908 := rfl
    have hv : (1908 : Word) = UInt16.ofNat 1908 := rfl
    exact (g 1907 (by decide) (by decide)).trans ((cell1904 3 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 16 := by
    rw [poff 3 (by decide)]
    have hval : decChunk119[4]! = 16 := rfl
    exact (g 1908 (by decide) (by decide)).trans ((cell1904 4 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk119[5]! = 0 := rfl
    exact (g 1909 (by decide) (by decide)).trans ((cell1904 5 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk119[6]! = 1911 := rfl
    have hv : (1911 : Word) = UInt16.ofNat 1911 := rfl
    exact (g 1910 (by decide) (by decide)).trans ((cell1904 6 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk119[7]! = 0 := rfl
    exact (g 1911 (by decide) (by decide)).trans ((cell1904 7 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk119[8]! = 18 := rfl
    exact (g 1912 (by decide) (by decide)).trans ((cell1904 8 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk119[9]! = 1914 := rfl
    have hv : (1914 : Word) = UInt16.ofNat 1914 := rfl
    exact (g 1913 (by decide) (by decide)).trans ((cell1904 9 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk119[10]! = 0 := rfl
    exact (g 1914 (by decide) (by decide)).trans ((cell1904 10 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk119[11]! = 0 := rfl
    exact (g 1915 (by decide) (by decide)).trans ((cell1904 11 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk119[12]! = 1917 := rfl
    have hv : (1917 : Word) = UInt16.ofNat 1917 := rfl
    exact (g 1916 (by decide) (by decide)).trans ((cell1904 12 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1905 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1905 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 16) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1917 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1917 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1917 = (1917 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- SUB CAP T at pc 1917. -/
theorem wn_sub_CAP_T_1917 {s : Machine}
    (hpc : s.pc = 1917)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1917 ≤ k → k < 1920 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 13)
        pc := 1920 } := by
  have hp : s.pc = UInt16.ofNat 1917 :=
    hpc.trans (rfl : (1917 : Word) = UInt16.ofNat 1917)
  have g (k : Nat) (h1 : 1917 ≤ k) (h2 : k < 1920) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 13 := by
    rw [hp]
    have hval : decChunk119[13]! = 13 := rfl
    exact (g 1917 (by decide) (by decide)).trans ((cell1904 13 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1918 : Word) := by simp [hpc]
    rw [this, (rfl : (1918 : Word) = UInt16.ofNat 1918)]
    have hval : decChunk119[14]! = 18 := rfl
    exact (g 1918 (by decide) (by decide)).trans ((cell1904 14 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1919 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1920 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1919 : Word) = UInt16.ofNat 1919)]
    have hval : decChunk119[15]! = 1920 := rfl
    have hv : (1920 : Word) = UInt16.ofNat 1920 := rfl
    exact (g 1919 (by decide) (by decide)).trans ((cell1904 15 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 13) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1920 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T NUL_AT_LEN at pc 1920. -/
theorem wn_enc_jlez_1920 {s : Machine}
    (hpc : s.pc = 1920)
    (hcode : ∀ k : Nat, 1920 ≤ k → k < 1920+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1926 := by
  have hp : s.pc = UInt16.ofNat 1920 :=
    hpc.trans (rfl : (1920 : Word) = UInt16.ofNat 1920)
  have g (k : Nat) (h1 : 1920 ≤ k) (h2 : k < 1920+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk120[0]! = 0 := rfl
    exact (g 1920 (by decide) (by decide)).trans ((cell1920 0 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1921 : Word) := by simp [hpc]
    rw [this, (rfl : (1921 : Word) = UInt16.ofNat 1921)]
    have hval : decChunk120[1]! = 18 := rfl
    exact (g 1921 (by decide) (by decide)).trans ((cell1920 1 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1926 := by
    have : s.pc + 2 = (1922 : Word) := by simp [hpc]
    rw [this, (rfl : (1922 : Word) = UInt16.ofNat 1922)]
    have hval : decChunk120[2]! = 1926 := rfl
    exact (g 1922 (by decide) (by decide)).trans ((cell1920 2 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP NUL_AT_ROOM at pc 1923. -/
theorem wn_enc_jmp_1923 {s : Machine}
    (hpc : s.pc = 1923)
    (hcode : ∀ k : Nat, 1923 ≤ k → k < 1923+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1956 := by
  have hp : s.pc = UInt16.ofNat 1923 :=
    hpc.trans (rfl : (1923 : Word) = UInt16.ofNat 1923)
  have g (k : Nat) (h1 : 1923 ≤ k) (h2 : k < 1923+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk120[3]! = 0 := rfl
    exact (g 1923 (by decide) (by decide)).trans ((cell1920 3 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1924 : Word) := by simp [hpc]
    rw [this, (rfl : (1924 : Word) = UInt16.ofNat 1924)]
    have hval : decChunk120[4]! = 0 := rfl
    exact (g 1924 (by decide) (by decide)).trans ((cell1920 4 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1956 := by
    have : s.pc + 2 = (1925 : Word) := by simp [hpc]
    rw [this, (rfl : (1925 : Word) = UInt16.ofNat 1925)]
    have hval : decChunk120[5]! = 1956 := rfl
    exact (g 1925 (by decide) (by decide)).trans ((cell1920 5 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- INC T at NUL_AT_LEN (pc 1926). -/
theorem wn_inc_T_1926 {s : Machine}
    (hpc : s.pc = 1926)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1926 ≤ k → k < 1935 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1935 ∧
    s3.halted = false ∧
    s3.mem.get 18 = s.mem.get 18 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1926 :=
    hpc.trans (rfl : (1926 : Word) = UInt16.ofNat 1926)
  have g (k : Nat) (h1 : 1926 ≤ k) (h2 : k < 1935) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1926 + off) :=
    word_pc_off 1926 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk120[6]! = 3 := rfl
    exact (g 1926 (by decide) (by decide)).trans ((cell1920 6 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk120[7]! = 0 := rfl
    exact (g 1927 (by decide) (by decide)).trans ((cell1920 7 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk120[8]! = 1929 := rfl
    have hv : (1929 : Word) = UInt16.ofNat 1929 := rfl
    exact (g 1928 (by decide) (by decide)).trans ((cell1920 8 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk120[9]! = 0 := rfl
    exact (g 1929 (by decide) (by decide)).trans ((cell1920 9 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 18 := by
    rw [poff 4 (by decide)]
    have hval : decChunk120[10]! = 18 := rfl
    exact (g 1930 (by decide) (by decide)).trans ((cell1920 10 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk120[11]! = 1932 := rfl
    have hv : (1932 : Word) = UInt16.ofNat 1932 := rfl
    exact (g 1931 (by decide) (by decide)).trans ((cell1920 11 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk120[12]! = 0 := rfl
    exact (g 1932 (by decide) (by decide)).trans ((cell1920 12 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk120[13]! = 0 := rfl
    exact (g 1933 (by decide) (by decide)).trans ((cell1920 13 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk120[14]! = 1935 := rfl
    have hv : (1935 : Word) = UInt16.ofNat 1935 := rfl
    exact (g 1934 (by decide) (by decide)).trans ((cell1920 14 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1926 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1926 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1935 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1935 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1935 = (1935 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 18 = s.mem.get 18 + 1 := by
    have : s.mem.get 18 + s.mem.get 3 = s.mem.get 18 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- JLEZ T NUL_USE_LEN at pc 1935. -/
theorem wn_enc_jlez_1935 {s : Machine}
    (hpc : s.pc = 1935)
    (hcode : ∀ k : Nat, 1935 ≤ k → k < 1935+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1941 := by
  have hp : s.pc = UInt16.ofNat 1935 :=
    hpc.trans (rfl : (1935 : Word) = UInt16.ofNat 1935)
  have g (k : Nat) (h1 : 1935 ≤ k) (h2 : k < 1935+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk120[15]! = 0 := rfl
    exact (g 1935 (by decide) (by decide)).trans ((cell1920 15 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1936 : Word) := by simp [hpc]
    rw [this, (rfl : (1936 : Word) = UInt16.ofNat 1936)]
    have hval : decChunk121[0]! = 18 := rfl
    exact (g 1936 (by decide) (by decide)).trans ((cell1936 0 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1941 := by
    have : s.pc + 2 = (1937 : Word) := by simp [hpc]
    rw [this, (rfl : (1937 : Word) = UInt16.ofNat 1937)]
    have hval : decChunk121[1]! = 1941 := rfl
    exact (g 1937 (by decide) (by decide)).trans ((cell1936 1 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP NUL_AT_ROOM at pc 1938. -/
theorem wn_enc_jmp_1938 {s : Machine}
    (hpc : s.pc = 1938)
    (hcode : ∀ k : Nat, 1938 ≤ k → k < 1938+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1956 := by
  have hp : s.pc = UInt16.ofNat 1938 :=
    hpc.trans (rfl : (1938 : Word) = UInt16.ofNat 1938)
  have g (k : Nat) (h1 : 1938 ≤ k) (h2 : k < 1938+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk121[2]! = 0 := rfl
    exact (g 1938 (by decide) (by decide)).trans ((cell1936 2 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1939 : Word) := by simp [hpc]
    rw [this, (rfl : (1939 : Word) = UInt16.ofNat 1939)]
    have hval : decChunk121[3]! = 0 := rfl
    exact (g 1939 (by decide) (by decide)).trans ((cell1936 3 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1956 := by
    have : s.pc + 2 = (1940 : Word) := by simp [hpc]
    rw [this, (rfl : (1940 : Word) = UInt16.ofNat 1940)]
    have hval : decChunk121[4]! = 1956 := rfl
    exact (g 1940 (by decide) (by decide)).trans ((cell1936 4 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV LEN IDX at NUL_USE_LEN (pc 1941). -/
theorem wn_mov_LEN_IDX_1941 {s : Machine}
    (hpc : s.pc = 1941)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1941 ≤ k → k < 1953 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1953 ∧
    s4.halted = false ∧
    s4.mem.get 29 = s.mem.get 16 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 16 = s.mem.get 16 ∧
    (∀ a, a ≠ 29 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1941 :=
    hpc.trans (rfl : (1941 : Word) = UInt16.ofNat 1941)
  have g (k : Nat) (h1 : 1941 ≤ k) (h2 : k < 1953) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1941 + off) :=
    word_pc_off 1941 off hp (by omega)
  have m0 : s.mem.get s.pc = 29 := by
    rw [hp]
    have hval : decChunk121[5]! = 29 := rfl
    exact (g 1941 (by decide) (by decide)).trans ((cell1936 5 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 29 := by
    rw [poff 1 (by decide)]
    have hval : decChunk121[6]! = 29 := rfl
    exact (g 1942 (by decide) (by decide)).trans ((cell1936 6 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk121[7]! = 1944 := rfl
    have hv : (1944 : Word) = UInt16.ofNat 1944 := rfl
    exact (g 1943 (by decide) (by decide)).trans ((cell1936 7 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 16 := by
    rw [poff 3 (by decide)]
    have hval : decChunk121[8]! = 16 := rfl
    exact (g 1944 (by decide) (by decide)).trans ((cell1936 8 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk121[9]! = 0 := rfl
    exact (g 1945 (by decide) (by decide)).trans ((cell1936 9 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk121[10]! = 1947 := rfl
    have hv : (1947 : Word) = UInt16.ofNat 1947 := rfl
    exact (g 1946 (by decide) (by decide)).trans ((cell1936 10 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk121[11]! = 0 := rfl
    exact (g 1947 (by decide) (by decide)).trans ((cell1936 11 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 29 := by
    rw [poff 7 (by decide)]
    have hval : decChunk121[12]! = 29 := rfl
    exact (g 1948 (by decide) (by decide)).trans ((cell1936 12 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk121[13]! = 1950 := rfl
    have hv : (1950 : Word) = UInt16.ofNat 1950 := rfl
    exact (g 1949 (by decide) (by decide)).trans ((cell1936 13 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk121[14]! = 0 := rfl
    exact (g 1950 (by decide) (by decide)).trans ((cell1936 14 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk121[15]! = 0 := rfl
    exact (g 1951 (by decide) (by decide)).trans ((cell1936 15 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk122[0]! = 1953 := rfl
    have hv : (1953 : Word) = UInt16.ofNat 1953 := rfl
    exact (g 1952 (by decide) (by decide)).trans ((cell1952 0 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (29 : Word) := by
    intro i hi
    have : (29 : Word) = UInt16.ofNat 29 := rfl
    rw [this]
    exact pc_off_ne 1941 i 29 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1941 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 16) (dst := 29)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1953 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1953 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1953 = (1953 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP WRITE_NUL at pc 1953. -/
theorem wn_enc_jmp_1953 {s : Machine}
    (hpc : s.pc = 1953)
    (hcode : ∀ k : Nat, 1953 ≤ k → k < 1953+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1971 := by
  have hp : s.pc = UInt16.ofNat 1953 :=
    hpc.trans (rfl : (1953 : Word) = UInt16.ofNat 1953)
  have g (k : Nat) (h1 : 1953 ≤ k) (h2 : k < 1953+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk122[1]! = 0 := rfl
    exact (g 1953 (by decide) (by decide)).trans ((cell1952 1 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1954 : Word) := by simp [hpc]
    rw [this, (rfl : (1954 : Word) = UInt16.ofNat 1954)]
    have hval : decChunk122[2]! = 0 := rfl
    exact (g 1954 (by decide) (by decide)).trans ((cell1952 2 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1971 := by
    have : s.pc + 2 = (1955 : Word) := by simp [hpc]
    rw [this, (rfl : (1955 : Word) = UInt16.ofNat 1955)]
    have hval : decChunk122[3]! = 1971 := rfl
    exact (g 1955 (by decide) (by decide)).trans ((cell1952 3 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV ROOM IDX at NUL_AT_ROOM (pc 1956). -/
theorem wn_mov_ROOM_IDX_1956 {s : Machine}
    (hpc : s.pc = 1956)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1956 ≤ k → k < 1968 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1968 ∧
    s4.halted = false ∧
    s4.mem.get 29 = s.mem.get 28 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 28 = s.mem.get 28 ∧
    (∀ a, a ≠ 29 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1956 :=
    hpc.trans (rfl : (1956 : Word) = UInt16.ofNat 1956)
  have g (k : Nat) (h1 : 1956 ≤ k) (h2 : k < 1968) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1956 + off) :=
    word_pc_off 1956 off hp (by omega)
  have m0 : s.mem.get s.pc = 29 := by
    rw [hp]
    have hval : decChunk122[4]! = 29 := rfl
    exact (g 1956 (by decide) (by decide)).trans ((cell1952 4 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 29 := by
    rw [poff 1 (by decide)]
    have hval : decChunk122[5]! = 29 := rfl
    exact (g 1957 (by decide) (by decide)).trans ((cell1952 5 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk122[6]! = 1959 := rfl
    have hv : (1959 : Word) = UInt16.ofNat 1959 := rfl
    exact (g 1958 (by decide) (by decide)).trans ((cell1952 6 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 28 := by
    rw [poff 3 (by decide)]
    have hval : decChunk122[7]! = 28 := rfl
    exact (g 1959 (by decide) (by decide)).trans ((cell1952 7 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk122[8]! = 0 := rfl
    exact (g 1960 (by decide) (by decide)).trans ((cell1952 8 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk122[9]! = 1962 := rfl
    have hv : (1962 : Word) = UInt16.ofNat 1962 := rfl
    exact (g 1961 (by decide) (by decide)).trans ((cell1952 9 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk122[10]! = 0 := rfl
    exact (g 1962 (by decide) (by decide)).trans ((cell1952 10 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 29 := by
    rw [poff 7 (by decide)]
    have hval : decChunk122[11]! = 29 := rfl
    exact (g 1963 (by decide) (by decide)).trans ((cell1952 11 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk122[12]! = 1965 := rfl
    have hv : (1965 : Word) = UInt16.ofNat 1965 := rfl
    exact (g 1964 (by decide) (by decide)).trans ((cell1952 12 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk122[13]! = 0 := rfl
    exact (g 1965 (by decide) (by decide)).trans ((cell1952 13 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk122[14]! = 0 := rfl
    exact (g 1966 (by decide) (by decide)).trans ((cell1952 14 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk122[15]! = 1968 := rfl
    have hv : (1968 : Word) = UInt16.ofNat 1968 := rfl
    exact (g 1967 (by decide) (by decide)).trans ((cell1952 15 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (29 : Word) := by
    intro i hi
    have : (29 : Word) = UInt16.ofNat 29 := rfl
    rw [this]
    exact pc_off_ne 1956 i 29 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1956 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 28) (dst := 29)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1968 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1968 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1968 = (1968 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP WRITE_NUL at pc 1968. -/
theorem wn_enc_jmp_1968 {s : Machine}
    (hpc : s.pc = 1968)
    (hcode : ∀ k : Nat, 1968 ≤ k → k < 1968+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1971 := by
  have hp : s.pc = UInt16.ofNat 1968 :=
    hpc.trans (rfl : (1968 : Word) = UInt16.ofNat 1968)
  have g (k : Nat) (h1 : 1968 ≤ k) (h2 : k < 1968+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk123[0]! = 0 := rfl
    exact (g 1968 (by decide) (by decide)).trans ((cell1968 0 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1969 : Word) := by simp [hpc]
    rw [this, (rfl : (1969 : Word) = UInt16.ofNat 1969)]
    have hval : decChunk123[1]! = 0 := rfl
    exact (g 1969 (by decide) (by decide)).trans ((cell1968 1 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1971 := by
    have : s.pc + 2 = (1970 : Word) := by simp [hpc]
    rw [this, (rfl : (1970 : Word) = UInt16.ofNat 1970)]
    have hval : decChunk123[2]! = 1971 := rfl
    exact (g 1970 (by decide) (by decide)).trans ((cell1968 2 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩


/-- ZERO CH at WRITE_NUL (pc 1971). -/
theorem wn_zero_CH_1971 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 1974 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s = { s with mem := s.mem.set 30 0, pc := 1974 } := by
  have hp : s.pc = UInt16.ofNat 1971 :=
    hpc.trans (rfl : (1971 : Word) = UInt16.ofNat 1971)
  have g (k : Nat) (h1 : 1971 ≤ k) (h2 : k < 1974) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 30 := by
    rw [hp]
    have hval : decChunk123[3]! = 30 := rfl
    exact (g 1971 (by decide) (by decide)).trans ((cell1968 3 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 30 := by
    have : s.pc + 1 = (1972 : Word) := by simp [hpc]
    rw [this, (rfl : (1972 : Word) = UInt16.ofNat 1972)]
    have hval : decChunk123[4]! = 30 := rfl
    exact (g 1972 (by decide) (by decide)).trans ((cell1968 4 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1973 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1974 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1973 : Word) = UInt16.ofNat 1973)]
    have hval : decChunk123[5]! = 1974 := rfl
    have hv : (1974 : Word) = UInt16.ofNat 1974 := rfl
    exact (g 1973 (by decide) (by decide)).trans ((cell1968 5 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hz :=
    step_ZERO (s := s) (x := 30) hh hpc0 ha hb hc (by decide)
  have hpc' : s.pc + 3 = (1974 : Word) := by simp [hpc]
  rw [hz, hpc']

/-- MOV IDX T at WRITE_NUL (pc 1974). -/
theorem wn_mov_IDX_T_1974 {s : Machine}
    (hpc : s.pc = 1974)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1974 ≤ k → k < 1986 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1986 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 29 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 29 = s.mem.get 29 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1974 :=
    hpc.trans (rfl : (1974 : Word) = UInt16.ofNat 1974)
  have g (k : Nat) (h1 : 1974 ≤ k) (h2 : k < 1986) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1974 + off) :=
    word_pc_off 1974 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk123[6]! = 18 := rfl
    exact (g 1974 (by decide) (by decide)).trans ((cell1968 6 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk123[7]! = 18 := rfl
    exact (g 1975 (by decide) (by decide)).trans ((cell1968 7 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk123[8]! = 1977 := rfl
    have hv : (1977 : Word) = UInt16.ofNat 1977 := rfl
    exact (g 1976 (by decide) (by decide)).trans ((cell1968 8 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 29 := by
    rw [poff 3 (by decide)]
    have hval : decChunk123[9]! = 29 := rfl
    exact (g 1977 (by decide) (by decide)).trans ((cell1968 9 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk123[10]! = 0 := rfl
    exact (g 1978 (by decide) (by decide)).trans ((cell1968 10 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk123[11]! = 1980 := rfl
    have hv : (1980 : Word) = UInt16.ofNat 1980 := rfl
    exact (g 1979 (by decide) (by decide)).trans ((cell1968 11 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk123[12]! = 0 := rfl
    exact (g 1980 (by decide) (by decide)).trans ((cell1968 12 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk123[13]! = 18 := rfl
    exact (g 1981 (by decide) (by decide)).trans ((cell1968 13 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk123[14]! = 1983 := rfl
    have hv : (1983 : Word) = UInt16.ofNat 1983 := rfl
    exact (g 1982 (by decide) (by decide)).trans ((cell1968 14 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk123[15]! = 0 := rfl
    exact (g 1983 (by decide) (by decide)).trans ((cell1968 15 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk124[0]! = 0 := rfl
    exact (g 1984 (by decide) (by decide)).trans ((cell1984 0 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk124[1]! = 1986 := rfl
    have hv : (1986 : Word) = UInt16.ofNat 1986 := rfl
    exact (g 1985 (by decide) (by decide)).trans ((cell1984 1 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1974 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1974 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 29) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1986 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1986 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1986 = (1986 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JLEZ T N0 at pc 1986. -/
theorem wn_enc_jlez_1986 {s : Machine}
    (hpc : s.pc = 1986)
    (hcode : ∀ k : Nat, 1986 ≤ k → k < 1986+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2076 := by
  have hp : s.pc = UInt16.ofNat 1986 :=
    hpc.trans (rfl : (1986 : Word) = UInt16.ofNat 1986)
  have g (k : Nat) (h1 : 1986 ≤ k) (h2 : k < 1986+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk124[2]! = 0 := rfl
    exact (g 1986 (by decide) (by decide)).trans ((cell1984 2 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1987 : Word) := by simp [hpc]
    rw [this, (rfl : (1987 : Word) = UInt16.ofNat 1987)]
    have hval : decChunk124[3]! = 18 := rfl
    exact (g 1987 (by decide) (by decide)).trans ((cell1984 3 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2076 := by
    have : s.pc + 2 = (1988 : Word) := by simp [hpc]
    rw [this, (rfl : (1988 : Word) = UInt16.ofNat 1988)]
    have hval : decChunk124[4]! = 2076 := rfl
    exact (g 1988 (by decide) (by decide)).trans ((cell1984 4 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1989 (WRITE_NUL dispatch). -/
theorem wn_dec_T_1989 {s : Machine}
    (hpc : s.pc = 1989)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1989 ≤ k → k < 1992 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1992 } := by
  have hp : s.pc = UInt16.ofNat 1989 :=
    hpc.trans (rfl : (1989 : Word) = UInt16.ofNat 1989)
  have g (k : Nat) (h1 : 1989 ≤ k) (h2 : k < 1992) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk124[5]! = 3 := rfl
    exact (g 1989 (by decide) (by decide)).trans ((cell1984 5 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1990 : Word) := by simp [hpc]
    rw [this, (rfl : (1990 : Word) = UInt16.ofNat 1990)]
    have hval : decChunk124[6]! = 18 := rfl
    exact (g 1990 (by decide) (by decide)).trans ((cell1984 6 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1991 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1992 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1991 : Word) = UInt16.ofNat 1991)]
    have hval : decChunk124[7]! = 1992 := rfl
    have hv : (1992 : Word) = UInt16.ofNat 1992 := rfl
    exact (g 1991 (by decide) (by decide)).trans ((cell1984 7 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1992 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N1 at pc 1992. -/
theorem wn_enc_jlez_1992 {s : Machine}
    (hpc : s.pc = 1992)
    (hcode : ∀ k : Nat, 1992 ≤ k → k < 1992+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2091 := by
  have hp : s.pc = UInt16.ofNat 1992 :=
    hpc.trans (rfl : (1992 : Word) = UInt16.ofNat 1992)
  have g (k : Nat) (h1 : 1992 ≤ k) (h2 : k < 1992+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk124[8]! = 0 := rfl
    exact (g 1992 (by decide) (by decide)).trans ((cell1984 8 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1993 : Word) := by simp [hpc]
    rw [this, (rfl : (1993 : Word) = UInt16.ofNat 1993)]
    have hval : decChunk124[9]! = 18 := rfl
    exact (g 1993 (by decide) (by decide)).trans ((cell1984 9 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2091 := by
    have : s.pc + 2 = (1994 : Word) := by simp [hpc]
    rw [this, (rfl : (1994 : Word) = UInt16.ofNat 1994)]
    have hval : decChunk124[10]! = 2091 := rfl
    exact (g 1994 (by decide) (by decide)).trans ((cell1984 10 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1995 (WRITE_NUL dispatch). -/
theorem wn_dec_T_1995 {s : Machine}
    (hpc : s.pc = 1995)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1995 ≤ k → k < 1998 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1998 } := by
  have hp : s.pc = UInt16.ofNat 1995 :=
    hpc.trans (rfl : (1995 : Word) = UInt16.ofNat 1995)
  have g (k : Nat) (h1 : 1995 ≤ k) (h2 : k < 1998) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk124[11]! = 3 := rfl
    exact (g 1995 (by decide) (by decide)).trans ((cell1984 11 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1996 : Word) := by simp [hpc]
    rw [this, (rfl : (1996 : Word) = UInt16.ofNat 1996)]
    have hval : decChunk124[12]! = 18 := rfl
    exact (g 1996 (by decide) (by decide)).trans ((cell1984 12 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1997 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1998 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1997 : Word) = UInt16.ofNat 1997)]
    have hval : decChunk124[13]! = 1998 := rfl
    have hv : (1998 : Word) = UInt16.ofNat 1998 := rfl
    exact (g 1997 (by decide) (by decide)).trans ((cell1984 13 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1998 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N2 at pc 1998. -/
theorem wn_enc_jlez_1998 {s : Machine}
    (hpc : s.pc = 1998)
    (hcode : ∀ k : Nat, 1998 ≤ k → k < 1998+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2106 := by
  have hp : s.pc = UInt16.ofNat 1998 :=
    hpc.trans (rfl : (1998 : Word) = UInt16.ofNat 1998)
  have g (k : Nat) (h1 : 1998 ≤ k) (h2 : k < 1998+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk124[14]! = 0 := rfl
    exact (g 1998 (by decide) (by decide)).trans ((cell1984 14 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1999 : Word) := by simp [hpc]
    rw [this, (rfl : (1999 : Word) = UInt16.ofNat 1999)]
    have hval : decChunk124[15]! = 18 := rfl
    exact (g 1999 (by decide) (by decide)).trans ((cell1984 15 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2106 := by
    have : s.pc + 2 = (2000 : Word) := by simp [hpc]
    rw [this, (rfl : (2000 : Word) = UInt16.ofNat 2000)]
    have hval : decChunk125[0]! = 2106 := rfl
    exact (g 2000 (by decide) (by decide)).trans ((cell2000 0 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 2001 (WRITE_NUL dispatch). -/
theorem wn_dec_T_2001 {s : Machine}
    (hpc : s.pc = 2001)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 2001 ≤ k → k < 2004 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 2004 } := by
  have hp : s.pc = UInt16.ofNat 2001 :=
    hpc.trans (rfl : (2001 : Word) = UInt16.ofNat 2001)
  have g (k : Nat) (h1 : 2001 ≤ k) (h2 : k < 2004) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk125[1]! = 3 := rfl
    exact (g 2001 (by decide) (by decide)).trans ((cell2000 1 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2002 : Word) := by simp [hpc]
    rw [this, (rfl : (2002 : Word) = UInt16.ofNat 2002)]
    have hval : decChunk125[2]! = 18 := rfl
    exact (g 2002 (by decide) (by decide)).trans ((cell2000 2 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (2003 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (2004 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (2003 : Word) = UInt16.ofNat 2003)]
    have hval : decChunk125[3]! = 2004 := rfl
    have hv : (2004 : Word) = UInt16.ofNat 2004 := rfl
    exact (g 2003 (by decide) (by decide)).trans ((cell2000 3 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (2004 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N3 at pc 2004. -/
theorem wn_enc_jlez_2004 {s : Machine}
    (hpc : s.pc = 2004)
    (hcode : ∀ k : Nat, 2004 ≤ k → k < 2004+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2121 := by
  have hp : s.pc = UInt16.ofNat 2004 :=
    hpc.trans (rfl : (2004 : Word) = UInt16.ofNat 2004)
  have g (k : Nat) (h1 : 2004 ≤ k) (h2 : k < 2004+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk125[4]! = 0 := rfl
    exact (g 2004 (by decide) (by decide)).trans ((cell2000 4 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2005 : Word) := by simp [hpc]
    rw [this, (rfl : (2005 : Word) = UInt16.ofNat 2005)]
    have hval : decChunk125[5]! = 18 := rfl
    exact (g 2005 (by decide) (by decide)).trans ((cell2000 5 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2121 := by
    have : s.pc + 2 = (2006 : Word) := by simp [hpc]
    rw [this, (rfl : (2006 : Word) = UInt16.ofNat 2006)]
    have hval : decChunk125[6]! = 2121 := rfl
    exact (g 2006 (by decide) (by decide)).trans ((cell2000 6 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 2007 (WRITE_NUL dispatch). -/
theorem wn_dec_T_2007 {s : Machine}
    (hpc : s.pc = 2007)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 2007 ≤ k → k < 2010 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 2010 } := by
  have hp : s.pc = UInt16.ofNat 2007 :=
    hpc.trans (rfl : (2007 : Word) = UInt16.ofNat 2007)
  have g (k : Nat) (h1 : 2007 ≤ k) (h2 : k < 2010) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk125[7]! = 3 := rfl
    exact (g 2007 (by decide) (by decide)).trans ((cell2000 7 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2008 : Word) := by simp [hpc]
    rw [this, (rfl : (2008 : Word) = UInt16.ofNat 2008)]
    have hval : decChunk125[8]! = 18 := rfl
    exact (g 2008 (by decide) (by decide)).trans ((cell2000 8 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (2009 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (2010 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (2009 : Word) = UInt16.ofNat 2009)]
    have hval : decChunk125[9]! = 2010 := rfl
    have hv : (2010 : Word) = UInt16.ofNat 2010 := rfl
    exact (g 2009 (by decide) (by decide)).trans ((cell2000 9 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (2010 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N4 at pc 2010. -/
theorem wn_enc_jlez_2010 {s : Machine}
    (hpc : s.pc = 2010)
    (hcode : ∀ k : Nat, 2010 ≤ k → k < 2010+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2136 := by
  have hp : s.pc = UInt16.ofNat 2010 :=
    hpc.trans (rfl : (2010 : Word) = UInt16.ofNat 2010)
  have g (k : Nat) (h1 : 2010 ≤ k) (h2 : k < 2010+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk125[10]! = 0 := rfl
    exact (g 2010 (by decide) (by decide)).trans ((cell2000 10 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2011 : Word) := by simp [hpc]
    rw [this, (rfl : (2011 : Word) = UInt16.ofNat 2011)]
    have hval : decChunk125[11]! = 18 := rfl
    exact (g 2011 (by decide) (by decide)).trans ((cell2000 11 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2136 := by
    have : s.pc + 2 = (2012 : Word) := by simp [hpc]
    rw [this, (rfl : (2012 : Word) = UInt16.ofNat 2012)]
    have hval : decChunk125[12]! = 2136 := rfl
    exact (g 2012 (by decide) (by decide)).trans ((cell2000 12 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 2013 (WRITE_NUL dispatch). -/
theorem wn_dec_T_2013 {s : Machine}
    (hpc : s.pc = 2013)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 2013 ≤ k → k < 2016 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 2016 } := by
  have hp : s.pc = UInt16.ofNat 2013 :=
    hpc.trans (rfl : (2013 : Word) = UInt16.ofNat 2013)
  have g (k : Nat) (h1 : 2013 ≤ k) (h2 : k < 2016) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk125[13]! = 3 := rfl
    exact (g 2013 (by decide) (by decide)).trans ((cell2000 13 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2014 : Word) := by simp [hpc]
    rw [this, (rfl : (2014 : Word) = UInt16.ofNat 2014)]
    have hval : decChunk125[14]! = 18 := rfl
    exact (g 2014 (by decide) (by decide)).trans ((cell2000 14 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (2015 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (2016 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (2015 : Word) = UInt16.ofNat 2015)]
    have hval : decChunk125[15]! = 2016 := rfl
    have hv : (2016 : Word) = UInt16.ofNat 2016 := rfl
    exact (g 2015 (by decide) (by decide)).trans ((cell2000 15 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (2016 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N5 at pc 2016. -/
theorem wn_enc_jlez_2016 {s : Machine}
    (hpc : s.pc = 2016)
    (hcode : ∀ k : Nat, 2016 ≤ k → k < 2016+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2151 := by
  have hp : s.pc = UInt16.ofNat 2016 :=
    hpc.trans (rfl : (2016 : Word) = UInt16.ofNat 2016)
  have g (k : Nat) (h1 : 2016 ≤ k) (h2 : k < 2016+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk126[0]! = 0 := rfl
    exact (g 2016 (by decide) (by decide)).trans ((cell2016 0 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2017 : Word) := by simp [hpc]
    rw [this, (rfl : (2017 : Word) = UInt16.ofNat 2017)]
    have hval : decChunk126[1]! = 18 := rfl
    exact (g 2017 (by decide) (by decide)).trans ((cell2016 1 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2151 := by
    have : s.pc + 2 = (2018 : Word) := by simp [hpc]
    rw [this, (rfl : (2018 : Word) = UInt16.ofNat 2018)]
    have hval : decChunk126[2]! = 2151 := rfl
    exact (g 2018 (by decide) (by decide)).trans ((cell2016 2 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 2019 (WRITE_NUL dispatch). -/
theorem wn_dec_T_2019 {s : Machine}
    (hpc : s.pc = 2019)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 2019 ≤ k → k < 2022 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 2022 } := by
  have hp : s.pc = UInt16.ofNat 2019 :=
    hpc.trans (rfl : (2019 : Word) = UInt16.ofNat 2019)
  have g (k : Nat) (h1 : 2019 ≤ k) (h2 : k < 2022) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk126[3]! = 3 := rfl
    exact (g 2019 (by decide) (by decide)).trans ((cell2016 3 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2020 : Word) := by simp [hpc]
    rw [this, (rfl : (2020 : Word) = UInt16.ofNat 2020)]
    have hval : decChunk126[4]! = 18 := rfl
    exact (g 2020 (by decide) (by decide)).trans ((cell2016 4 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (2021 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (2022 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (2021 : Word) = UInt16.ofNat 2021)]
    have hval : decChunk126[5]! = 2022 := rfl
    have hv : (2022 : Word) = UInt16.ofNat 2022 := rfl
    exact (g 2021 (by decide) (by decide)).trans ((cell2016 5 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (2022 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N6 at pc 2022. -/
theorem wn_enc_jlez_2022 {s : Machine}
    (hpc : s.pc = 2022)
    (hcode : ∀ k : Nat, 2022 ≤ k → k < 2022+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2166 := by
  have hp : s.pc = UInt16.ofNat 2022 :=
    hpc.trans (rfl : (2022 : Word) = UInt16.ofNat 2022)
  have g (k : Nat) (h1 : 2022 ≤ k) (h2 : k < 2022+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk126[6]! = 0 := rfl
    exact (g 2022 (by decide) (by decide)).trans ((cell2016 6 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2023 : Word) := by simp [hpc]
    rw [this, (rfl : (2023 : Word) = UInt16.ofNat 2023)]
    have hval : decChunk126[7]! = 18 := rfl
    exact (g 2023 (by decide) (by decide)).trans ((cell2016 7 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2166 := by
    have : s.pc + 2 = (2024 : Word) := by simp [hpc]
    rw [this, (rfl : (2024 : Word) = UInt16.ofNat 2024)]
    have hval : decChunk126[8]! = 2166 := rfl
    exact (g 2024 (by decide) (by decide)).trans ((cell2016 8 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 2025 (WRITE_NUL dispatch). -/
theorem wn_dec_T_2025 {s : Machine}
    (hpc : s.pc = 2025)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 2025 ≤ k → k < 2028 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 2028 } := by
  have hp : s.pc = UInt16.ofNat 2025 :=
    hpc.trans (rfl : (2025 : Word) = UInt16.ofNat 2025)
  have g (k : Nat) (h1 : 2025 ≤ k) (h2 : k < 2028) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk126[9]! = 3 := rfl
    exact (g 2025 (by decide) (by decide)).trans ((cell2016 9 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2026 : Word) := by simp [hpc]
    rw [this, (rfl : (2026 : Word) = UInt16.ofNat 2026)]
    have hval : decChunk126[10]! = 18 := rfl
    exact (g 2026 (by decide) (by decide)).trans ((cell2016 10 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (2027 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (2028 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (2027 : Word) = UInt16.ofNat 2027)]
    have hval : decChunk126[11]! = 2028 := rfl
    have hv : (2028 : Word) = UInt16.ofNat 2028 := rfl
    exact (g 2027 (by decide) (by decide)).trans ((cell2016 11 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (2028 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N7 at pc 2028. -/
theorem wn_enc_jlez_2028 {s : Machine}
    (hpc : s.pc = 2028)
    (hcode : ∀ k : Nat, 2028 ≤ k → k < 2028+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2181 := by
  have hp : s.pc = UInt16.ofNat 2028 :=
    hpc.trans (rfl : (2028 : Word) = UInt16.ofNat 2028)
  have g (k : Nat) (h1 : 2028 ≤ k) (h2 : k < 2028+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk126[12]! = 0 := rfl
    exact (g 2028 (by decide) (by decide)).trans ((cell2016 12 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2029 : Word) := by simp [hpc]
    rw [this, (rfl : (2029 : Word) = UInt16.ofNat 2029)]
    have hval : decChunk126[13]! = 18 := rfl
    exact (g 2029 (by decide) (by decide)).trans ((cell2016 13 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2181 := by
    have : s.pc + 2 = (2030 : Word) := by simp [hpc]
    rw [this, (rfl : (2030 : Word) = UInt16.ofNat 2030)]
    have hval : decChunk126[14]! = 2181 := rfl
    exact (g 2030 (by decide) (by decide)).trans ((cell2016 14 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 2031 (WRITE_NUL dispatch). -/
theorem wn_dec_T_2031 {s : Machine}
    (hpc : s.pc = 2031)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 2031 ≤ k → k < 2034 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 2034 } := by
  have hp : s.pc = UInt16.ofNat 2031 :=
    hpc.trans (rfl : (2031 : Word) = UInt16.ofNat 2031)
  have g (k : Nat) (h1 : 2031 ≤ k) (h2 : k < 2034) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk126[15]! = 3 := rfl
    exact (g 2031 (by decide) (by decide)).trans ((cell2016 15 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2032 : Word) := by simp [hpc]
    rw [this, (rfl : (2032 : Word) = UInt16.ofNat 2032)]
    have hval : decChunk127[0]! = 18 := rfl
    exact (g 2032 (by decide) (by decide)).trans ((cell2032 0 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (2033 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (2034 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (2033 : Word) = UInt16.ofNat 2033)]
    have hval : decChunk127[1]! = 2034 := rfl
    have hv : (2034 : Word) = UInt16.ofNat 2034 := rfl
    exact (g 2033 (by decide) (by decide)).trans ((cell2032 1 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (2034 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N8 at pc 2034. -/
theorem wn_enc_jlez_2034 {s : Machine}
    (hpc : s.pc = 2034)
    (hcode : ∀ k : Nat, 2034 ≤ k → k < 2034+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2196 := by
  have hp : s.pc = UInt16.ofNat 2034 :=
    hpc.trans (rfl : (2034 : Word) = UInt16.ofNat 2034)
  have g (k : Nat) (h1 : 2034 ≤ k) (h2 : k < 2034+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk127[2]! = 0 := rfl
    exact (g 2034 (by decide) (by decide)).trans ((cell2032 2 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2035 : Word) := by simp [hpc]
    rw [this, (rfl : (2035 : Word) = UInt16.ofNat 2035)]
    have hval : decChunk127[3]! = 18 := rfl
    exact (g 2035 (by decide) (by decide)).trans ((cell2032 3 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2196 := by
    have : s.pc + 2 = (2036 : Word) := by simp [hpc]
    rw [this, (rfl : (2036 : Word) = UInt16.ofNat 2036)]
    have hval : decChunk127[4]! = 2196 := rfl
    exact (g 2036 (by decide) (by decide)).trans ((cell2032 4 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 2037 (WRITE_NUL dispatch). -/
theorem wn_dec_T_2037 {s : Machine}
    (hpc : s.pc = 2037)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 2037 ≤ k → k < 2040 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 2040 } := by
  have hp : s.pc = UInt16.ofNat 2037 :=
    hpc.trans (rfl : (2037 : Word) = UInt16.ofNat 2037)
  have g (k : Nat) (h1 : 2037 ≤ k) (h2 : k < 2040) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk127[5]! = 3 := rfl
    exact (g 2037 (by decide) (by decide)).trans ((cell2032 5 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2038 : Word) := by simp [hpc]
    rw [this, (rfl : (2038 : Word) = UInt16.ofNat 2038)]
    have hval : decChunk127[6]! = 18 := rfl
    exact (g 2038 (by decide) (by decide)).trans ((cell2032 6 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (2039 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (2040 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (2039 : Word) = UInt16.ofNat 2039)]
    have hval : decChunk127[7]! = 2040 := rfl
    have hv : (2040 : Word) = UInt16.ofNat 2040 := rfl
    exact (g 2039 (by decide) (by decide)).trans ((cell2032 7 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (2040 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N9 at pc 2040. -/
theorem wn_enc_jlez_2040 {s : Machine}
    (hpc : s.pc = 2040)
    (hcode : ∀ k : Nat, 2040 ≤ k → k < 2040+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2211 := by
  have hp : s.pc = UInt16.ofNat 2040 :=
    hpc.trans (rfl : (2040 : Word) = UInt16.ofNat 2040)
  have g (k : Nat) (h1 : 2040 ≤ k) (h2 : k < 2040+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk127[8]! = 0 := rfl
    exact (g 2040 (by decide) (by decide)).trans ((cell2032 8 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2041 : Word) := by simp [hpc]
    rw [this, (rfl : (2041 : Word) = UInt16.ofNat 2041)]
    have hval : decChunk127[9]! = 18 := rfl
    exact (g 2041 (by decide) (by decide)).trans ((cell2032 9 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2211 := by
    have : s.pc + 2 = (2042 : Word) := by simp [hpc]
    rw [this, (rfl : (2042 : Word) = UInt16.ofNat 2042)]
    have hval : decChunk127[10]! = 2211 := rfl
    exact (g 2042 (by decide) (by decide)).trans ((cell2032 10 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 2043 (WRITE_NUL dispatch). -/
theorem wn_dec_T_2043 {s : Machine}
    (hpc : s.pc = 2043)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 2043 ≤ k → k < 2046 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 2046 } := by
  have hp : s.pc = UInt16.ofNat 2043 :=
    hpc.trans (rfl : (2043 : Word) = UInt16.ofNat 2043)
  have g (k : Nat) (h1 : 2043 ≤ k) (h2 : k < 2046) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk127[11]! = 3 := rfl
    exact (g 2043 (by decide) (by decide)).trans ((cell2032 11 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2044 : Word) := by simp [hpc]
    rw [this, (rfl : (2044 : Word) = UInt16.ofNat 2044)]
    have hval : decChunk127[12]! = 18 := rfl
    exact (g 2044 (by decide) (by decide)).trans ((cell2032 12 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (2045 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (2046 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (2045 : Word) = UInt16.ofNat 2045)]
    have hval : decChunk127[13]! = 2046 := rfl
    have hv : (2046 : Word) = UInt16.ofNat 2046 := rfl
    exact (g 2045 (by decide) (by decide)).trans ((cell2032 13 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (2046 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N10 at pc 2046. -/
theorem wn_enc_jlez_2046 {s : Machine}
    (hpc : s.pc = 2046)
    (hcode : ∀ k : Nat, 2046 ≤ k → k < 2046+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2226 := by
  have hp : s.pc = UInt16.ofNat 2046 :=
    hpc.trans (rfl : (2046 : Word) = UInt16.ofNat 2046)
  have g (k : Nat) (h1 : 2046 ≤ k) (h2 : k < 2046+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk127[14]! = 0 := rfl
    exact (g 2046 (by decide) (by decide)).trans ((cell2032 14 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2047 : Word) := by simp [hpc]
    rw [this, (rfl : (2047 : Word) = UInt16.ofNat 2047)]
    have hval : decChunk127[15]! = 18 := rfl
    exact (g 2047 (by decide) (by decide)).trans ((cell2032 15 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2226 := by
    have : s.pc + 2 = (2048 : Word) := by simp [hpc]
    rw [this, (rfl : (2048 : Word) = UInt16.ofNat 2048)]
    have hval : decChunk128[0]! = 2226 := rfl
    exact (g 2048 (by decide) (by decide)).trans ((cell2048 0 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 2049 (WRITE_NUL dispatch). -/
theorem wn_dec_T_2049 {s : Machine}
    (hpc : s.pc = 2049)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 2049 ≤ k → k < 2052 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 2052 } := by
  have hp : s.pc = UInt16.ofNat 2049 :=
    hpc.trans (rfl : (2049 : Word) = UInt16.ofNat 2049)
  have g (k : Nat) (h1 : 2049 ≤ k) (h2 : k < 2052) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk128[1]! = 3 := rfl
    exact (g 2049 (by decide) (by decide)).trans ((cell2048 1 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2050 : Word) := by simp [hpc]
    rw [this, (rfl : (2050 : Word) = UInt16.ofNat 2050)]
    have hval : decChunk128[2]! = 18 := rfl
    exact (g 2050 (by decide) (by decide)).trans ((cell2048 2 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (2051 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (2052 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (2051 : Word) = UInt16.ofNat 2051)]
    have hval : decChunk128[3]! = 2052 := rfl
    have hv : (2052 : Word) = UInt16.ofNat 2052 := rfl
    exact (g 2051 (by decide) (by decide)).trans ((cell2048 3 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (2052 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N11 at pc 2052. -/
theorem wn_enc_jlez_2052 {s : Machine}
    (hpc : s.pc = 2052)
    (hcode : ∀ k : Nat, 2052 ≤ k → k < 2052+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2241 := by
  have hp : s.pc = UInt16.ofNat 2052 :=
    hpc.trans (rfl : (2052 : Word) = UInt16.ofNat 2052)
  have g (k : Nat) (h1 : 2052 ≤ k) (h2 : k < 2052+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk128[4]! = 0 := rfl
    exact (g 2052 (by decide) (by decide)).trans ((cell2048 4 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2053 : Word) := by simp [hpc]
    rw [this, (rfl : (2053 : Word) = UInt16.ofNat 2053)]
    have hval : decChunk128[5]! = 18 := rfl
    exact (g 2053 (by decide) (by decide)).trans ((cell2048 5 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2241 := by
    have : s.pc + 2 = (2054 : Word) := by simp [hpc]
    rw [this, (rfl : (2054 : Word) = UInt16.ofNat 2054)]
    have hval : decChunk128[6]! = 2241 := rfl
    exact (g 2054 (by decide) (by decide)).trans ((cell2048 6 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 2055 (WRITE_NUL dispatch). -/
theorem wn_dec_T_2055 {s : Machine}
    (hpc : s.pc = 2055)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 2055 ≤ k → k < 2058 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 2058 } := by
  have hp : s.pc = UInt16.ofNat 2055 :=
    hpc.trans (rfl : (2055 : Word) = UInt16.ofNat 2055)
  have g (k : Nat) (h1 : 2055 ≤ k) (h2 : k < 2058) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk128[7]! = 3 := rfl
    exact (g 2055 (by decide) (by decide)).trans ((cell2048 7 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2056 : Word) := by simp [hpc]
    rw [this, (rfl : (2056 : Word) = UInt16.ofNat 2056)]
    have hval : decChunk128[8]! = 18 := rfl
    exact (g 2056 (by decide) (by decide)).trans ((cell2048 8 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (2057 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (2058 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (2057 : Word) = UInt16.ofNat 2057)]
    have hval : decChunk128[9]! = 2058 := rfl
    have hv : (2058 : Word) = UInt16.ofNat 2058 := rfl
    exact (g 2057 (by decide) (by decide)).trans ((cell2048 9 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (2058 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N12 at pc 2058. -/
theorem wn_enc_jlez_2058 {s : Machine}
    (hpc : s.pc = 2058)
    (hcode : ∀ k : Nat, 2058 ≤ k → k < 2058+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2256 := by
  have hp : s.pc = UInt16.ofNat 2058 :=
    hpc.trans (rfl : (2058 : Word) = UInt16.ofNat 2058)
  have g (k : Nat) (h1 : 2058 ≤ k) (h2 : k < 2058+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk128[10]! = 0 := rfl
    exact (g 2058 (by decide) (by decide)).trans ((cell2048 10 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2059 : Word) := by simp [hpc]
    rw [this, (rfl : (2059 : Word) = UInt16.ofNat 2059)]
    have hval : decChunk128[11]! = 18 := rfl
    exact (g 2059 (by decide) (by decide)).trans ((cell2048 11 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2256 := by
    have : s.pc + 2 = (2060 : Word) := by simp [hpc]
    rw [this, (rfl : (2060 : Word) = UInt16.ofNat 2060)]
    have hval : decChunk128[12]! = 2256 := rfl
    exact (g 2060 (by decide) (by decide)).trans ((cell2048 12 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 2061 (WRITE_NUL dispatch). -/
theorem wn_dec_T_2061 {s : Machine}
    (hpc : s.pc = 2061)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 2061 ≤ k → k < 2064 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 2064 } := by
  have hp : s.pc = UInt16.ofNat 2061 :=
    hpc.trans (rfl : (2061 : Word) = UInt16.ofNat 2061)
  have g (k : Nat) (h1 : 2061 ≤ k) (h2 : k < 2064) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk128[13]! = 3 := rfl
    exact (g 2061 (by decide) (by decide)).trans ((cell2048 13 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2062 : Word) := by simp [hpc]
    rw [this, (rfl : (2062 : Word) = UInt16.ofNat 2062)]
    have hval : decChunk128[14]! = 18 := rfl
    exact (g 2062 (by decide) (by decide)).trans ((cell2048 14 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (2063 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (2064 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (2063 : Word) = UInt16.ofNat 2063)]
    have hval : decChunk128[15]! = 2064 := rfl
    have hv : (2064 : Word) = UInt16.ofNat 2064 := rfl
    exact (g 2063 (by decide) (by decide)).trans ((cell2048 15 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (2064 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N13 at pc 2064. -/
theorem wn_enc_jlez_2064 {s : Machine}
    (hpc : s.pc = 2064)
    (hcode : ∀ k : Nat, 2064 ≤ k → k < 2064+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2271 := by
  have hp : s.pc = UInt16.ofNat 2064 :=
    hpc.trans (rfl : (2064 : Word) = UInt16.ofNat 2064)
  have g (k : Nat) (h1 : 2064 ≤ k) (h2 : k < 2064+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk129[0]! = 0 := rfl
    exact (g 2064 (by decide) (by decide)).trans ((cell2064 0 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2065 : Word) := by simp [hpc]
    rw [this, (rfl : (2065 : Word) = UInt16.ofNat 2065)]
    have hval : decChunk129[1]! = 18 := rfl
    exact (g 2065 (by decide) (by decide)).trans ((cell2064 1 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2271 := by
    have : s.pc + 2 = (2066 : Word) := by simp [hpc]
    rw [this, (rfl : (2066 : Word) = UInt16.ofNat 2066)]
    have hval : decChunk129[2]! = 2271 := rfl
    exact (g 2066 (by decide) (by decide)).trans ((cell2064 2 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 2067 (WRITE_NUL dispatch). -/
theorem wn_dec_T_2067 {s : Machine}
    (hpc : s.pc = 2067)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 2067 ≤ k → k < 2070 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 2070 } := by
  have hp : s.pc = UInt16.ofNat 2067 :=
    hpc.trans (rfl : (2067 : Word) = UInt16.ofNat 2067)
  have g (k : Nat) (h1 : 2067 ≤ k) (h2 : k < 2070) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk129[3]! = 3 := rfl
    exact (g 2067 (by decide) (by decide)).trans ((cell2064 3 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2068 : Word) := by simp [hpc]
    rw [this, (rfl : (2068 : Word) = UInt16.ofNat 2068)]
    have hval : decChunk129[4]! = 18 := rfl
    exact (g 2068 (by decide) (by decide)).trans ((cell2064 4 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (2069 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (2070 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (2069 : Word) = UInt16.ofNat 2069)]
    have hval : decChunk129[5]! = 2070 := rfl
    have hv : (2070 : Word) = UInt16.ofNat 2070 := rfl
    exact (g 2069 (by decide) (by decide)).trans ((cell2064 5 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (2070 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T N14 at pc 2070. -/
theorem wn_enc_jlez_2070 {s : Machine}
    (hpc : s.pc = 2070)
    (hcode : ∀ k : Nat, 2070 ≤ k → k < 2070+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2286 := by
  have hp : s.pc = UInt16.ofNat 2070 :=
    hpc.trans (rfl : (2070 : Word) = UInt16.ofNat 2070)
  have g (k : Nat) (h1 : 2070 ≤ k) (h2 : k < 2070+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk129[6]! = 0 := rfl
    exact (g 2070 (by decide) (by decide)).trans ((cell2064 6 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (2071 : Word) := by simp [hpc]
    rw [this, (rfl : (2071 : Word) = UInt16.ofNat 2071)]
    have hval : decChunk129[7]! = 18 := rfl
    exact (g 2071 (by decide) (by decide)).trans ((cell2064 7 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2286 := by
    have : s.pc + 2 = (2072 : Word) := by simp [hpc]
    rw [this, (rfl : (2072 : Word) = UInt16.ofNat 2072)]
    have hval : decChunk129[8]! = 2286 := rfl
    exact (g 2072 (by decide) (by decide)).trans ((cell2064 8 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP N15 at pc 2073. -/
theorem wn_enc_jmp_2073 {s : Machine}
    (hpc : s.pc = 2073)
    (hcode : ∀ k : Nat, 2073 ≤ k → k < 2073+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2301 := by
  have hp : s.pc = UInt16.ofNat 2073 :=
    hpc.trans (rfl : (2073 : Word) = UInt16.ofNat 2073)
  have g (k : Nat) (h1 : 2073 ≤ k) (h2 : k < 2073+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk129[9]! = 0 := rfl
    exact (g 2073 (by decide) (by decide)).trans ((cell2064 9 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2074 : Word) := by simp [hpc]
    rw [this, (rfl : (2074 : Word) = UInt16.ofNat 2074)]
    have hval : decChunk129[10]! = 0 := rfl
    exact (g 2074 (by decide) (by decide)).trans ((cell2064 10 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2301 := by
    have : s.pc + 2 = (2075 : Word) := by simp [hpc]
    rw [this, (rfl : (2075 : Word) = UInt16.ofNat 2075)]
    have hval : decChunk129[11]! = 2301 := rfl
    exact (g 2075 (by decide) (by decide)).trans ((cell2064 11 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+0 at N0 (pc 2076). -/
theorem wn_mov_CH_BUF0_2076 {s : Machine}
    (hpc : s.pc = 2076)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2076 ≤ k → k < 2088 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2088 ∧
    s4.halted = false ∧
    s4.mem.get 32 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 32 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2076 :=
    hpc.trans (rfl : (2076 : Word) = UInt16.ofNat 2076)
  have g (k : Nat) (h1 : 2076 ≤ k) (h2 : k < 2088) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2076 + off) :=
    word_pc_off 2076 off hp (by omega)
  have m0 : s.mem.get s.pc = 32 := by
    rw [hp]
    have hval : decChunk129[12]! = 32 := rfl
    exact (g 2076 (by decide) (by decide)).trans ((cell2064 12 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 32 := by
    rw [poff 1 (by decide)]
    have hval : decChunk129[13]! = 32 := rfl
    exact (g 2077 (by decide) (by decide)).trans ((cell2064 13 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk129[14]! = 2079 := rfl
    have hv : (2079 : Word) = UInt16.ofNat 2079 := rfl
    exact (g 2078 (by decide) (by decide)).trans ((cell2064 14 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk129[15]! = 30 := rfl
    exact (g 2079 (by decide) (by decide)).trans ((cell2064 15 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk130[0]! = 0 := rfl
    exact (g 2080 (by decide) (by decide)).trans ((cell2080 0 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk130[1]! = 2082 := rfl
    have hv : (2082 : Word) = UInt16.ofNat 2082 := rfl
    exact (g 2081 (by decide) (by decide)).trans ((cell2080 1 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk130[2]! = 0 := rfl
    exact (g 2082 (by decide) (by decide)).trans ((cell2080 2 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 32 := by
    rw [poff 7 (by decide)]
    have hval : decChunk130[3]! = 32 := rfl
    exact (g 2083 (by decide) (by decide)).trans ((cell2080 3 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk130[4]! = 2085 := rfl
    have hv : (2085 : Word) = UInt16.ofNat 2085 := rfl
    exact (g 2084 (by decide) (by decide)).trans ((cell2080 4 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk130[5]! = 0 := rfl
    exact (g 2085 (by decide) (by decide)).trans ((cell2080 5 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk130[6]! = 0 := rfl
    exact (g 2086 (by decide) (by decide)).trans ((cell2080 6 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk130[7]! = 2088 := rfl
    have hv : (2088 : Word) = UInt16.ofNat 2088 := rfl
    exact (g 2087 (by decide) (by decide)).trans ((cell2080 7 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (32 : Word) := by
    intro i hi
    have : (32 : Word) = UInt16.ofNat 32 := rfl
    rw [this]
    exact pc_off_ne 2076 i 32 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2076 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 32)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2088 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2088 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2088 = (2088 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2088. -/
theorem wn_enc_jmp_2088 {s : Machine}
    (hpc : s.pc = 2088)
    (hcode : ∀ k : Nat, 2088 ≤ k → k < 2088+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2088 :=
    hpc.trans (rfl : (2088 : Word) = UInt16.ofNat 2088)
  have g (k : Nat) (h1 : 2088 ≤ k) (h2 : k < 2088+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk130[8]! = 0 := rfl
    exact (g 2088 (by decide) (by decide)).trans ((cell2080 8 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2089 : Word) := by simp [hpc]
    rw [this, (rfl : (2089 : Word) = UInt16.ofNat 2089)]
    have hval : decChunk130[9]! = 0 := rfl
    exact (g 2089 (by decide) (by decide)).trans ((cell2080 9 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2090 : Word) := by simp [hpc]
    rw [this, (rfl : (2090 : Word) = UInt16.ofNat 2090)]
    have hval : decChunk130[10]! = 2316 := rfl
    exact (g 2090 (by decide) (by decide)).trans ((cell2080 10 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+1 at N1 (pc 2091). -/
theorem wn_mov_CH_BUF1_2091 {s : Machine}
    (hpc : s.pc = 2091)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2091 ≤ k → k < 2103 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2103 ∧
    s4.halted = false ∧
    s4.mem.get 33 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 33 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2091 :=
    hpc.trans (rfl : (2091 : Word) = UInt16.ofNat 2091)
  have g (k : Nat) (h1 : 2091 ≤ k) (h2 : k < 2103) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2091 + off) :=
    word_pc_off 2091 off hp (by omega)
  have m0 : s.mem.get s.pc = 33 := by
    rw [hp]
    have hval : decChunk130[11]! = 33 := rfl
    exact (g 2091 (by decide) (by decide)).trans ((cell2080 11 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 33 := by
    rw [poff 1 (by decide)]
    have hval : decChunk130[12]! = 33 := rfl
    exact (g 2092 (by decide) (by decide)).trans ((cell2080 12 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk130[13]! = 2094 := rfl
    have hv : (2094 : Word) = UInt16.ofNat 2094 := rfl
    exact (g 2093 (by decide) (by decide)).trans ((cell2080 13 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk130[14]! = 30 := rfl
    exact (g 2094 (by decide) (by decide)).trans ((cell2080 14 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk130[15]! = 0 := rfl
    exact (g 2095 (by decide) (by decide)).trans ((cell2080 15 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk131[0]! = 2097 := rfl
    have hv : (2097 : Word) = UInt16.ofNat 2097 := rfl
    exact (g 2096 (by decide) (by decide)).trans ((cell2096 0 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk131[1]! = 0 := rfl
    exact (g 2097 (by decide) (by decide)).trans ((cell2096 1 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 33 := by
    rw [poff 7 (by decide)]
    have hval : decChunk131[2]! = 33 := rfl
    exact (g 2098 (by decide) (by decide)).trans ((cell2096 2 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk131[3]! = 2100 := rfl
    have hv : (2100 : Word) = UInt16.ofNat 2100 := rfl
    exact (g 2099 (by decide) (by decide)).trans ((cell2096 3 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk131[4]! = 0 := rfl
    exact (g 2100 (by decide) (by decide)).trans ((cell2096 4 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk131[5]! = 0 := rfl
    exact (g 2101 (by decide) (by decide)).trans ((cell2096 5 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk131[6]! = 2103 := rfl
    have hv : (2103 : Word) = UInt16.ofNat 2103 := rfl
    exact (g 2102 (by decide) (by decide)).trans ((cell2096 6 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (33 : Word) := by
    intro i hi
    have : (33 : Word) = UInt16.ofNat 33 := rfl
    rw [this]
    exact pc_off_ne 2091 i 33 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2091 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 33)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2103 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2103 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2103 = (2103 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2103. -/
theorem wn_enc_jmp_2103 {s : Machine}
    (hpc : s.pc = 2103)
    (hcode : ∀ k : Nat, 2103 ≤ k → k < 2103+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2103 :=
    hpc.trans (rfl : (2103 : Word) = UInt16.ofNat 2103)
  have g (k : Nat) (h1 : 2103 ≤ k) (h2 : k < 2103+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk131[7]! = 0 := rfl
    exact (g 2103 (by decide) (by decide)).trans ((cell2096 7 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2104 : Word) := by simp [hpc]
    rw [this, (rfl : (2104 : Word) = UInt16.ofNat 2104)]
    have hval : decChunk131[8]! = 0 := rfl
    exact (g 2104 (by decide) (by decide)).trans ((cell2096 8 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2105 : Word) := by simp [hpc]
    rw [this, (rfl : (2105 : Word) = UInt16.ofNat 2105)]
    have hval : decChunk131[9]! = 2316 := rfl
    exact (g 2105 (by decide) (by decide)).trans ((cell2096 9 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+2 at N2 (pc 2106). -/
theorem wn_mov_CH_BUF2_2106 {s : Machine}
    (hpc : s.pc = 2106)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2106 ≤ k → k < 2118 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2118 ∧
    s4.halted = false ∧
    s4.mem.get 34 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 34 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2106 :=
    hpc.trans (rfl : (2106 : Word) = UInt16.ofNat 2106)
  have g (k : Nat) (h1 : 2106 ≤ k) (h2 : k < 2118) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2106 + off) :=
    word_pc_off 2106 off hp (by omega)
  have m0 : s.mem.get s.pc = 34 := by
    rw [hp]
    have hval : decChunk131[10]! = 34 := rfl
    exact (g 2106 (by decide) (by decide)).trans ((cell2096 10 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 34 := by
    rw [poff 1 (by decide)]
    have hval : decChunk131[11]! = 34 := rfl
    exact (g 2107 (by decide) (by decide)).trans ((cell2096 11 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk131[12]! = 2109 := rfl
    have hv : (2109 : Word) = UInt16.ofNat 2109 := rfl
    exact (g 2108 (by decide) (by decide)).trans ((cell2096 12 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk131[13]! = 30 := rfl
    exact (g 2109 (by decide) (by decide)).trans ((cell2096 13 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk131[14]! = 0 := rfl
    exact (g 2110 (by decide) (by decide)).trans ((cell2096 14 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk131[15]! = 2112 := rfl
    have hv : (2112 : Word) = UInt16.ofNat 2112 := rfl
    exact (g 2111 (by decide) (by decide)).trans ((cell2096 15 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk132[0]! = 0 := rfl
    exact (g 2112 (by decide) (by decide)).trans ((cell2112 0 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 34 := by
    rw [poff 7 (by decide)]
    have hval : decChunk132[1]! = 34 := rfl
    exact (g 2113 (by decide) (by decide)).trans ((cell2112 1 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk132[2]! = 2115 := rfl
    have hv : (2115 : Word) = UInt16.ofNat 2115 := rfl
    exact (g 2114 (by decide) (by decide)).trans ((cell2112 2 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk132[3]! = 0 := rfl
    exact (g 2115 (by decide) (by decide)).trans ((cell2112 3 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk132[4]! = 0 := rfl
    exact (g 2116 (by decide) (by decide)).trans ((cell2112 4 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk132[5]! = 2118 := rfl
    have hv : (2118 : Word) = UInt16.ofNat 2118 := rfl
    exact (g 2117 (by decide) (by decide)).trans ((cell2112 5 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (34 : Word) := by
    intro i hi
    have : (34 : Word) = UInt16.ofNat 34 := rfl
    rw [this]
    exact pc_off_ne 2106 i 34 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2106 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 34)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2118 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2118 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2118 = (2118 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2118. -/
theorem wn_enc_jmp_2118 {s : Machine}
    (hpc : s.pc = 2118)
    (hcode : ∀ k : Nat, 2118 ≤ k → k < 2118+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2118 :=
    hpc.trans (rfl : (2118 : Word) = UInt16.ofNat 2118)
  have g (k : Nat) (h1 : 2118 ≤ k) (h2 : k < 2118+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk132[6]! = 0 := rfl
    exact (g 2118 (by decide) (by decide)).trans ((cell2112 6 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2119 : Word) := by simp [hpc]
    rw [this, (rfl : (2119 : Word) = UInt16.ofNat 2119)]
    have hval : decChunk132[7]! = 0 := rfl
    exact (g 2119 (by decide) (by decide)).trans ((cell2112 7 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2120 : Word) := by simp [hpc]
    rw [this, (rfl : (2120 : Word) = UInt16.ofNat 2120)]
    have hval : decChunk132[8]! = 2316 := rfl
    exact (g 2120 (by decide) (by decide)).trans ((cell2112 8 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+3 at N3 (pc 2121). -/
theorem wn_mov_CH_BUF3_2121 {s : Machine}
    (hpc : s.pc = 2121)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2121 ≤ k → k < 2133 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2133 ∧
    s4.halted = false ∧
    s4.mem.get 35 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 35 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2121 :=
    hpc.trans (rfl : (2121 : Word) = UInt16.ofNat 2121)
  have g (k : Nat) (h1 : 2121 ≤ k) (h2 : k < 2133) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2121 + off) :=
    word_pc_off 2121 off hp (by omega)
  have m0 : s.mem.get s.pc = 35 := by
    rw [hp]
    have hval : decChunk132[9]! = 35 := rfl
    exact (g 2121 (by decide) (by decide)).trans ((cell2112 9 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 35 := by
    rw [poff 1 (by decide)]
    have hval : decChunk132[10]! = 35 := rfl
    exact (g 2122 (by decide) (by decide)).trans ((cell2112 10 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk132[11]! = 2124 := rfl
    have hv : (2124 : Word) = UInt16.ofNat 2124 := rfl
    exact (g 2123 (by decide) (by decide)).trans ((cell2112 11 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk132[12]! = 30 := rfl
    exact (g 2124 (by decide) (by decide)).trans ((cell2112 12 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk132[13]! = 0 := rfl
    exact (g 2125 (by decide) (by decide)).trans ((cell2112 13 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk132[14]! = 2127 := rfl
    have hv : (2127 : Word) = UInt16.ofNat 2127 := rfl
    exact (g 2126 (by decide) (by decide)).trans ((cell2112 14 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk132[15]! = 0 := rfl
    exact (g 2127 (by decide) (by decide)).trans ((cell2112 15 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 35 := by
    rw [poff 7 (by decide)]
    have hval : decChunk133[0]! = 35 := rfl
    exact (g 2128 (by decide) (by decide)).trans ((cell2128 0 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk133[1]! = 2130 := rfl
    have hv : (2130 : Word) = UInt16.ofNat 2130 := rfl
    exact (g 2129 (by decide) (by decide)).trans ((cell2128 1 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk133[2]! = 0 := rfl
    exact (g 2130 (by decide) (by decide)).trans ((cell2128 2 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk133[3]! = 0 := rfl
    exact (g 2131 (by decide) (by decide)).trans ((cell2128 3 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk133[4]! = 2133 := rfl
    have hv : (2133 : Word) = UInt16.ofNat 2133 := rfl
    exact (g 2132 (by decide) (by decide)).trans ((cell2128 4 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (35 : Word) := by
    intro i hi
    have : (35 : Word) = UInt16.ofNat 35 := rfl
    rw [this]
    exact pc_off_ne 2121 i 35 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2121 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 35)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2133 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2133 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2133 = (2133 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2133. -/
theorem wn_enc_jmp_2133 {s : Machine}
    (hpc : s.pc = 2133)
    (hcode : ∀ k : Nat, 2133 ≤ k → k < 2133+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2133 :=
    hpc.trans (rfl : (2133 : Word) = UInt16.ofNat 2133)
  have g (k : Nat) (h1 : 2133 ≤ k) (h2 : k < 2133+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk133[5]! = 0 := rfl
    exact (g 2133 (by decide) (by decide)).trans ((cell2128 5 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2134 : Word) := by simp [hpc]
    rw [this, (rfl : (2134 : Word) = UInt16.ofNat 2134)]
    have hval : decChunk133[6]! = 0 := rfl
    exact (g 2134 (by decide) (by decide)).trans ((cell2128 6 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2135 : Word) := by simp [hpc]
    rw [this, (rfl : (2135 : Word) = UInt16.ofNat 2135)]
    have hval : decChunk133[7]! = 2316 := rfl
    exact (g 2135 (by decide) (by decide)).trans ((cell2128 7 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+4 at N4 (pc 2136). -/
theorem wn_mov_CH_BUF4_2136 {s : Machine}
    (hpc : s.pc = 2136)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2136 ≤ k → k < 2148 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2148 ∧
    s4.halted = false ∧
    s4.mem.get 36 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 36 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2136 :=
    hpc.trans (rfl : (2136 : Word) = UInt16.ofNat 2136)
  have g (k : Nat) (h1 : 2136 ≤ k) (h2 : k < 2148) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2136 + off) :=
    word_pc_off 2136 off hp (by omega)
  have m0 : s.mem.get s.pc = 36 := by
    rw [hp]
    have hval : decChunk133[8]! = 36 := rfl
    exact (g 2136 (by decide) (by decide)).trans ((cell2128 8 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 36 := by
    rw [poff 1 (by decide)]
    have hval : decChunk133[9]! = 36 := rfl
    exact (g 2137 (by decide) (by decide)).trans ((cell2128 9 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk133[10]! = 2139 := rfl
    have hv : (2139 : Word) = UInt16.ofNat 2139 := rfl
    exact (g 2138 (by decide) (by decide)).trans ((cell2128 10 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk133[11]! = 30 := rfl
    exact (g 2139 (by decide) (by decide)).trans ((cell2128 11 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk133[12]! = 0 := rfl
    exact (g 2140 (by decide) (by decide)).trans ((cell2128 12 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk133[13]! = 2142 := rfl
    have hv : (2142 : Word) = UInt16.ofNat 2142 := rfl
    exact (g 2141 (by decide) (by decide)).trans ((cell2128 13 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk133[14]! = 0 := rfl
    exact (g 2142 (by decide) (by decide)).trans ((cell2128 14 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 36 := by
    rw [poff 7 (by decide)]
    have hval : decChunk133[15]! = 36 := rfl
    exact (g 2143 (by decide) (by decide)).trans ((cell2128 15 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk134[0]! = 2145 := rfl
    have hv : (2145 : Word) = UInt16.ofNat 2145 := rfl
    exact (g 2144 (by decide) (by decide)).trans ((cell2144 0 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk134[1]! = 0 := rfl
    exact (g 2145 (by decide) (by decide)).trans ((cell2144 1 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk134[2]! = 0 := rfl
    exact (g 2146 (by decide) (by decide)).trans ((cell2144 2 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk134[3]! = 2148 := rfl
    have hv : (2148 : Word) = UInt16.ofNat 2148 := rfl
    exact (g 2147 (by decide) (by decide)).trans ((cell2144 3 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (36 : Word) := by
    intro i hi
    have : (36 : Word) = UInt16.ofNat 36 := rfl
    rw [this]
    exact pc_off_ne 2136 i 36 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2136 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 36)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2148 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2148 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2148 = (2148 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2148. -/
theorem wn_enc_jmp_2148 {s : Machine}
    (hpc : s.pc = 2148)
    (hcode : ∀ k : Nat, 2148 ≤ k → k < 2148+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2148 :=
    hpc.trans (rfl : (2148 : Word) = UInt16.ofNat 2148)
  have g (k : Nat) (h1 : 2148 ≤ k) (h2 : k < 2148+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk134[4]! = 0 := rfl
    exact (g 2148 (by decide) (by decide)).trans ((cell2144 4 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2149 : Word) := by simp [hpc]
    rw [this, (rfl : (2149 : Word) = UInt16.ofNat 2149)]
    have hval : decChunk134[5]! = 0 := rfl
    exact (g 2149 (by decide) (by decide)).trans ((cell2144 5 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2150 : Word) := by simp [hpc]
    rw [this, (rfl : (2150 : Word) = UInt16.ofNat 2150)]
    have hval : decChunk134[6]! = 2316 := rfl
    exact (g 2150 (by decide) (by decide)).trans ((cell2144 6 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+5 at N5 (pc 2151). -/
theorem wn_mov_CH_BUF5_2151 {s : Machine}
    (hpc : s.pc = 2151)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2151 ≤ k → k < 2163 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2163 ∧
    s4.halted = false ∧
    s4.mem.get 37 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 37 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2151 :=
    hpc.trans (rfl : (2151 : Word) = UInt16.ofNat 2151)
  have g (k : Nat) (h1 : 2151 ≤ k) (h2 : k < 2163) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2151 + off) :=
    word_pc_off 2151 off hp (by omega)
  have m0 : s.mem.get s.pc = 37 := by
    rw [hp]
    have hval : decChunk134[7]! = 37 := rfl
    exact (g 2151 (by decide) (by decide)).trans ((cell2144 7 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 37 := by
    rw [poff 1 (by decide)]
    have hval : decChunk134[8]! = 37 := rfl
    exact (g 2152 (by decide) (by decide)).trans ((cell2144 8 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk134[9]! = 2154 := rfl
    have hv : (2154 : Word) = UInt16.ofNat 2154 := rfl
    exact (g 2153 (by decide) (by decide)).trans ((cell2144 9 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk134[10]! = 30 := rfl
    exact (g 2154 (by decide) (by decide)).trans ((cell2144 10 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk134[11]! = 0 := rfl
    exact (g 2155 (by decide) (by decide)).trans ((cell2144 11 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk134[12]! = 2157 := rfl
    have hv : (2157 : Word) = UInt16.ofNat 2157 := rfl
    exact (g 2156 (by decide) (by decide)).trans ((cell2144 12 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk134[13]! = 0 := rfl
    exact (g 2157 (by decide) (by decide)).trans ((cell2144 13 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 37 := by
    rw [poff 7 (by decide)]
    have hval : decChunk134[14]! = 37 := rfl
    exact (g 2158 (by decide) (by decide)).trans ((cell2144 14 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk134[15]! = 2160 := rfl
    have hv : (2160 : Word) = UInt16.ofNat 2160 := rfl
    exact (g 2159 (by decide) (by decide)).trans ((cell2144 15 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk135[0]! = 0 := rfl
    exact (g 2160 (by decide) (by decide)).trans ((cell2160 0 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk135[1]! = 0 := rfl
    exact (g 2161 (by decide) (by decide)).trans ((cell2160 1 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk135[2]! = 2163 := rfl
    have hv : (2163 : Word) = UInt16.ofNat 2163 := rfl
    exact (g 2162 (by decide) (by decide)).trans ((cell2160 2 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (37 : Word) := by
    intro i hi
    have : (37 : Word) = UInt16.ofNat 37 := rfl
    rw [this]
    exact pc_off_ne 2151 i 37 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2151 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 37)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2163 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2163 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2163 = (2163 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2163. -/
theorem wn_enc_jmp_2163 {s : Machine}
    (hpc : s.pc = 2163)
    (hcode : ∀ k : Nat, 2163 ≤ k → k < 2163+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2163 :=
    hpc.trans (rfl : (2163 : Word) = UInt16.ofNat 2163)
  have g (k : Nat) (h1 : 2163 ≤ k) (h2 : k < 2163+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk135[3]! = 0 := rfl
    exact (g 2163 (by decide) (by decide)).trans ((cell2160 3 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2164 : Word) := by simp [hpc]
    rw [this, (rfl : (2164 : Word) = UInt16.ofNat 2164)]
    have hval : decChunk135[4]! = 0 := rfl
    exact (g 2164 (by decide) (by decide)).trans ((cell2160 4 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2165 : Word) := by simp [hpc]
    rw [this, (rfl : (2165 : Word) = UInt16.ofNat 2165)]
    have hval : decChunk135[5]! = 2316 := rfl
    exact (g 2165 (by decide) (by decide)).trans ((cell2160 5 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+6 at N6 (pc 2166). -/
theorem wn_mov_CH_BUF6_2166 {s : Machine}
    (hpc : s.pc = 2166)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2166 ≤ k → k < 2178 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2178 ∧
    s4.halted = false ∧
    s4.mem.get 38 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 38 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2166 :=
    hpc.trans (rfl : (2166 : Word) = UInt16.ofNat 2166)
  have g (k : Nat) (h1 : 2166 ≤ k) (h2 : k < 2178) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2166 + off) :=
    word_pc_off 2166 off hp (by omega)
  have m0 : s.mem.get s.pc = 38 := by
    rw [hp]
    have hval : decChunk135[6]! = 38 := rfl
    exact (g 2166 (by decide) (by decide)).trans ((cell2160 6 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 38 := by
    rw [poff 1 (by decide)]
    have hval : decChunk135[7]! = 38 := rfl
    exact (g 2167 (by decide) (by decide)).trans ((cell2160 7 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk135[8]! = 2169 := rfl
    have hv : (2169 : Word) = UInt16.ofNat 2169 := rfl
    exact (g 2168 (by decide) (by decide)).trans ((cell2160 8 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk135[9]! = 30 := rfl
    exact (g 2169 (by decide) (by decide)).trans ((cell2160 9 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk135[10]! = 0 := rfl
    exact (g 2170 (by decide) (by decide)).trans ((cell2160 10 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk135[11]! = 2172 := rfl
    have hv : (2172 : Word) = UInt16.ofNat 2172 := rfl
    exact (g 2171 (by decide) (by decide)).trans ((cell2160 11 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk135[12]! = 0 := rfl
    exact (g 2172 (by decide) (by decide)).trans ((cell2160 12 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 38 := by
    rw [poff 7 (by decide)]
    have hval : decChunk135[13]! = 38 := rfl
    exact (g 2173 (by decide) (by decide)).trans ((cell2160 13 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk135[14]! = 2175 := rfl
    have hv : (2175 : Word) = UInt16.ofNat 2175 := rfl
    exact (g 2174 (by decide) (by decide)).trans ((cell2160 14 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk135[15]! = 0 := rfl
    exact (g 2175 (by decide) (by decide)).trans ((cell2160 15 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk136[0]! = 0 := rfl
    exact (g 2176 (by decide) (by decide)).trans ((cell2176 0 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk136[1]! = 2178 := rfl
    have hv : (2178 : Word) = UInt16.ofNat 2178 := rfl
    exact (g 2177 (by decide) (by decide)).trans ((cell2176 1 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (38 : Word) := by
    intro i hi
    have : (38 : Word) = UInt16.ofNat 38 := rfl
    rw [this]
    exact pc_off_ne 2166 i 38 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2166 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 38)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2178 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2178 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2178 = (2178 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2178. -/
theorem wn_enc_jmp_2178 {s : Machine}
    (hpc : s.pc = 2178)
    (hcode : ∀ k : Nat, 2178 ≤ k → k < 2178+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2178 :=
    hpc.trans (rfl : (2178 : Word) = UInt16.ofNat 2178)
  have g (k : Nat) (h1 : 2178 ≤ k) (h2 : k < 2178+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk136[2]! = 0 := rfl
    exact (g 2178 (by decide) (by decide)).trans ((cell2176 2 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2179 : Word) := by simp [hpc]
    rw [this, (rfl : (2179 : Word) = UInt16.ofNat 2179)]
    have hval : decChunk136[3]! = 0 := rfl
    exact (g 2179 (by decide) (by decide)).trans ((cell2176 3 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2180 : Word) := by simp [hpc]
    rw [this, (rfl : (2180 : Word) = UInt16.ofNat 2180)]
    have hval : decChunk136[4]! = 2316 := rfl
    exact (g 2180 (by decide) (by decide)).trans ((cell2176 4 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+7 at N7 (pc 2181). -/
theorem wn_mov_CH_BUF7_2181 {s : Machine}
    (hpc : s.pc = 2181)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2181 ≤ k → k < 2193 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2193 ∧
    s4.halted = false ∧
    s4.mem.get 39 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 39 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2181 :=
    hpc.trans (rfl : (2181 : Word) = UInt16.ofNat 2181)
  have g (k : Nat) (h1 : 2181 ≤ k) (h2 : k < 2193) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2181 + off) :=
    word_pc_off 2181 off hp (by omega)
  have m0 : s.mem.get s.pc = 39 := by
    rw [hp]
    have hval : decChunk136[5]! = 39 := rfl
    exact (g 2181 (by decide) (by decide)).trans ((cell2176 5 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 39 := by
    rw [poff 1 (by decide)]
    have hval : decChunk136[6]! = 39 := rfl
    exact (g 2182 (by decide) (by decide)).trans ((cell2176 6 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk136[7]! = 2184 := rfl
    have hv : (2184 : Word) = UInt16.ofNat 2184 := rfl
    exact (g 2183 (by decide) (by decide)).trans ((cell2176 7 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk136[8]! = 30 := rfl
    exact (g 2184 (by decide) (by decide)).trans ((cell2176 8 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk136[9]! = 0 := rfl
    exact (g 2185 (by decide) (by decide)).trans ((cell2176 9 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk136[10]! = 2187 := rfl
    have hv : (2187 : Word) = UInt16.ofNat 2187 := rfl
    exact (g 2186 (by decide) (by decide)).trans ((cell2176 10 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk136[11]! = 0 := rfl
    exact (g 2187 (by decide) (by decide)).trans ((cell2176 11 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 39 := by
    rw [poff 7 (by decide)]
    have hval : decChunk136[12]! = 39 := rfl
    exact (g 2188 (by decide) (by decide)).trans ((cell2176 12 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk136[13]! = 2190 := rfl
    have hv : (2190 : Word) = UInt16.ofNat 2190 := rfl
    exact (g 2189 (by decide) (by decide)).trans ((cell2176 13 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk136[14]! = 0 := rfl
    exact (g 2190 (by decide) (by decide)).trans ((cell2176 14 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk136[15]! = 0 := rfl
    exact (g 2191 (by decide) (by decide)).trans ((cell2176 15 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk137[0]! = 2193 := rfl
    have hv : (2193 : Word) = UInt16.ofNat 2193 := rfl
    exact (g 2192 (by decide) (by decide)).trans ((cell2192 0 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (39 : Word) := by
    intro i hi
    have : (39 : Word) = UInt16.ofNat 39 := rfl
    rw [this]
    exact pc_off_ne 2181 i 39 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2181 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 39)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2193 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2193 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2193 = (2193 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2193. -/
theorem wn_enc_jmp_2193 {s : Machine}
    (hpc : s.pc = 2193)
    (hcode : ∀ k : Nat, 2193 ≤ k → k < 2193+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2193 :=
    hpc.trans (rfl : (2193 : Word) = UInt16.ofNat 2193)
  have g (k : Nat) (h1 : 2193 ≤ k) (h2 : k < 2193+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk137[1]! = 0 := rfl
    exact (g 2193 (by decide) (by decide)).trans ((cell2192 1 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2194 : Word) := by simp [hpc]
    rw [this, (rfl : (2194 : Word) = UInt16.ofNat 2194)]
    have hval : decChunk137[2]! = 0 := rfl
    exact (g 2194 (by decide) (by decide)).trans ((cell2192 2 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2195 : Word) := by simp [hpc]
    rw [this, (rfl : (2195 : Word) = UInt16.ofNat 2195)]
    have hval : decChunk137[3]! = 2316 := rfl
    exact (g 2195 (by decide) (by decide)).trans ((cell2192 3 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+8 at N8 (pc 2196). -/
theorem wn_mov_CH_BUF8_2196 {s : Machine}
    (hpc : s.pc = 2196)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2196 ≤ k → k < 2208 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2208 ∧
    s4.halted = false ∧
    s4.mem.get 40 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 40 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2196 :=
    hpc.trans (rfl : (2196 : Word) = UInt16.ofNat 2196)
  have g (k : Nat) (h1 : 2196 ≤ k) (h2 : k < 2208) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2196 + off) :=
    word_pc_off 2196 off hp (by omega)
  have m0 : s.mem.get s.pc = 40 := by
    rw [hp]
    have hval : decChunk137[4]! = 40 := rfl
    exact (g 2196 (by decide) (by decide)).trans ((cell2192 4 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 40 := by
    rw [poff 1 (by decide)]
    have hval : decChunk137[5]! = 40 := rfl
    exact (g 2197 (by decide) (by decide)).trans ((cell2192 5 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk137[6]! = 2199 := rfl
    have hv : (2199 : Word) = UInt16.ofNat 2199 := rfl
    exact (g 2198 (by decide) (by decide)).trans ((cell2192 6 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk137[7]! = 30 := rfl
    exact (g 2199 (by decide) (by decide)).trans ((cell2192 7 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk137[8]! = 0 := rfl
    exact (g 2200 (by decide) (by decide)).trans ((cell2192 8 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk137[9]! = 2202 := rfl
    have hv : (2202 : Word) = UInt16.ofNat 2202 := rfl
    exact (g 2201 (by decide) (by decide)).trans ((cell2192 9 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk137[10]! = 0 := rfl
    exact (g 2202 (by decide) (by decide)).trans ((cell2192 10 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 40 := by
    rw [poff 7 (by decide)]
    have hval : decChunk137[11]! = 40 := rfl
    exact (g 2203 (by decide) (by decide)).trans ((cell2192 11 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk137[12]! = 2205 := rfl
    have hv : (2205 : Word) = UInt16.ofNat 2205 := rfl
    exact (g 2204 (by decide) (by decide)).trans ((cell2192 12 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk137[13]! = 0 := rfl
    exact (g 2205 (by decide) (by decide)).trans ((cell2192 13 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk137[14]! = 0 := rfl
    exact (g 2206 (by decide) (by decide)).trans ((cell2192 14 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk137[15]! = 2208 := rfl
    have hv : (2208 : Word) = UInt16.ofNat 2208 := rfl
    exact (g 2207 (by decide) (by decide)).trans ((cell2192 15 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (40 : Word) := by
    intro i hi
    have : (40 : Word) = UInt16.ofNat 40 := rfl
    rw [this]
    exact pc_off_ne 2196 i 40 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2196 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 40)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2208 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2208 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2208 = (2208 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2208. -/
theorem wn_enc_jmp_2208 {s : Machine}
    (hpc : s.pc = 2208)
    (hcode : ∀ k : Nat, 2208 ≤ k → k < 2208+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2208 :=
    hpc.trans (rfl : (2208 : Word) = UInt16.ofNat 2208)
  have g (k : Nat) (h1 : 2208 ≤ k) (h2 : k < 2208+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk138[0]! = 0 := rfl
    exact (g 2208 (by decide) (by decide)).trans ((cell2208 0 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2209 : Word) := by simp [hpc]
    rw [this, (rfl : (2209 : Word) = UInt16.ofNat 2209)]
    have hval : decChunk138[1]! = 0 := rfl
    exact (g 2209 (by decide) (by decide)).trans ((cell2208 1 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2210 : Word) := by simp [hpc]
    rw [this, (rfl : (2210 : Word) = UInt16.ofNat 2210)]
    have hval : decChunk138[2]! = 2316 := rfl
    exact (g 2210 (by decide) (by decide)).trans ((cell2208 2 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+9 at N9 (pc 2211). -/
theorem wn_mov_CH_BUF9_2211 {s : Machine}
    (hpc : s.pc = 2211)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2211 ≤ k → k < 2223 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2223 ∧
    s4.halted = false ∧
    s4.mem.get 41 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 41 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2211 :=
    hpc.trans (rfl : (2211 : Word) = UInt16.ofNat 2211)
  have g (k : Nat) (h1 : 2211 ≤ k) (h2 : k < 2223) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2211 + off) :=
    word_pc_off 2211 off hp (by omega)
  have m0 : s.mem.get s.pc = 41 := by
    rw [hp]
    have hval : decChunk138[3]! = 41 := rfl
    exact (g 2211 (by decide) (by decide)).trans ((cell2208 3 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 41 := by
    rw [poff 1 (by decide)]
    have hval : decChunk138[4]! = 41 := rfl
    exact (g 2212 (by decide) (by decide)).trans ((cell2208 4 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk138[5]! = 2214 := rfl
    have hv : (2214 : Word) = UInt16.ofNat 2214 := rfl
    exact (g 2213 (by decide) (by decide)).trans ((cell2208 5 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk138[6]! = 30 := rfl
    exact (g 2214 (by decide) (by decide)).trans ((cell2208 6 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk138[7]! = 0 := rfl
    exact (g 2215 (by decide) (by decide)).trans ((cell2208 7 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk138[8]! = 2217 := rfl
    have hv : (2217 : Word) = UInt16.ofNat 2217 := rfl
    exact (g 2216 (by decide) (by decide)).trans ((cell2208 8 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk138[9]! = 0 := rfl
    exact (g 2217 (by decide) (by decide)).trans ((cell2208 9 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 41 := by
    rw [poff 7 (by decide)]
    have hval : decChunk138[10]! = 41 := rfl
    exact (g 2218 (by decide) (by decide)).trans ((cell2208 10 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk138[11]! = 2220 := rfl
    have hv : (2220 : Word) = UInt16.ofNat 2220 := rfl
    exact (g 2219 (by decide) (by decide)).trans ((cell2208 11 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk138[12]! = 0 := rfl
    exact (g 2220 (by decide) (by decide)).trans ((cell2208 12 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk138[13]! = 0 := rfl
    exact (g 2221 (by decide) (by decide)).trans ((cell2208 13 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk138[14]! = 2223 := rfl
    have hv : (2223 : Word) = UInt16.ofNat 2223 := rfl
    exact (g 2222 (by decide) (by decide)).trans ((cell2208 14 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (41 : Word) := by
    intro i hi
    have : (41 : Word) = UInt16.ofNat 41 := rfl
    rw [this]
    exact pc_off_ne 2211 i 41 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2211 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 41)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2223 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2223 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2223 = (2223 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2223. -/
theorem wn_enc_jmp_2223 {s : Machine}
    (hpc : s.pc = 2223)
    (hcode : ∀ k : Nat, 2223 ≤ k → k < 2223+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2223 :=
    hpc.trans (rfl : (2223 : Word) = UInt16.ofNat 2223)
  have g (k : Nat) (h1 : 2223 ≤ k) (h2 : k < 2223+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk138[15]! = 0 := rfl
    exact (g 2223 (by decide) (by decide)).trans ((cell2208 15 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2224 : Word) := by simp [hpc]
    rw [this, (rfl : (2224 : Word) = UInt16.ofNat 2224)]
    have hval : decChunk139[0]! = 0 := rfl
    exact (g 2224 (by decide) (by decide)).trans ((cell2224 0 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2225 : Word) := by simp [hpc]
    rw [this, (rfl : (2225 : Word) = UInt16.ofNat 2225)]
    have hval : decChunk139[1]! = 2316 := rfl
    exact (g 2225 (by decide) (by decide)).trans ((cell2224 1 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+10 at N10 (pc 2226). -/
theorem wn_mov_CH_BUF10_2226 {s : Machine}
    (hpc : s.pc = 2226)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2226 ≤ k → k < 2238 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2238 ∧
    s4.halted = false ∧
    s4.mem.get 42 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 42 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2226 :=
    hpc.trans (rfl : (2226 : Word) = UInt16.ofNat 2226)
  have g (k : Nat) (h1 : 2226 ≤ k) (h2 : k < 2238) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2226 + off) :=
    word_pc_off 2226 off hp (by omega)
  have m0 : s.mem.get s.pc = 42 := by
    rw [hp]
    have hval : decChunk139[2]! = 42 := rfl
    exact (g 2226 (by decide) (by decide)).trans ((cell2224 2 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 42 := by
    rw [poff 1 (by decide)]
    have hval : decChunk139[3]! = 42 := rfl
    exact (g 2227 (by decide) (by decide)).trans ((cell2224 3 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk139[4]! = 2229 := rfl
    have hv : (2229 : Word) = UInt16.ofNat 2229 := rfl
    exact (g 2228 (by decide) (by decide)).trans ((cell2224 4 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk139[5]! = 30 := rfl
    exact (g 2229 (by decide) (by decide)).trans ((cell2224 5 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk139[6]! = 0 := rfl
    exact (g 2230 (by decide) (by decide)).trans ((cell2224 6 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk139[7]! = 2232 := rfl
    have hv : (2232 : Word) = UInt16.ofNat 2232 := rfl
    exact (g 2231 (by decide) (by decide)).trans ((cell2224 7 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk139[8]! = 0 := rfl
    exact (g 2232 (by decide) (by decide)).trans ((cell2224 8 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 42 := by
    rw [poff 7 (by decide)]
    have hval : decChunk139[9]! = 42 := rfl
    exact (g 2233 (by decide) (by decide)).trans ((cell2224 9 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk139[10]! = 2235 := rfl
    have hv : (2235 : Word) = UInt16.ofNat 2235 := rfl
    exact (g 2234 (by decide) (by decide)).trans ((cell2224 10 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk139[11]! = 0 := rfl
    exact (g 2235 (by decide) (by decide)).trans ((cell2224 11 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk139[12]! = 0 := rfl
    exact (g 2236 (by decide) (by decide)).trans ((cell2224 12 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk139[13]! = 2238 := rfl
    have hv : (2238 : Word) = UInt16.ofNat 2238 := rfl
    exact (g 2237 (by decide) (by decide)).trans ((cell2224 13 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (42 : Word) := by
    intro i hi
    have : (42 : Word) = UInt16.ofNat 42 := rfl
    rw [this]
    exact pc_off_ne 2226 i 42 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2226 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 42)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2238 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2238 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2238 = (2238 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2238. -/
theorem wn_enc_jmp_2238 {s : Machine}
    (hpc : s.pc = 2238)
    (hcode : ∀ k : Nat, 2238 ≤ k → k < 2238+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2238 :=
    hpc.trans (rfl : (2238 : Word) = UInt16.ofNat 2238)
  have g (k : Nat) (h1 : 2238 ≤ k) (h2 : k < 2238+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk139[14]! = 0 := rfl
    exact (g 2238 (by decide) (by decide)).trans ((cell2224 14 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2239 : Word) := by simp [hpc]
    rw [this, (rfl : (2239 : Word) = UInt16.ofNat 2239)]
    have hval : decChunk139[15]! = 0 := rfl
    exact (g 2239 (by decide) (by decide)).trans ((cell2224 15 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2240 : Word) := by simp [hpc]
    rw [this, (rfl : (2240 : Word) = UInt16.ofNat 2240)]
    have hval : decChunk140[0]! = 2316 := rfl
    exact (g 2240 (by decide) (by decide)).trans ((cell2240 0 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+11 at N11 (pc 2241). -/
theorem wn_mov_CH_BUF11_2241 {s : Machine}
    (hpc : s.pc = 2241)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2241 ≤ k → k < 2253 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2253 ∧
    s4.halted = false ∧
    s4.mem.get 43 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 43 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2241 :=
    hpc.trans (rfl : (2241 : Word) = UInt16.ofNat 2241)
  have g (k : Nat) (h1 : 2241 ≤ k) (h2 : k < 2253) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2241 + off) :=
    word_pc_off 2241 off hp (by omega)
  have m0 : s.mem.get s.pc = 43 := by
    rw [hp]
    have hval : decChunk140[1]! = 43 := rfl
    exact (g 2241 (by decide) (by decide)).trans ((cell2240 1 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 43 := by
    rw [poff 1 (by decide)]
    have hval : decChunk140[2]! = 43 := rfl
    exact (g 2242 (by decide) (by decide)).trans ((cell2240 2 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk140[3]! = 2244 := rfl
    have hv : (2244 : Word) = UInt16.ofNat 2244 := rfl
    exact (g 2243 (by decide) (by decide)).trans ((cell2240 3 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk140[4]! = 30 := rfl
    exact (g 2244 (by decide) (by decide)).trans ((cell2240 4 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk140[5]! = 0 := rfl
    exact (g 2245 (by decide) (by decide)).trans ((cell2240 5 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk140[6]! = 2247 := rfl
    have hv : (2247 : Word) = UInt16.ofNat 2247 := rfl
    exact (g 2246 (by decide) (by decide)).trans ((cell2240 6 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk140[7]! = 0 := rfl
    exact (g 2247 (by decide) (by decide)).trans ((cell2240 7 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 43 := by
    rw [poff 7 (by decide)]
    have hval : decChunk140[8]! = 43 := rfl
    exact (g 2248 (by decide) (by decide)).trans ((cell2240 8 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk140[9]! = 2250 := rfl
    have hv : (2250 : Word) = UInt16.ofNat 2250 := rfl
    exact (g 2249 (by decide) (by decide)).trans ((cell2240 9 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk140[10]! = 0 := rfl
    exact (g 2250 (by decide) (by decide)).trans ((cell2240 10 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk140[11]! = 0 := rfl
    exact (g 2251 (by decide) (by decide)).trans ((cell2240 11 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk140[12]! = 2253 := rfl
    have hv : (2253 : Word) = UInt16.ofNat 2253 := rfl
    exact (g 2252 (by decide) (by decide)).trans ((cell2240 12 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (43 : Word) := by
    intro i hi
    have : (43 : Word) = UInt16.ofNat 43 := rfl
    rw [this]
    exact pc_off_ne 2241 i 43 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2241 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 43)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2253 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2253 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2253 = (2253 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2253. -/
theorem wn_enc_jmp_2253 {s : Machine}
    (hpc : s.pc = 2253)
    (hcode : ∀ k : Nat, 2253 ≤ k → k < 2253+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2253 :=
    hpc.trans (rfl : (2253 : Word) = UInt16.ofNat 2253)
  have g (k : Nat) (h1 : 2253 ≤ k) (h2 : k < 2253+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk140[13]! = 0 := rfl
    exact (g 2253 (by decide) (by decide)).trans ((cell2240 13 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2254 : Word) := by simp [hpc]
    rw [this, (rfl : (2254 : Word) = UInt16.ofNat 2254)]
    have hval : decChunk140[14]! = 0 := rfl
    exact (g 2254 (by decide) (by decide)).trans ((cell2240 14 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2255 : Word) := by simp [hpc]
    rw [this, (rfl : (2255 : Word) = UInt16.ofNat 2255)]
    have hval : decChunk140[15]! = 2316 := rfl
    exact (g 2255 (by decide) (by decide)).trans ((cell2240 15 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+12 at N12 (pc 2256). -/
theorem wn_mov_CH_BUF12_2256 {s : Machine}
    (hpc : s.pc = 2256)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2256 ≤ k → k < 2268 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2268 ∧
    s4.halted = false ∧
    s4.mem.get 44 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 44 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2256 :=
    hpc.trans (rfl : (2256 : Word) = UInt16.ofNat 2256)
  have g (k : Nat) (h1 : 2256 ≤ k) (h2 : k < 2268) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2256 + off) :=
    word_pc_off 2256 off hp (by omega)
  have m0 : s.mem.get s.pc = 44 := by
    rw [hp]
    have hval : decChunk141[0]! = 44 := rfl
    exact (g 2256 (by decide) (by decide)).trans ((cell2256 0 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 44 := by
    rw [poff 1 (by decide)]
    have hval : decChunk141[1]! = 44 := rfl
    exact (g 2257 (by decide) (by decide)).trans ((cell2256 1 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk141[2]! = 2259 := rfl
    have hv : (2259 : Word) = UInt16.ofNat 2259 := rfl
    exact (g 2258 (by decide) (by decide)).trans ((cell2256 2 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk141[3]! = 30 := rfl
    exact (g 2259 (by decide) (by decide)).trans ((cell2256 3 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk141[4]! = 0 := rfl
    exact (g 2260 (by decide) (by decide)).trans ((cell2256 4 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk141[5]! = 2262 := rfl
    have hv : (2262 : Word) = UInt16.ofNat 2262 := rfl
    exact (g 2261 (by decide) (by decide)).trans ((cell2256 5 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk141[6]! = 0 := rfl
    exact (g 2262 (by decide) (by decide)).trans ((cell2256 6 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 44 := by
    rw [poff 7 (by decide)]
    have hval : decChunk141[7]! = 44 := rfl
    exact (g 2263 (by decide) (by decide)).trans ((cell2256 7 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk141[8]! = 2265 := rfl
    have hv : (2265 : Word) = UInt16.ofNat 2265 := rfl
    exact (g 2264 (by decide) (by decide)).trans ((cell2256 8 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk141[9]! = 0 := rfl
    exact (g 2265 (by decide) (by decide)).trans ((cell2256 9 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk141[10]! = 0 := rfl
    exact (g 2266 (by decide) (by decide)).trans ((cell2256 10 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk141[11]! = 2268 := rfl
    have hv : (2268 : Word) = UInt16.ofNat 2268 := rfl
    exact (g 2267 (by decide) (by decide)).trans ((cell2256 11 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (44 : Word) := by
    intro i hi
    have : (44 : Word) = UInt16.ofNat 44 := rfl
    rw [this]
    exact pc_off_ne 2256 i 44 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2256 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 44)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2268 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2268 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2268 = (2268 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2268. -/
theorem wn_enc_jmp_2268 {s : Machine}
    (hpc : s.pc = 2268)
    (hcode : ∀ k : Nat, 2268 ≤ k → k < 2268+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2268 :=
    hpc.trans (rfl : (2268 : Word) = UInt16.ofNat 2268)
  have g (k : Nat) (h1 : 2268 ≤ k) (h2 : k < 2268+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk141[12]! = 0 := rfl
    exact (g 2268 (by decide) (by decide)).trans ((cell2256 12 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2269 : Word) := by simp [hpc]
    rw [this, (rfl : (2269 : Word) = UInt16.ofNat 2269)]
    have hval : decChunk141[13]! = 0 := rfl
    exact (g 2269 (by decide) (by decide)).trans ((cell2256 13 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2270 : Word) := by simp [hpc]
    rw [this, (rfl : (2270 : Word) = UInt16.ofNat 2270)]
    have hval : decChunk141[14]! = 2316 := rfl
    exact (g 2270 (by decide) (by decide)).trans ((cell2256 14 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+13 at N13 (pc 2271). -/
theorem wn_mov_CH_BUF13_2271 {s : Machine}
    (hpc : s.pc = 2271)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2271 ≤ k → k < 2283 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2283 ∧
    s4.halted = false ∧
    s4.mem.get 45 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 45 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2271 :=
    hpc.trans (rfl : (2271 : Word) = UInt16.ofNat 2271)
  have g (k : Nat) (h1 : 2271 ≤ k) (h2 : k < 2283) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2271 + off) :=
    word_pc_off 2271 off hp (by omega)
  have m0 : s.mem.get s.pc = 45 := by
    rw [hp]
    have hval : decChunk141[15]! = 45 := rfl
    exact (g 2271 (by decide) (by decide)).trans ((cell2256 15 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 45 := by
    rw [poff 1 (by decide)]
    have hval : decChunk142[0]! = 45 := rfl
    exact (g 2272 (by decide) (by decide)).trans ((cell2272 0 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk142[1]! = 2274 := rfl
    have hv : (2274 : Word) = UInt16.ofNat 2274 := rfl
    exact (g 2273 (by decide) (by decide)).trans ((cell2272 1 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk142[2]! = 30 := rfl
    exact (g 2274 (by decide) (by decide)).trans ((cell2272 2 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk142[3]! = 0 := rfl
    exact (g 2275 (by decide) (by decide)).trans ((cell2272 3 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk142[4]! = 2277 := rfl
    have hv : (2277 : Word) = UInt16.ofNat 2277 := rfl
    exact (g 2276 (by decide) (by decide)).trans ((cell2272 4 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk142[5]! = 0 := rfl
    exact (g 2277 (by decide) (by decide)).trans ((cell2272 5 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 45 := by
    rw [poff 7 (by decide)]
    have hval : decChunk142[6]! = 45 := rfl
    exact (g 2278 (by decide) (by decide)).trans ((cell2272 6 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk142[7]! = 2280 := rfl
    have hv : (2280 : Word) = UInt16.ofNat 2280 := rfl
    exact (g 2279 (by decide) (by decide)).trans ((cell2272 7 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk142[8]! = 0 := rfl
    exact (g 2280 (by decide) (by decide)).trans ((cell2272 8 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk142[9]! = 0 := rfl
    exact (g 2281 (by decide) (by decide)).trans ((cell2272 9 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk142[10]! = 2283 := rfl
    have hv : (2283 : Word) = UInt16.ofNat 2283 := rfl
    exact (g 2282 (by decide) (by decide)).trans ((cell2272 10 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (45 : Word) := by
    intro i hi
    have : (45 : Word) = UInt16.ofNat 45 := rfl
    rw [this]
    exact pc_off_ne 2271 i 45 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2271 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 45)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2283 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2283 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2283 = (2283 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2283. -/
theorem wn_enc_jmp_2283 {s : Machine}
    (hpc : s.pc = 2283)
    (hcode : ∀ k : Nat, 2283 ≤ k → k < 2283+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2283 :=
    hpc.trans (rfl : (2283 : Word) = UInt16.ofNat 2283)
  have g (k : Nat) (h1 : 2283 ≤ k) (h2 : k < 2283+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk142[11]! = 0 := rfl
    exact (g 2283 (by decide) (by decide)).trans ((cell2272 11 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2284 : Word) := by simp [hpc]
    rw [this, (rfl : (2284 : Word) = UInt16.ofNat 2284)]
    have hval : decChunk142[12]! = 0 := rfl
    exact (g 2284 (by decide) (by decide)).trans ((cell2272 12 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2285 : Word) := by simp [hpc]
    rw [this, (rfl : (2285 : Word) = UInt16.ofNat 2285)]
    have hval : decChunk142[13]! = 2316 := rfl
    exact (g 2285 (by decide) (by decide)).trans ((cell2272 13 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+14 at N14 (pc 2286). -/
theorem wn_mov_CH_BUF14_2286 {s : Machine}
    (hpc : s.pc = 2286)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2286 ≤ k → k < 2298 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2298 ∧
    s4.halted = false ∧
    s4.mem.get 46 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 46 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2286 :=
    hpc.trans (rfl : (2286 : Word) = UInt16.ofNat 2286)
  have g (k : Nat) (h1 : 2286 ≤ k) (h2 : k < 2298) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2286 + off) :=
    word_pc_off 2286 off hp (by omega)
  have m0 : s.mem.get s.pc = 46 := by
    rw [hp]
    have hval : decChunk142[14]! = 46 := rfl
    exact (g 2286 (by decide) (by decide)).trans ((cell2272 14 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 46 := by
    rw [poff 1 (by decide)]
    have hval : decChunk142[15]! = 46 := rfl
    exact (g 2287 (by decide) (by decide)).trans ((cell2272 15 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk143[0]! = 2289 := rfl
    have hv : (2289 : Word) = UInt16.ofNat 2289 := rfl
    exact (g 2288 (by decide) (by decide)).trans ((cell2288 0 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk143[1]! = 30 := rfl
    exact (g 2289 (by decide) (by decide)).trans ((cell2288 1 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk143[2]! = 0 := rfl
    exact (g 2290 (by decide) (by decide)).trans ((cell2288 2 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk143[3]! = 2292 := rfl
    have hv : (2292 : Word) = UInt16.ofNat 2292 := rfl
    exact (g 2291 (by decide) (by decide)).trans ((cell2288 3 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk143[4]! = 0 := rfl
    exact (g 2292 (by decide) (by decide)).trans ((cell2288 4 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 46 := by
    rw [poff 7 (by decide)]
    have hval : decChunk143[5]! = 46 := rfl
    exact (g 2293 (by decide) (by decide)).trans ((cell2288 5 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk143[6]! = 2295 := rfl
    have hv : (2295 : Word) = UInt16.ofNat 2295 := rfl
    exact (g 2294 (by decide) (by decide)).trans ((cell2288 6 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk143[7]! = 0 := rfl
    exact (g 2295 (by decide) (by decide)).trans ((cell2288 7 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk143[8]! = 0 := rfl
    exact (g 2296 (by decide) (by decide)).trans ((cell2288 8 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk143[9]! = 2298 := rfl
    have hv : (2298 : Word) = UInt16.ofNat 2298 := rfl
    exact (g 2297 (by decide) (by decide)).trans ((cell2288 9 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (46 : Word) := by
    intro i hi
    have : (46 : Word) = UInt16.ofNat 46 := rfl
    rw [this]
    exact pc_off_ne 2286 i 46 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2286 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 46)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2298 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2298 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2298 = (2298 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2298. -/
theorem wn_enc_jmp_2298 {s : Machine}
    (hpc : s.pc = 2298)
    (hcode : ∀ k : Nat, 2298 ≤ k → k < 2298+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2298 :=
    hpc.trans (rfl : (2298 : Word) = UInt16.ofNat 2298)
  have g (k : Nat) (h1 : 2298 ≤ k) (h2 : k < 2298+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk143[10]! = 0 := rfl
    exact (g 2298 (by decide) (by decide)).trans ((cell2288 10 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2299 : Word) := by simp [hpc]
    rw [this, (rfl : (2299 : Word) = UInt16.ofNat 2299)]
    have hval : decChunk143[11]! = 0 := rfl
    exact (g 2299 (by decide) (by decide)).trans ((cell2288 11 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2300 : Word) := by simp [hpc]
    rw [this, (rfl : (2300 : Word) = UInt16.ofNat 2300)]
    have hval : decChunk143[12]! = 2316 := rfl
    exact (g 2300 (by decide) (by decide)).trans ((cell2288 12 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+15 at N15 (pc 2301). -/
theorem wn_mov_CH_BUF15_2301 {s : Machine}
    (hpc : s.pc = 2301)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 2301 ≤ k → k < 2313 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 2313 ∧
    s4.halted = false ∧
    s4.mem.get 47 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 47 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 2301 :=
    hpc.trans (rfl : (2301 : Word) = UInt16.ofNat 2301)
  have g (k : Nat) (h1 : 2301 ≤ k) (h2 : k < 2313) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (2301 + off) :=
    word_pc_off 2301 off hp (by omega)
  have m0 : s.mem.get s.pc = 47 := by
    rw [hp]
    have hval : decChunk143[13]! = 47 := rfl
    exact (g 2301 (by decide) (by decide)).trans ((cell2288 13 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 47 := by
    rw [poff 1 (by decide)]
    have hval : decChunk143[14]! = 47 := rfl
    exact (g 2302 (by decide) (by decide)).trans ((cell2288 14 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk143[15]! = 2304 := rfl
    have hv : (2304 : Word) = UInt16.ofNat 2304 := rfl
    exact (g 2303 (by decide) (by decide)).trans ((cell2288 15 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk144[0]! = 30 := rfl
    exact (g 2304 (by decide) (by decide)).trans ((cell2304 0 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk144[1]! = 0 := rfl
    exact (g 2305 (by decide) (by decide)).trans ((cell2304 1 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk144[2]! = 2307 := rfl
    have hv : (2307 : Word) = UInt16.ofNat 2307 := rfl
    exact (g 2306 (by decide) (by decide)).trans ((cell2304 2 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk144[3]! = 0 := rfl
    exact (g 2307 (by decide) (by decide)).trans ((cell2304 3 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 47 := by
    rw [poff 7 (by decide)]
    have hval : decChunk144[4]! = 47 := rfl
    exact (g 2308 (by decide) (by decide)).trans ((cell2304 4 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk144[5]! = 2310 := rfl
    have hv : (2310 : Word) = UInt16.ofNat 2310 := rfl
    exact (g 2309 (by decide) (by decide)).trans ((cell2304 5 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk144[6]! = 0 := rfl
    exact (g 2310 (by decide) (by decide)).trans ((cell2304 6 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk144[7]! = 0 := rfl
    exact (g 2311 (by decide) (by decide)).trans ((cell2304 7 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk144[8]! = 2313 := rfl
    have hv : (2313 : Word) = UInt16.ofNat 2313 := rfl
    exact (g 2312 (by decide) (by decide)).trans ((cell2304 8 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (47 : Word) := by
    intro i hi
    have : (47 : Word) = UInt16.ofNat 47 := rfl
    rw [this]
    exact pc_off_ne 2301 i 47 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 2301 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 47)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 2313 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (2313 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 2313 = (2313 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP DONE at pc 2313. -/
theorem wn_enc_jmp_2313 {s : Machine}
    (hpc : s.pc = 2313)
    (hcode : ∀ k : Nat, 2313 ≤ k → k < 2313+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 2313 :=
    hpc.trans (rfl : (2313 : Word) = UInt16.ofNat 2313)
  have g (k : Nat) (h1 : 2313 ≤ k) (h2 : k < 2313+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk144[9]! = 0 := rfl
    exact (g 2313 (by decide) (by decide)).trans ((cell2304 9 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2314 : Word) := by simp [hpc]
    rw [this, (rfl : (2314 : Word) = UInt16.ofNat 2314)]
    have hval : decChunk144[10]! = 0 := rfl
    exact (g 2314 (by decide) (by decide)).trans ((cell2304 10 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (2315 : Word) := by simp [hpc]
    rw [this, (rfl : (2315 : Word) = UInt16.ofNat 2315)]
    have hval : decChunk144[11]! = 2316 := rfl
    exact (g 2315 (by decide) (by decide)).trans ((cell2304 11 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩


/-- `AFTER_DIGS` with `LEN < CAP`: 15 steps, `IDX = LEN`, pc = `WRITE_NUL`. -/
theorem after_digs_nul_at_len {s : Machine}
    (hpc : s.pc = 1905)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hLlt : (s.mem.get 16).toNat < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1905 ≤ k → k < 1971 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s15 := runN s 15
    s15.pc = 1971 ∧
    s15.halted = false ∧
    s15.mem.get 0 = 0 ∧
    s15.mem.get 29 = s.mem.get 16 ∧
    s15.mem.get 16 = s.mem.get 16 ∧
    s15.mem.get 13 = s.mem.get 13 ∧
    (∀ a, a ≠ 18 → a ≠ 29 → a ≠ 0 → s15.mem.get a = s.mem.get a) := by
  intro s15
  have hm := wn_mov_LEN_T_1905 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1917 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 16 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hL4 : s4.mem.get 16 = s.mem.get 16 := hm.2.2.2.2.1
  have hC4 : s4.mem.get 13 = s.mem.get 13 := hpres4 13 (by decide) (by decide)
  have gs4 : ∀ k : Nat, 1917 ≤ k → k < 1920 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hsub := wn_sub_CAP_T_1917 (s := s4) hs4pc hs4h
    (fun k h1 h2 => gs4 k h1 (by omega))
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hrun5_s : s5 = _ := hrun5
  have hs5eq' : s5 =
      { s4 with mem := s4.mem.set 18 (s4.mem.get 18 - s4.mem.get 13), pc := 1920 } := by
    have : s5 = step s4 := hrun5
    rw [this, hsub]
  have hs5pc : s5.pc = 1920 := by rw [hs5eq']
  have hs5h : s5.halted = false := by rw [hs5eq']; exact hs4h
  have hs5T : s5.mem.get 18 = s.mem.get 16 - s.mem.get 13 := by
    rw [hs5eq', Mem.get_set_eq, hs4T, hC4]
  have hs5Z : s5.mem.get 0 = 0 := by
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - s4.mem.get 13) (by decide)).trans hs4Z
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq']
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - s4.mem.get 13) ha18).trans
      (hpres4 a ha18 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hL5 : s5.mem.get 16 = s.mem.get 16 := hpres5 16 (by decide) (by decide)
  have hC5 : s5.mem.get 13 = s.mem.get 13 := hpres5 13 (by decide) (by decide)
  have gs5 : ∀ k : Nat, 1920 ≤ k → k < 1923 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc1 := wn_enc_jlez_1920 (s := s5) hs5pc gs5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj1 :=
    step_JLEZ (s := s5) (x := 18) (dest := 1926)
      hs5h hpc5 hs5Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = true := by
    have : le0 (s5.mem.get 18) = true := by
      rw [hs5T]; exact idx_lt_room_le0 (s.mem.get 16) (s.mem.get 13) hChi hLlt
    simpa [le0] using this
  have hs6step : step s5 = { s5 with pc := 1926 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (1926 : Word) else s5.pc + 3) = (1926 : Word) := by
      simp [hle1]
    rw [hj1, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hrun6_s : s6 = _ := hrun6
  have hs6eq : s6 = { s5 with pc := 1926 } := by
    have : s6 = step s5 := hrun6
    rw [this, hs6step]
  have hs6pc : s6.pc = 1926 := by rw [hs6eq]
  have hs6h : s6.halted = false := by rw [hs6eq]; exact hs5h
  have hs6T : s6.mem.get 18 = s.mem.get 16 - s.mem.get 13 := by rw [hs6eq]; exact hs5T
  have hs6Z : s6.mem.get 0 = 0 := by rw [hs6eq]; exact hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs6eq]; exact hpres5 a ha18 ha0
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have hL6 : s6.mem.get 16 = s.mem.get 16 := hpres6 16 (by decide) (by decide)
  have hC6 : s6.mem.get 13 = s.mem.get 13 := hpres6 13 (by decide) (by decide)
  have gs6 : ∀ k : Nat, 1926 ≤ k → k < 1935 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hinc := wn_inc_T_1926 (s := s6) hs6pc hs6h hs6Z hONE6 gs6
  have hrun9 : runN s 9 = runN s6 3 := runN_add_eq s 6 3 9 (by decide)
  let s9 := runN s 9
  have hrun9_s : s9 = _ := hrun9
  have hs9pc : s9.pc = 1935 := by rw [hrun9_s]; exact hinc.1
  have hs9h : s9.halted = false := by rw [hrun9_s]; exact hinc.2.1
  have hs9T : s9.mem.get 18 = (s.mem.get 16 - s.mem.get 13) + 1 := by
    rw [hrun9_s, hinc.2.2.1, hs6T]
  have hs9Z : s9.mem.get 0 = 0 := by rw [hrun9_s]; exact hinc.2.2.2.1
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun9_s]
    exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide)).trans hONE
  have hL9 : s9.mem.get 16 = s.mem.get 16 := hpres9 16 (by decide) (by decide)
  have hC9 : s9.mem.get 13 = s.mem.get 13 := hpres9 13 (by decide) (by decide)
  have gs9 : ∀ k : Nat, 1935 ≤ k → k < 1938 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc2 := wn_enc_jlez_1935 (s := s9) hs9pc gs9
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hj2 :=
    step_JLEZ (s := s9) (x := 18) (dest := 1941)
      hs9h hpc9 hs9Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = true := by
    have : le0 (s9.mem.get 18) = true := by
      rw [hs9T]; exact idx_lt_room_inc_le0 (s.mem.get 16) (s.mem.get 13) hChi hLlt
    simpa [le0] using this
  have hs10step : step s9 = { s9 with pc := 1941 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18
          then (1941 : Word) else s9.pc + 3) = (1941 : Word) := by
      simp [hle2]
    rw [hj2, hif]
  have hrun10 : runN s 10 = step s9 := by
    have h10 : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact h10.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hrun10_s : s10 = _ := hrun10
  have hs10eq : s10 = { s9 with pc := 1941 } := by
    have : s10 = step s9 := hrun10
    rw [this, hs10step]
  have hs10pc : s10.pc = 1941 := by rw [hs10eq]
  have hs10h : s10.halted = false := by rw [hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by rw [hs10eq]; exact hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs10eq]; exact hpres9 a ha18 ha0
  have hL10 : s10.mem.get 16 = s.mem.get 16 := hpres10 16 (by decide) (by decide)
  have hC10 : s10.mem.get 13 = s.mem.get 13 := hpres10 13 (by decide) (by decide)
  have gs10 : ∀ k : Nat, 1941 ≤ k → k < 1953 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hm2 := wn_mov_LEN_IDX_1941 (s := s10) hs10pc hs10h hs10Z gs10
  have hrun14 : runN s 14 = runN s10 4 := runN_add_eq s 10 4 14 (by decide)
  let s14 := runN s 14
  have hrun14_s : s14 = _ := hrun14
  have hs14pc : s14.pc = 1953 := by rw [hrun14_s]; exact hm2.1
  have hs14h : s14.halted = false := by rw [hrun14_s]; exact hm2.2.1
  have hs14I : s14.mem.get 29 = s.mem.get 16 := by
    rw [hrun14_s, hm2.2.2.1, hL10]
  have hs14Z : s14.mem.get 0 = 0 := by rw [hrun14_s]; exact hm2.2.2.2.1
  have hpres14mov := hm2.2.2.2.2.2
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 29 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha29 ha0
    rw [hrun14_s]
    exact (hpres14mov a ha29 ha0).trans (hpres10 a ha18 ha0)
  have hL14 : s14.mem.get 16 = s.mem.get 16 := by
    rw [hrun14_s]
    exact (hpres14mov 16 (by decide) (by decide)).trans hL10
  have hC14 : s14.mem.get 13 = s.mem.get 13 := hpres14 13 (by decide) (by decide) (by decide)
  have gs14 : ∀ k : Nat, 1953 ≤ k → k < 1956 →
      s14.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    exact (hpres14 (UInt16.ofNat k) n18 n29 n0).trans (hcode k (by omega) (by omega))
  have henc3 := wn_enc_jmp_1953 (s := s14) hs14pc gs14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hj3 :=
    step_JMP (s := s14) (dest := 1971)
      hs14h hpc14 hs14Z henc3.1 henc3.2.1 henc3.2.2
  have hrun15 : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
  have hs15eq : s15 = step s14 := hrun15.trans (runN_one s14 hs14h hpc14)
  have hs15pc : s15.pc = 1971 := by rw [hs15eq, hj3]
  have hs15h : s15.halted = false := by rw [hs15eq, hj3]; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by rw [hs15eq, hj3]; exact hs14Z
  have hs15I : s15.mem.get 29 = s.mem.get 16 := by rw [hs15eq, hj3]; exact hs14I
  have hs15L : s15.mem.get 16 = s.mem.get 16 := by rw [hs15eq, hj3]; exact hL14
  have hs15C : s15.mem.get 13 = s.mem.get 13 := by rw [hs15eq, hj3]; exact hC14
  have hpres : ∀ a, a ≠ 18 → a ≠ 29 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha29 ha0
    rw [hs15eq, hj3]; exact hpres14 a ha18 ha29 ha0
  exact ⟨hs15pc, hs15h, hs15Z, hs15I, hs15L, hs15C, hpres⟩


/-- `WRITE_NUL` with `IDX = 0`: 11 steps, write `0` at `BUF+0`, pc = `DONE`. -/
theorem write_nul_idx0 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 0)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2316 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 11
    sN.pc = 2316 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 32 = 0 ∧
    sN.mem.get 29 = 0 ∧
    sN.mem.get 30 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hz := wn_zero_CH_1971 (s := s) hpc hh
    (fun k h1 h2 => hcode k h1 (by omega))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hrun1 : runN s 1 = step s := runN_one s hh hpc0
  let s1 := runN s 1
  have hrun1_s : s1 = _ := hrun1
  have hs1eq : s1 = { s with mem := s.mem.set 30 0, pc := 1974 } := by
    have : s1 = step s := hrun1
    rw [this, hz]
  have hs1pc : s1.pc = 1974 := by rw [hs1eq]
  have hs1h : s1.halted = false := by rw [hs1eq]; exact hh
  have hs1Z : s1.mem.get 0 = 0 := by
    rw [hs1eq]
    exact (Mem.get_set_ne s.mem 30 0 0 (by decide)).trans hZ
  have hs1CH : s1.mem.get 30 = 0 := by rw [hs1eq, Mem.get_set_eq]
  have hpres1 : ∀ a, a ≠ 30 → a ≠ 0 → s1.mem.get a = s.mem.get a := by
    intro a ha30 ha0
    rw [hs1eq]
    exact Mem.get_set_ne s.mem 30 a 0 ha30
  have hONE1 : s1.mem.get 3 = 1 := (hpres1 3 (by decide) (by decide)).trans hONE
  have hI1 : s1.mem.get 29 = 0 := (hpres1 29 (by decide) (by decide)).trans hI
  -- g for MOV uses pres excluding 30 as well as 18, 0
  have gs1 : ∀ k : Nat, 1974 ≤ k → k < 1986 →
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres1 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hm := wn_mov_IDX_T_1974 (s := s1) hs1pc hs1h hs1Z gs1
  have hrun5 : runN s 5 = runN s1 4 := runN_add_eq s 1 4 5 (by decide)
  let s5 := runN s 5
  have hrun5_s : s5 = _ := hrun5
  have hs5pc : s5.pc = 1986 := by rw [hrun5_s]; exact hm.1
  have hs5h : s5.halted = false := by rw [hrun5_s]; exact hm.2.1
  have hs5T : s5.mem.get 18 = (0 : Word) := by
    rw [hrun5_s, hm.2.2.1, hI1]
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun5_s]; exact hm.2.2.2.1
  have hpres5mov := hm.2.2.2.2.2
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hrun5_s]
    exact (hpres5mov a ha18 ha0).trans (hpres1 a ha30 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 0 := (hpres5 29 (by decide) (by decide) (by decide)).trans hI
  have hCH5 : s5.mem.get 30 = 0 := by
    rw [hrun5_s]
    exact (hpres5mov 30 (by decide) (by decide)).trans hs1CH

  have gs5 : ∀ k : Nat, 1986 ≤ k → k < 1989 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres5 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc := wn_enc_jlez_1986 (s := s5) hs5pc gs5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj :=
    step_JLEZ (s := s5) (x := 18) (dest := 2076)
      hs5h hpc5 hs5Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = true := by
    have : le0 (s5.mem.get 18) = true := by
      rw [hs5T]; exact le0_zero
    simpa [le0] using this
  have hs6step : step s5 = { s5 with pc := 2076 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (2076 : Word) else s5.pc + 3) = (2076 : Word) := by
      simp [hle]
    rw [hj, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hrun6_s : s6 = _ := hrun6
  have hs6eq : s6 = { s5 with pc := 2076 } := by
    have : s6 = step s5 := hrun6
    rw [this, hs6step]
  have hsDpc : s6.pc = 2076 := by rw [hs6eq]
  have hsDh : s6.halted = false := by rw [hs6eq]; exact hs5h
  have hsDZ : s6.mem.get 0 = 0 := by rw [hs6eq]; exact hs5Z
  have hCHD : s6.mem.get 30 = 0 := by rw [hs6eq]; exact hCH5
  have hID : s6.mem.get 29 = 0 := by rw [hs6eq]; exact hI5
  have hpresD : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs6eq]; exact hpres5 a ha18 ha30 ha0
  have gsD : ∀ k : Nat, 2076 ≤ k → k < 2088 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpresD (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hm2 := wn_mov_CH_BUF0_2076 (s := s6) hsDpc hsDh hsDZ gsD
  have hrun10 : runN s 10 = runN s6 4 := runN_add_eq s 6 4 10 (by decide)
  let s10 := runN s 10
  have hrun10_s : s10 = _ := hrun10
  have hs10pc : s10.pc = 2088 := by rw [hrun10_s]; exact hm2.1
  have hs10h : s10.halted = false := by rw [hrun10_s]; exact hm2.2.1
  have hs10B : s10.mem.get 32 = 0 := by
    rw [hrun10_s, hm2.2.2.1, hCHD]
  have hs10Z : s10.mem.get 0 = 0 := by rw [hrun10_s]; exact hm2.2.2.2.1
  have hpres10mov := hm2.2.2.2.2.2
  have hpres10 : ∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hrun10_s]
    exact (hpres10mov a haB ha0).trans (hpresD a ha18 ha30 ha0)
  have hI10 : s10.mem.get 29 = 0 := (hpres10 29 (by decide) (by decide) (by decide) (by decide)).trans hI
  have hCH10 : s10.mem.get 30 = 0 := by
    rw [hrun10_s]
    exact (hpres10mov 30 (by decide) (by decide)).trans hCHD
  have gs10 : ∀ k : Nat, 2088 ≤ k → k < 2091 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n32 n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hencJ := wn_enc_jmp_2088 (s := s10) hs10pc gs10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hj3 :=
    step_JMP (s := s10) (dest := 2316)
      hs10h hpc10 hs10Z hencJ.1 hencJ.2.1 hencJ.2.2
  have hrunN : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
  have hsNeq : sN = step s10 := hrunN.trans (runN_one s10 hs10h hpc10)
  have hsNpc : sN.pc = 2316 := by rw [hsNeq, hj3]
  have hsNh : sN.halted = false := by rw [hsNeq, hj3]; exact hs10h
  have hsNZ : sN.mem.get 0 = 0 := by rw [hsNeq, hj3]; exact hs10Z
  have hsNB : sN.mem.get 32 = 0 := by rw [hsNeq, hj3]; exact hs10B
  have hsNI : sN.mem.get 29 = 0 := by rw [hsNeq, hj3]; exact hI10
  have hsNCH : sN.mem.get 30 = 0 := by rw [hsNeq, hj3]; exact hCH10
  have hpres : ∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsNeq, hj3]; exact hpres10 a haB ha18 ha30 ha0
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hsNCH, hpres⟩


/-- `WRITE_NUL` with `IDX = 1`: 13 steps, write `0` at `BUF+1`, pc = `DONE`. -/
theorem write_nul_idx1 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 1)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2316 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 13
    sN.pc = 2316 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 33 = 0 ∧
    sN.mem.get 29 = 1 ∧
    sN.mem.get 30 = 0 ∧
    (∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hz := wn_zero_CH_1971 (s := s) hpc hh
    (fun k h1 h2 => hcode k h1 (by omega))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hrun1 : runN s 1 = step s := runN_one s hh hpc0
  let s1 := runN s 1
  have hrun1_s : s1 = _ := hrun1
  have hs1eq : s1 = { s with mem := s.mem.set 30 0, pc := 1974 } := by
    have : s1 = step s := hrun1
    rw [this, hz]
  have hs1pc : s1.pc = 1974 := by rw [hs1eq]
  have hs1h : s1.halted = false := by rw [hs1eq]; exact hh
  have hs1Z : s1.mem.get 0 = 0 := by
    rw [hs1eq]
    exact (Mem.get_set_ne s.mem 30 0 0 (by decide)).trans hZ
  have hs1CH : s1.mem.get 30 = 0 := by rw [hs1eq, Mem.get_set_eq]
  have hpres1 : ∀ a, a ≠ 30 → a ≠ 0 → s1.mem.get a = s.mem.get a := by
    intro a ha30 ha0
    rw [hs1eq]
    exact Mem.get_set_ne s.mem 30 a 0 ha30
  have hONE1 : s1.mem.get 3 = 1 := (hpres1 3 (by decide) (by decide)).trans hONE
  have hI1 : s1.mem.get 29 = 1 := (hpres1 29 (by decide) (by decide)).trans hI
  -- g for MOV uses pres excluding 30 as well as 18, 0
  have gs1 : ∀ k : Nat, 1974 ≤ k → k < 1986 →
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres1 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hm := wn_mov_IDX_T_1974 (s := s1) hs1pc hs1h hs1Z gs1
  have hrun5 : runN s 5 = runN s1 4 := runN_add_eq s 1 4 5 (by decide)
  let s5 := runN s 5
  have hrun5_s : s5 = _ := hrun5
  have hs5pc : s5.pc = 1986 := by rw [hrun5_s]; exact hm.1
  have hs5h : s5.halted = false := by rw [hrun5_s]; exact hm.2.1
  have hs5T : s5.mem.get 18 = (1 : Word) := by
    rw [hrun5_s, hm.2.2.1, hI1]
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun5_s]; exact hm.2.2.2.1
  have hpres5mov := hm.2.2.2.2.2
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hrun5_s]
    exact (hpres5mov a ha18 ha0).trans (hpres1 a ha30 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 1 := (hpres5 29 (by decide) (by decide) (by decide)).trans hI
  have hCH5 : s5.mem.get 30 = 0 := by
    rw [hrun5_s]
    exact (hpres5mov 30 (by decide) (by decide)).trans hs1CH

  have gs5 : ∀ k : Nat, 1986 ≤ k → k < 1989 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres5 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc0 := wn_enc_jlez_1986 (s := s5) hs5pc gs5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj0 :=
    step_JLEZ (s := s5) (x := 18) (dest := 2076)
      hs5h hpc5 hs5Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = false := by
    have : le0 (s5.mem.get 18) = false := by
      rw [hs5T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs6step : step s5 = { s5 with pc := s5.pc + 3 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (2076 : Word) else s5.pc + 3) = s5.pc + 3 := by
      simp [hle0]
    rw [hj0, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hrun6_s : s6 = _ := hrun6
  have hs6eq : s6 = { s5 with pc := 1989 } := by
    have : s6 = step s5 := hrun6
    have hp3 : s5.pc + 3 = (1989 : Word) := by simp [hs5pc]
    rw [this, hs6step, hp3]
  have hs6pc : s6.pc = 1989 := by rw [hs6eq]
  have hs6h : s6.halted = false := by rw [hs6eq]; exact hs5h
  have hs6T : s6.mem.get 18 = (1 : Word) := by rw [hs6eq]; exact hs5T
  have hs6Z : s6.mem.get 0 = 0 := by rw [hs6eq]; exact hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs6eq]; exact hpres5 a ha18 ha30 ha0
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide) (by decide)).trans hONE
  have hI6 : s6.mem.get 29 = 1 := (hpres6 29 (by decide) (by decide) (by decide)).trans hI
  have hCH6 : s6.mem.get 30 = 0 := by rw [hs6eq]; exact hCH5

  have gs6dec : ∀ k : Nat, 1989 ≤ k → k < 1992 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres6 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec1 := wn_dec_T_1989 (s := s6) hs6pc hs6h
    (fun k h1 h2 => gs6dec k h1 (by omega))
  have hrun7 : runN s 7 = step s6 := by
    have hmid : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    have hpcp : s6.pc.toNat < 32768 := by simp [hs6pc]
    exact hmid.trans (runN_one s6 hs6h hpcp)
  let s7 := runN s 7
  have hrun7_s : s7 = _ := hrun7
  have hs7eq' : s7 =
      { s6 with mem := s6.mem.set 18 (s6.mem.get 18 - s6.mem.get 3), pc := 1992 } := by
    have : s7 = step s6 := hrun7
    rw [this, hdec1]
  have hs7pc : s7.pc = 1992 := by rw [hs7eq']
  have hs7h : s7.halted = false := by rw [hs7eq']; exact hs6h
  have hs7T : s7.mem.get 18 = (0 : Word) := by
    rw [hs7eq', Mem.get_set_eq, hs6T, hONE6]
    rfl
  have hs7Z : s7.mem.get 0 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 0 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hs6Z
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 a (s6.mem.get 18 - s6.mem.get 3) ha18).trans
      (hpres6 a ha18 ha30 ha0)
  have hONE7 : s7.mem.get 3 = 1 := (hpres7 3 (by decide) (by decide) (by decide)).trans hONE
  have hI7 : s7.mem.get 29 = 1 := (hpres7 29 (by decide) (by decide) (by decide)).trans hI
  have hCH7 : s7.mem.get 30 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 30 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hCH6
  have gs7 : ∀ k : Nat, 1992 ≤ k → k < 1992+3 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres7 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc1 := wn_enc_jlez_1992 (s := s7) hs7pc gs7
  have hpc7 : s7.pc.toNat < 32768 := by simp [hs7pc]
  have hj1 :=
    step_JLEZ (s := s7) (x := 18) (dest := 2091)
      hs7h hpc7 hs7Z henc1.1 henc1.2.1 henc1.2.2 (by decide)

  have hle1 : (s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18) = true := by
    have : le0 (s7.mem.get 18) = true := by
      rw [hs7T]; exact le0_zero
    simpa [le0] using this
  have hs8step : step s7 = { s7 with pc := 2091 } := by
    have hif :
        (if s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18
          then (2091 : Word) else s7.pc + 3) = (2091 : Word) := by
      simp [hle1]
    rw [hj1, hif]
  have hrun8 : runN s 8 = step s7 := by
    have hn : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hn.trans (runN_one s7 hs7h hpc7)
  let s8 := runN s 8
  have hrun8_s : s8 = _ := hrun8
  have hs8eq : s8 = { s7 with pc := 2091 } := by
    have : s8 = step s7 := hrun8
    rw [this, hs8step]
  have hsDpc : s8.pc = 2091 := by rw [hs8eq]
  have hsDh : s8.halted = false := by rw [hs8eq]; exact hs7h
  have hsDZ : s8.mem.get 0 = 0 := by rw [hs8eq]; exact hs7Z
  have hCHD : s8.mem.get 30 = 0 := by rw [hs8eq]; exact hCH7
  have hID : s8.mem.get 29 = 1 := by rw [hs8eq]; exact hI7
  have hpresD : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs8eq]; exact hpres7 a ha18 ha30 ha0

  have gsD : ∀ k : Nat, 2091 ≤ k → k < 2103 →
      s8.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpresD (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hm2 := wn_mov_CH_BUF1_2091 (s := s8) hsDpc hsDh hsDZ gsD
  have hrun12 : runN s 12 = runN s8 4 := runN_add_eq s 8 4 12 (by decide)
  let s12 := runN s 12
  have hrun12_s : s12 = _ := hrun12
  have hs12pc : s12.pc = 2103 := by rw [hrun12_s]; exact hm2.1
  have hs12h : s12.halted = false := by rw [hrun12_s]; exact hm2.2.1
  have hs12B : s12.mem.get 33 = 0 := by
    rw [hrun12_s, hm2.2.2.1, hCHD]
  have hs12Z : s12.mem.get 0 = 0 := by rw [hrun12_s]; exact hm2.2.2.2.1
  have hpres12mov := hm2.2.2.2.2.2
  have hpres12 : ∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hrun12_s]
    exact (hpres12mov a haB ha0).trans (hpresD a ha18 ha30 ha0)
  have hI12 : s12.mem.get 29 = 1 := (hpres12 29 (by decide) (by decide) (by decide) (by decide)).trans hI
  have hCH12 : s12.mem.get 30 = 0 := by
    rw [hrun12_s]
    exact (hpres12mov 30 (by decide) (by decide)).trans hCHD
  have gs12 : ∀ k : Nat, 2103 ≤ k → k < 2103+3 →
      s12.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres12 (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hencJ := wn_enc_jmp_2103 (s := s12) hs12pc gs12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hj3 :=
    step_JMP (s := s12) (dest := 2316)
      hs12h hpc12 hs12Z hencJ.1 hencJ.2.1 hencJ.2.2
  have hrunN : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
  have hsNeq : sN = step s12 := hrunN.trans (runN_one s12 hs12h hpc12)
  have hsNpc : sN.pc = 2316 := by rw [hsNeq, hj3]
  have hsNh : sN.halted = false := by rw [hsNeq, hj3]; exact hs12h
  have hsNZ : sN.mem.get 0 = 0 := by rw [hsNeq, hj3]; exact hs12Z
  have hsNB : sN.mem.get 33 = 0 := by rw [hsNeq, hj3]; exact hs12B
  have hsNI : sN.mem.get 29 = 1 := by rw [hsNeq, hj3]; exact hI12
  have hsNCH : sN.mem.get 30 = 0 := by rw [hsNeq, hj3]; exact hCH12
  have hpres : ∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsNeq, hj3]; exact hpres12 a haB ha18 ha30 ha0
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hsNCH, hpres⟩


/-- `WRITE_NUL` with `IDX = 2`: 15 steps, write `0` at `BUF+2`, pc = `DONE`. -/
theorem write_nul_idx2 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 2)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2316 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 15
    sN.pc = 2316 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 34 = 0 ∧
    sN.mem.get 29 = 2 ∧
    sN.mem.get 30 = 0 ∧
    (∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hz := wn_zero_CH_1971 (s := s) hpc hh
    (fun k h1 h2 => hcode k h1 (by omega))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hrun1 : runN s 1 = step s := runN_one s hh hpc0
  let s1 := runN s 1
  have hrun1_s : s1 = _ := hrun1
  have hs1eq : s1 = { s with mem := s.mem.set 30 0, pc := 1974 } := by
    have : s1 = step s := hrun1
    rw [this, hz]
  have hs1pc : s1.pc = 1974 := by rw [hs1eq]
  have hs1h : s1.halted = false := by rw [hs1eq]; exact hh
  have hs1Z : s1.mem.get 0 = 0 := by
    rw [hs1eq]
    exact (Mem.get_set_ne s.mem 30 0 0 (by decide)).trans hZ
  have hs1CH : s1.mem.get 30 = 0 := by rw [hs1eq, Mem.get_set_eq]
  have hpres1 : ∀ a, a ≠ 30 → a ≠ 0 → s1.mem.get a = s.mem.get a := by
    intro a ha30 ha0
    rw [hs1eq]
    exact Mem.get_set_ne s.mem 30 a 0 ha30
  have hONE1 : s1.mem.get 3 = 1 := (hpres1 3 (by decide) (by decide)).trans hONE
  have hI1 : s1.mem.get 29 = 2 := (hpres1 29 (by decide) (by decide)).trans hI
  -- g for MOV uses pres excluding 30 as well as 18, 0
  have gs1 : ∀ k : Nat, 1974 ≤ k → k < 1986 →
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres1 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hm := wn_mov_IDX_T_1974 (s := s1) hs1pc hs1h hs1Z gs1
  have hrun5 : runN s 5 = runN s1 4 := runN_add_eq s 1 4 5 (by decide)
  let s5 := runN s 5
  have hrun5_s : s5 = _ := hrun5
  have hs5pc : s5.pc = 1986 := by rw [hrun5_s]; exact hm.1
  have hs5h : s5.halted = false := by rw [hrun5_s]; exact hm.2.1
  have hs5T : s5.mem.get 18 = (2 : Word) := by
    rw [hrun5_s, hm.2.2.1, hI1]
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun5_s]; exact hm.2.2.2.1
  have hpres5mov := hm.2.2.2.2.2
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hrun5_s]
    exact (hpres5mov a ha18 ha0).trans (hpres1 a ha30 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 2 := (hpres5 29 (by decide) (by decide) (by decide)).trans hI
  have hCH5 : s5.mem.get 30 = 0 := by
    rw [hrun5_s]
    exact (hpres5mov 30 (by decide) (by decide)).trans hs1CH

  have gs5 : ∀ k : Nat, 1986 ≤ k → k < 1989 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres5 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc0 := wn_enc_jlez_1986 (s := s5) hs5pc gs5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj0 :=
    step_JLEZ (s := s5) (x := 18) (dest := 2076)
      hs5h hpc5 hs5Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = false := by
    have : le0 (s5.mem.get 18) = false := by
      rw [hs5T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs6step : step s5 = { s5 with pc := s5.pc + 3 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (2076 : Word) else s5.pc + 3) = s5.pc + 3 := by
      simp [hle0]
    rw [hj0, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hrun6_s : s6 = _ := hrun6
  have hs6eq : s6 = { s5 with pc := 1989 } := by
    have : s6 = step s5 := hrun6
    have hp3 : s5.pc + 3 = (1989 : Word) := by simp [hs5pc]
    rw [this, hs6step, hp3]
  have hs6pc : s6.pc = 1989 := by rw [hs6eq]
  have hs6h : s6.halted = false := by rw [hs6eq]; exact hs5h
  have hs6T : s6.mem.get 18 = (2 : Word) := by rw [hs6eq]; exact hs5T
  have hs6Z : s6.mem.get 0 = 0 := by rw [hs6eq]; exact hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs6eq]; exact hpres5 a ha18 ha30 ha0
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide) (by decide)).trans hONE
  have hI6 : s6.mem.get 29 = 2 := (hpres6 29 (by decide) (by decide) (by decide)).trans hI
  have hCH6 : s6.mem.get 30 = 0 := by rw [hs6eq]; exact hCH5

  have gs6dec : ∀ k : Nat, 1989 ≤ k → k < 1992 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres6 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec1 := wn_dec_T_1989 (s := s6) hs6pc hs6h
    (fun k h1 h2 => gs6dec k h1 (by omega))
  have hrun7 : runN s 7 = step s6 := by
    have hmid : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    have hpcp : s6.pc.toNat < 32768 := by simp [hs6pc]
    exact hmid.trans (runN_one s6 hs6h hpcp)
  let s7 := runN s 7
  have hrun7_s : s7 = _ := hrun7
  have hs7eq' : s7 =
      { s6 with mem := s6.mem.set 18 (s6.mem.get 18 - s6.mem.get 3), pc := 1992 } := by
    have : s7 = step s6 := hrun7
    rw [this, hdec1]
  have hs7pc : s7.pc = 1992 := by rw [hs7eq']
  have hs7h : s7.halted = false := by rw [hs7eq']; exact hs6h
  have hs7T : s7.mem.get 18 = (1 : Word) := by
    rw [hs7eq', Mem.get_set_eq, hs6T, hONE6]
    rfl
  have hs7Z : s7.mem.get 0 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 0 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hs6Z
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 a (s6.mem.get 18 - s6.mem.get 3) ha18).trans
      (hpres6 a ha18 ha30 ha0)
  have hONE7 : s7.mem.get 3 = 1 := (hpres7 3 (by decide) (by decide) (by decide)).trans hONE
  have hI7 : s7.mem.get 29 = 2 := (hpres7 29 (by decide) (by decide) (by decide)).trans hI
  have hCH7 : s7.mem.get 30 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 30 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hCH6
  have gs7 : ∀ k : Nat, 1992 ≤ k → k < 1992+3 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres7 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc1 := wn_enc_jlez_1992 (s := s7) hs7pc gs7
  have hpc7 : s7.pc.toNat < 32768 := by simp [hs7pc]
  have hj1 :=
    step_JLEZ (s := s7) (x := 18) (dest := 2091)
      hs7h hpc7 hs7Z henc1.1 henc1.2.1 henc1.2.2 (by decide)

  have hle1 : (s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18) = false := by
    have : le0 (s7.mem.get 18) = false := by
      rw [hs7T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs8step : step s7 = { s7 with pc := s7.pc + 3 } := by
    have hif :
        (if s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18
          then (2091 : Word) else s7.pc + 3) = s7.pc + 3 := by
      simp [hle1]
    rw [hj1, hif]
  have hrun8 : runN s 8 = step s7 := by
    have hn : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hn.trans (runN_one s7 hs7h hpc7)
  let s8 := runN s 8
  have hrun8_s : s8 = _ := hrun8
  have hs8eq : s8 = { s7 with pc := 1995 } := by
    have : s8 = step s7 := hrun8
    have hp3 : s7.pc + 3 = (1995 : Word) := by simp [hs7pc]
    rw [this, hs8step, hp3]
  have hs8pc : s8.pc = 1995 := by rw [hs8eq]
  have hs8h : s8.halted = false := by rw [hs8eq]; exact hs7h
  have hs8T : s8.mem.get 18 = (1 : Word) := by rw [hs8eq]; exact hs7T
  have hs8Z : s8.mem.get 0 = 0 := by rw [hs8eq]; exact hs7Z
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs8eq]; exact hpres7 a ha18 ha30 ha0
  have hONE8 : s8.mem.get 3 = 1 := (hpres8 3 (by decide) (by decide) (by decide)).trans hONE
  have hI8 : s8.mem.get 29 = 2 := (hpres8 29 (by decide) (by decide) (by decide)).trans hI
  have hCH8 : s8.mem.get 30 = 0 := by rw [hs8eq]; exact hCH7

  have gs8dec : ∀ k : Nat, 1995 ≤ k → k < 1998 →
      s8.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres8 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec2 := wn_dec_T_1995 (s := s8) hs8pc hs8h
    (fun k h1 h2 => gs8dec k h1 (by omega))
  have hrun9 : runN s 9 = step s8 := by
    have hmid : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    have hpcp : s8.pc.toNat < 32768 := by simp [hs8pc]
    exact hmid.trans (runN_one s8 hs8h hpcp)
  let s9 := runN s 9
  have hrun9_s : s9 = _ := hrun9
  have hs9eq' : s9 =
      { s8 with mem := s8.mem.set 18 (s8.mem.get 18 - s8.mem.get 3), pc := 1998 } := by
    have : s9 = step s8 := hrun9
    rw [this, hdec2]
  have hs9pc : s9.pc = 1998 := by rw [hs9eq']
  have hs9h : s9.halted = false := by rw [hs9eq']; exact hs8h
  have hs9T : s9.mem.get 18 = (0 : Word) := by
    rw [hs9eq', Mem.get_set_eq, hs8T, hONE8]
    rfl
  have hs9Z : s9.mem.get 0 = 0 := by
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 0 (s8.mem.get 18 - s8.mem.get 3) (by decide)).trans hs8Z
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 a (s8.mem.get 18 - s8.mem.get 3) ha18).trans
      (hpres8 a ha18 ha30 ha0)
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide) (by decide)).trans hONE
  have hI9 : s9.mem.get 29 = 2 := (hpres9 29 (by decide) (by decide) (by decide)).trans hI
  have hCH9 : s9.mem.get 30 = 0 := by
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 30 (s8.mem.get 18 - s8.mem.get 3) (by decide)).trans hCH8
  have gs9 : ∀ k : Nat, 1998 ≤ k → k < 1998+3 →
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
  have henc2 := wn_enc_jlez_1998 (s := s9) hs9pc gs9
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hj2 :=
    step_JLEZ (s := s9) (x := 18) (dest := 2106)
      hs9h hpc9 hs9Z henc2.1 henc2.2.1 henc2.2.2 (by decide)

  have hle2 : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = true := by
    have : le0 (s9.mem.get 18) = true := by
      rw [hs9T]; exact le0_zero
    simpa [le0] using this
  have hs10step : step s9 = { s9 with pc := 2106 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18
          then (2106 : Word) else s9.pc + 3) = (2106 : Word) := by
      simp [hle2]
    rw [hj2, hif]
  have hrun10 : runN s 10 = step s9 := by
    have hn : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hn.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hrun10_s : s10 = _ := hrun10
  have hs10eq : s10 = { s9 with pc := 2106 } := by
    have : s10 = step s9 := hrun10
    rw [this, hs10step]
  have hsDpc : s10.pc = 2106 := by rw [hs10eq]
  have hsDh : s10.halted = false := by rw [hs10eq]; exact hs9h
  have hsDZ : s10.mem.get 0 = 0 := by rw [hs10eq]; exact hs9Z
  have hCHD : s10.mem.get 30 = 0 := by rw [hs10eq]; exact hCH9
  have hID : s10.mem.get 29 = 2 := by rw [hs10eq]; exact hI9
  have hpresD : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs10eq]; exact hpres9 a ha18 ha30 ha0

  have gsD : ∀ k : Nat, 2106 ≤ k → k < 2118 →
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
    exact (hpresD (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hm2 := wn_mov_CH_BUF2_2106 (s := s10) hsDpc hsDh hsDZ gsD
  have hrun14 : runN s 14 = runN s10 4 := runN_add_eq s 10 4 14 (by decide)
  let s14 := runN s 14
  have hrun14_s : s14 = _ := hrun14
  have hs14pc : s14.pc = 2118 := by rw [hrun14_s]; exact hm2.1
  have hs14h : s14.halted = false := by rw [hrun14_s]; exact hm2.2.1
  have hs14B : s14.mem.get 34 = 0 := by
    rw [hrun14_s, hm2.2.2.1, hCHD]
  have hs14Z : s14.mem.get 0 = 0 := by rw [hrun14_s]; exact hm2.2.2.2.1
  have hpres14mov := hm2.2.2.2.2.2
  have hpres14 : ∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hrun14_s]
    exact (hpres14mov a haB ha0).trans (hpresD a ha18 ha30 ha0)
  have hI14 : s14.mem.get 29 = 2 := (hpres14 29 (by decide) (by decide) (by decide) (by decide)).trans hI
  have hCH14 : s14.mem.get 30 = 0 := by
    rw [hrun14_s]
    exact (hpres14mov 30 (by decide) (by decide)).trans hCHD
  have gs14 : ∀ k : Nat, 2118 ≤ k → k < 2118+3 →
      s14.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres14 (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hencJ := wn_enc_jmp_2118 (s := s14) hs14pc gs14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hj3 :=
    step_JMP (s := s14) (dest := 2316)
      hs14h hpc14 hs14Z hencJ.1 hencJ.2.1 hencJ.2.2
  have hrunN : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
  have hsNeq : sN = step s14 := hrunN.trans (runN_one s14 hs14h hpc14)
  have hsNpc : sN.pc = 2316 := by rw [hsNeq, hj3]
  have hsNh : sN.halted = false := by rw [hsNeq, hj3]; exact hs14h
  have hsNZ : sN.mem.get 0 = 0 := by rw [hsNeq, hj3]; exact hs14Z
  have hsNB : sN.mem.get 34 = 0 := by rw [hsNeq, hj3]; exact hs14B
  have hsNI : sN.mem.get 29 = 2 := by rw [hsNeq, hj3]; exact hI14
  have hsNCH : sN.mem.get 30 = 0 := by rw [hsNeq, hj3]; exact hCH14
  have hpres : ∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsNeq, hj3]; exact hpres14 a haB ha18 ha30 ha0
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hsNCH, hpres⟩


/-- `WRITE_NUL` with `IDX = 3`: 17 steps, write `0` at `BUF+3`, pc = `DONE`. -/
theorem write_nul_idx3 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 3)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2316 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 17
    sN.pc = 2316 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 35 = 0 ∧
    sN.mem.get 29 = 3 ∧
    sN.mem.get 30 = 0 ∧
    (∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hz := wn_zero_CH_1971 (s := s) hpc hh
    (fun k h1 h2 => hcode k h1 (by omega))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hrun1 : runN s 1 = step s := runN_one s hh hpc0
  let s1 := runN s 1
  have hrun1_s : s1 = _ := hrun1
  have hs1eq : s1 = { s with mem := s.mem.set 30 0, pc := 1974 } := by
    have : s1 = step s := hrun1
    rw [this, hz]
  have hs1pc : s1.pc = 1974 := by rw [hs1eq]
  have hs1h : s1.halted = false := by rw [hs1eq]; exact hh
  have hs1Z : s1.mem.get 0 = 0 := by
    rw [hs1eq]
    exact (Mem.get_set_ne s.mem 30 0 0 (by decide)).trans hZ
  have hs1CH : s1.mem.get 30 = 0 := by rw [hs1eq, Mem.get_set_eq]
  have hpres1 : ∀ a, a ≠ 30 → a ≠ 0 → s1.mem.get a = s.mem.get a := by
    intro a ha30 ha0
    rw [hs1eq]
    exact Mem.get_set_ne s.mem 30 a 0 ha30
  have hONE1 : s1.mem.get 3 = 1 := (hpres1 3 (by decide) (by decide)).trans hONE
  have hI1 : s1.mem.get 29 = 3 := (hpres1 29 (by decide) (by decide)).trans hI
  -- g for MOV uses pres excluding 30 as well as 18, 0
  have gs1 : ∀ k : Nat, 1974 ≤ k → k < 1986 →
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres1 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hm := wn_mov_IDX_T_1974 (s := s1) hs1pc hs1h hs1Z gs1
  have hrun5 : runN s 5 = runN s1 4 := runN_add_eq s 1 4 5 (by decide)
  let s5 := runN s 5
  have hrun5_s : s5 = _ := hrun5
  have hs5pc : s5.pc = 1986 := by rw [hrun5_s]; exact hm.1
  have hs5h : s5.halted = false := by rw [hrun5_s]; exact hm.2.1
  have hs5T : s5.mem.get 18 = (3 : Word) := by
    rw [hrun5_s, hm.2.2.1, hI1]
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun5_s]; exact hm.2.2.2.1
  have hpres5mov := hm.2.2.2.2.2
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hrun5_s]
    exact (hpres5mov a ha18 ha0).trans (hpres1 a ha30 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 3 := (hpres5 29 (by decide) (by decide) (by decide)).trans hI
  have hCH5 : s5.mem.get 30 = 0 := by
    rw [hrun5_s]
    exact (hpres5mov 30 (by decide) (by decide)).trans hs1CH

  have gs5 : ∀ k : Nat, 1986 ≤ k → k < 1989 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres5 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc0 := wn_enc_jlez_1986 (s := s5) hs5pc gs5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj0 :=
    step_JLEZ (s := s5) (x := 18) (dest := 2076)
      hs5h hpc5 hs5Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = false := by
    have : le0 (s5.mem.get 18) = false := by
      rw [hs5T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs6step : step s5 = { s5 with pc := s5.pc + 3 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (2076 : Word) else s5.pc + 3) = s5.pc + 3 := by
      simp [hle0]
    rw [hj0, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hrun6_s : s6 = _ := hrun6
  have hs6eq : s6 = { s5 with pc := 1989 } := by
    have : s6 = step s5 := hrun6
    have hp3 : s5.pc + 3 = (1989 : Word) := by simp [hs5pc]
    rw [this, hs6step, hp3]
  have hs6pc : s6.pc = 1989 := by rw [hs6eq]
  have hs6h : s6.halted = false := by rw [hs6eq]; exact hs5h
  have hs6T : s6.mem.get 18 = (3 : Word) := by rw [hs6eq]; exact hs5T
  have hs6Z : s6.mem.get 0 = 0 := by rw [hs6eq]; exact hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs6eq]; exact hpres5 a ha18 ha30 ha0
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide) (by decide)).trans hONE
  have hI6 : s6.mem.get 29 = 3 := (hpres6 29 (by decide) (by decide) (by decide)).trans hI
  have hCH6 : s6.mem.get 30 = 0 := by rw [hs6eq]; exact hCH5

  have gs6dec : ∀ k : Nat, 1989 ≤ k → k < 1992 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres6 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec1 := wn_dec_T_1989 (s := s6) hs6pc hs6h
    (fun k h1 h2 => gs6dec k h1 (by omega))
  have hrun7 : runN s 7 = step s6 := by
    have hmid : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    have hpcp : s6.pc.toNat < 32768 := by simp [hs6pc]
    exact hmid.trans (runN_one s6 hs6h hpcp)
  let s7 := runN s 7
  have hrun7_s : s7 = _ := hrun7
  have hs7eq' : s7 =
      { s6 with mem := s6.mem.set 18 (s6.mem.get 18 - s6.mem.get 3), pc := 1992 } := by
    have : s7 = step s6 := hrun7
    rw [this, hdec1]
  have hs7pc : s7.pc = 1992 := by rw [hs7eq']
  have hs7h : s7.halted = false := by rw [hs7eq']; exact hs6h
  have hs7T : s7.mem.get 18 = (2 : Word) := by
    rw [hs7eq', Mem.get_set_eq, hs6T, hONE6]
    rfl
  have hs7Z : s7.mem.get 0 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 0 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hs6Z
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 a (s6.mem.get 18 - s6.mem.get 3) ha18).trans
      (hpres6 a ha18 ha30 ha0)
  have hONE7 : s7.mem.get 3 = 1 := (hpres7 3 (by decide) (by decide) (by decide)).trans hONE
  have hI7 : s7.mem.get 29 = 3 := (hpres7 29 (by decide) (by decide) (by decide)).trans hI
  have hCH7 : s7.mem.get 30 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 30 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hCH6
  have gs7 : ∀ k : Nat, 1992 ≤ k → k < 1992+3 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres7 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc1 := wn_enc_jlez_1992 (s := s7) hs7pc gs7
  have hpc7 : s7.pc.toNat < 32768 := by simp [hs7pc]
  have hj1 :=
    step_JLEZ (s := s7) (x := 18) (dest := 2091)
      hs7h hpc7 hs7Z henc1.1 henc1.2.1 henc1.2.2 (by decide)

  have hle1 : (s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18) = false := by
    have : le0 (s7.mem.get 18) = false := by
      rw [hs7T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs8step : step s7 = { s7 with pc := s7.pc + 3 } := by
    have hif :
        (if s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18
          then (2091 : Word) else s7.pc + 3) = s7.pc + 3 := by
      simp [hle1]
    rw [hj1, hif]
  have hrun8 : runN s 8 = step s7 := by
    have hn : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hn.trans (runN_one s7 hs7h hpc7)
  let s8 := runN s 8
  have hrun8_s : s8 = _ := hrun8
  have hs8eq : s8 = { s7 with pc := 1995 } := by
    have : s8 = step s7 := hrun8
    have hp3 : s7.pc + 3 = (1995 : Word) := by simp [hs7pc]
    rw [this, hs8step, hp3]
  have hs8pc : s8.pc = 1995 := by rw [hs8eq]
  have hs8h : s8.halted = false := by rw [hs8eq]; exact hs7h
  have hs8T : s8.mem.get 18 = (2 : Word) := by rw [hs8eq]; exact hs7T
  have hs8Z : s8.mem.get 0 = 0 := by rw [hs8eq]; exact hs7Z
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs8eq]; exact hpres7 a ha18 ha30 ha0
  have hONE8 : s8.mem.get 3 = 1 := (hpres8 3 (by decide) (by decide) (by decide)).trans hONE
  have hI8 : s8.mem.get 29 = 3 := (hpres8 29 (by decide) (by decide) (by decide)).trans hI
  have hCH8 : s8.mem.get 30 = 0 := by rw [hs8eq]; exact hCH7

  have gs8dec : ∀ k : Nat, 1995 ≤ k → k < 1998 →
      s8.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres8 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec2 := wn_dec_T_1995 (s := s8) hs8pc hs8h
    (fun k h1 h2 => gs8dec k h1 (by omega))
  have hrun9 : runN s 9 = step s8 := by
    have hmid : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    have hpcp : s8.pc.toNat < 32768 := by simp [hs8pc]
    exact hmid.trans (runN_one s8 hs8h hpcp)
  let s9 := runN s 9
  have hrun9_s : s9 = _ := hrun9
  have hs9eq' : s9 =
      { s8 with mem := s8.mem.set 18 (s8.mem.get 18 - s8.mem.get 3), pc := 1998 } := by
    have : s9 = step s8 := hrun9
    rw [this, hdec2]
  have hs9pc : s9.pc = 1998 := by rw [hs9eq']
  have hs9h : s9.halted = false := by rw [hs9eq']; exact hs8h
  have hs9T : s9.mem.get 18 = (1 : Word) := by
    rw [hs9eq', Mem.get_set_eq, hs8T, hONE8]
    rfl
  have hs9Z : s9.mem.get 0 = 0 := by
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 0 (s8.mem.get 18 - s8.mem.get 3) (by decide)).trans hs8Z
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 a (s8.mem.get 18 - s8.mem.get 3) ha18).trans
      (hpres8 a ha18 ha30 ha0)
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide) (by decide)).trans hONE
  have hI9 : s9.mem.get 29 = 3 := (hpres9 29 (by decide) (by decide) (by decide)).trans hI
  have hCH9 : s9.mem.get 30 = 0 := by
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 30 (s8.mem.get 18 - s8.mem.get 3) (by decide)).trans hCH8
  have gs9 : ∀ k : Nat, 1998 ≤ k → k < 1998+3 →
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
  have henc2 := wn_enc_jlez_1998 (s := s9) hs9pc gs9
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hj2 :=
    step_JLEZ (s := s9) (x := 18) (dest := 2106)
      hs9h hpc9 hs9Z henc2.1 henc2.2.1 henc2.2.2 (by decide)

  have hle2 : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = false := by
    have : le0 (s9.mem.get 18) = false := by
      rw [hs9T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs10step : step s9 = { s9 with pc := s9.pc + 3 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18
          then (2106 : Word) else s9.pc + 3) = s9.pc + 3 := by
      simp [hle2]
    rw [hj2, hif]
  have hrun10 : runN s 10 = step s9 := by
    have hn : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hn.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hrun10_s : s10 = _ := hrun10
  have hs10eq : s10 = { s9 with pc := 2001 } := by
    have : s10 = step s9 := hrun10
    have hp3 : s9.pc + 3 = (2001 : Word) := by simp [hs9pc]
    rw [this, hs10step, hp3]
  have hs10pc : s10.pc = 2001 := by rw [hs10eq]
  have hs10h : s10.halted = false := by rw [hs10eq]; exact hs9h
  have hs10T : s10.mem.get 18 = (1 : Word) := by rw [hs10eq]; exact hs9T
  have hs10Z : s10.mem.get 0 = 0 := by rw [hs10eq]; exact hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs10eq]; exact hpres9 a ha18 ha30 ha0
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide) (by decide)).trans hONE
  have hI10 : s10.mem.get 29 = 3 := (hpres10 29 (by decide) (by decide) (by decide)).trans hI
  have hCH10 : s10.mem.get 30 = 0 := by rw [hs10eq]; exact hCH9

  have gs10dec : ∀ k : Nat, 2001 ≤ k → k < 2004 →
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
    exact (hpres10 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec3 := wn_dec_T_2001 (s := s10) hs10pc hs10h
    (fun k h1 h2 => gs10dec k h1 (by omega))
  have hrun11 : runN s 11 = step s10 := by
    have hmid : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    have hpcp : s10.pc.toNat < 32768 := by simp [hs10pc]
    exact hmid.trans (runN_one s10 hs10h hpcp)
  let s11 := runN s 11
  have hrun11_s : s11 = _ := hrun11
  have hs11eq' : s11 =
      { s10 with mem := s10.mem.set 18 (s10.mem.get 18 - s10.mem.get 3), pc := 2004 } := by
    have : s11 = step s10 := hrun11
    rw [this, hdec3]
  have hs11pc : s11.pc = 2004 := by rw [hs11eq']
  have hs11h : s11.halted = false := by rw [hs11eq']; exact hs10h
  have hs11T : s11.mem.get 18 = (0 : Word) := by
    rw [hs11eq', Mem.get_set_eq, hs10T, hONE10]
    rfl
  have hs11Z : s11.mem.get 0 = 0 := by
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 0 (s10.mem.get 18 - s10.mem.get 3) (by decide)).trans hs10Z
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 a (s10.mem.get 18 - s10.mem.get 3) ha18).trans
      (hpres10 a ha18 ha30 ha0)
  have hONE11 : s11.mem.get 3 = 1 := (hpres11 3 (by decide) (by decide) (by decide)).trans hONE
  have hI11 : s11.mem.get 29 = 3 := (hpres11 29 (by decide) (by decide) (by decide)).trans hI
  have hCH11 : s11.mem.get 30 = 0 := by
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 30 (s10.mem.get 18 - s10.mem.get 3) (by decide)).trans hCH10
  have gs11 : ∀ k : Nat, 2004 ≤ k → k < 2004+3 →
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
  have henc3 := wn_enc_jlez_2004 (s := s11) hs11pc gs11
  have hpc11 : s11.pc.toNat < 32768 := by simp [hs11pc]
  have hj3 :=
    step_JLEZ (s := s11) (x := 18) (dest := 2121)
      hs11h hpc11 hs11Z henc3.1 henc3.2.1 henc3.2.2 (by decide)

  have hle3 : (s11.mem.get 18 = 0 || 0x8000 ≤ s11.mem.get 18) = true := by
    have : le0 (s11.mem.get 18) = true := by
      rw [hs11T]; exact le0_zero
    simpa [le0] using this
  have hs12step : step s11 = { s11 with pc := 2121 } := by
    have hif :
        (if s11.mem.get 18 = 0 || 0x8000 ≤ s11.mem.get 18
          then (2121 : Word) else s11.pc + 3) = (2121 : Word) := by
      simp [hle3]
    rw [hj3, hif]
  have hrun12 : runN s 12 = step s11 := by
    have hn : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hn.trans (runN_one s11 hs11h hpc11)
  let s12 := runN s 12
  have hrun12_s : s12 = _ := hrun12
  have hs12eq : s12 = { s11 with pc := 2121 } := by
    have : s12 = step s11 := hrun12
    rw [this, hs12step]
  have hsDpc : s12.pc = 2121 := by rw [hs12eq]
  have hsDh : s12.halted = false := by rw [hs12eq]; exact hs11h
  have hsDZ : s12.mem.get 0 = 0 := by rw [hs12eq]; exact hs11Z
  have hCHD : s12.mem.get 30 = 0 := by rw [hs12eq]; exact hCH11
  have hID : s12.mem.get 29 = 3 := by rw [hs12eq]; exact hI11
  have hpresD : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs12eq]; exact hpres11 a ha18 ha30 ha0

  have gsD : ∀ k : Nat, 2121 ≤ k → k < 2133 →
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
    exact (hpresD (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hm2 := wn_mov_CH_BUF3_2121 (s := s12) hsDpc hsDh hsDZ gsD
  have hrun16 : runN s 16 = runN s12 4 := runN_add_eq s 12 4 16 (by decide)
  let s16 := runN s 16
  have hrun16_s : s16 = _ := hrun16
  have hs16pc : s16.pc = 2133 := by rw [hrun16_s]; exact hm2.1
  have hs16h : s16.halted = false := by rw [hrun16_s]; exact hm2.2.1
  have hs16B : s16.mem.get 35 = 0 := by
    rw [hrun16_s, hm2.2.2.1, hCHD]
  have hs16Z : s16.mem.get 0 = 0 := by rw [hrun16_s]; exact hm2.2.2.2.1
  have hpres16mov := hm2.2.2.2.2.2
  have hpres16 : ∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hrun16_s]
    exact (hpres16mov a haB ha0).trans (hpresD a ha18 ha30 ha0)
  have hI16 : s16.mem.get 29 = 3 := (hpres16 29 (by decide) (by decide) (by decide) (by decide)).trans hI
  have hCH16 : s16.mem.get 30 = 0 := by
    rw [hrun16_s]
    exact (hpres16mov 30 (by decide) (by decide)).trans hCHD
  have gs16 : ∀ k : Nat, 2133 ≤ k → k < 2133+3 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hencJ := wn_enc_jmp_2133 (s := s16) hs16pc gs16
  have hpc16 : s16.pc.toNat < 32768 := by simp [hs16pc]
  have hj3 :=
    step_JMP (s := s16) (dest := 2316)
      hs16h hpc16 hs16Z hencJ.1 hencJ.2.1 hencJ.2.2
  have hrunN : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
  have hsNeq : sN = step s16 := hrunN.trans (runN_one s16 hs16h hpc16)
  have hsNpc : sN.pc = 2316 := by rw [hsNeq, hj3]
  have hsNh : sN.halted = false := by rw [hsNeq, hj3]; exact hs16h
  have hsNZ : sN.mem.get 0 = 0 := by rw [hsNeq, hj3]; exact hs16Z
  have hsNB : sN.mem.get 35 = 0 := by rw [hsNeq, hj3]; exact hs16B
  have hsNI : sN.mem.get 29 = 3 := by rw [hsNeq, hj3]; exact hI16
  have hsNCH : sN.mem.get 30 = 0 := by rw [hsNeq, hj3]; exact hCH16
  have hpres : ∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsNeq, hj3]; exact hpres16 a haB ha18 ha30 ha0
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hsNCH, hpres⟩


/-- `WRITE_NUL` with `IDX = 4`: 19 steps, write `0` at `BUF+4`, pc = `DONE`. -/
theorem write_nul_idx4 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 4)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2316 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 19
    sN.pc = 2316 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 36 = 0 ∧
    sN.mem.get 29 = 4 ∧
    sN.mem.get 30 = 0 ∧
    (∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hz := wn_zero_CH_1971 (s := s) hpc hh
    (fun k h1 h2 => hcode k h1 (by omega))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hrun1 : runN s 1 = step s := runN_one s hh hpc0
  let s1 := runN s 1
  have hrun1_s : s1 = _ := hrun1
  have hs1eq : s1 = { s with mem := s.mem.set 30 0, pc := 1974 } := by
    have : s1 = step s := hrun1
    rw [this, hz]
  have hs1pc : s1.pc = 1974 := by rw [hs1eq]
  have hs1h : s1.halted = false := by rw [hs1eq]; exact hh
  have hs1Z : s1.mem.get 0 = 0 := by
    rw [hs1eq]
    exact (Mem.get_set_ne s.mem 30 0 0 (by decide)).trans hZ
  have hs1CH : s1.mem.get 30 = 0 := by rw [hs1eq, Mem.get_set_eq]
  have hpres1 : ∀ a, a ≠ 30 → a ≠ 0 → s1.mem.get a = s.mem.get a := by
    intro a ha30 ha0
    rw [hs1eq]
    exact Mem.get_set_ne s.mem 30 a 0 ha30
  have hONE1 : s1.mem.get 3 = 1 := (hpres1 3 (by decide) (by decide)).trans hONE
  have hI1 : s1.mem.get 29 = 4 := (hpres1 29 (by decide) (by decide)).trans hI
  -- g for MOV uses pres excluding 30 as well as 18, 0
  have gs1 : ∀ k : Nat, 1974 ≤ k → k < 1986 →
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres1 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hm := wn_mov_IDX_T_1974 (s := s1) hs1pc hs1h hs1Z gs1
  have hrun5 : runN s 5 = runN s1 4 := runN_add_eq s 1 4 5 (by decide)
  let s5 := runN s 5
  have hrun5_s : s5 = _ := hrun5
  have hs5pc : s5.pc = 1986 := by rw [hrun5_s]; exact hm.1
  have hs5h : s5.halted = false := by rw [hrun5_s]; exact hm.2.1
  have hs5T : s5.mem.get 18 = (4 : Word) := by
    rw [hrun5_s, hm.2.2.1, hI1]
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun5_s]; exact hm.2.2.2.1
  have hpres5mov := hm.2.2.2.2.2
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hrun5_s]
    exact (hpres5mov a ha18 ha0).trans (hpres1 a ha30 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 4 := (hpres5 29 (by decide) (by decide) (by decide)).trans hI
  have hCH5 : s5.mem.get 30 = 0 := by
    rw [hrun5_s]
    exact (hpres5mov 30 (by decide) (by decide)).trans hs1CH

  have gs5 : ∀ k : Nat, 1986 ≤ k → k < 1989 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres5 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc0 := wn_enc_jlez_1986 (s := s5) hs5pc gs5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj0 :=
    step_JLEZ (s := s5) (x := 18) (dest := 2076)
      hs5h hpc5 hs5Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = false := by
    have : le0 (s5.mem.get 18) = false := by
      rw [hs5T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs6step : step s5 = { s5 with pc := s5.pc + 3 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (2076 : Word) else s5.pc + 3) = s5.pc + 3 := by
      simp [hle0]
    rw [hj0, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hrun6_s : s6 = _ := hrun6
  have hs6eq : s6 = { s5 with pc := 1989 } := by
    have : s6 = step s5 := hrun6
    have hp3 : s5.pc + 3 = (1989 : Word) := by simp [hs5pc]
    rw [this, hs6step, hp3]
  have hs6pc : s6.pc = 1989 := by rw [hs6eq]
  have hs6h : s6.halted = false := by rw [hs6eq]; exact hs5h
  have hs6T : s6.mem.get 18 = (4 : Word) := by rw [hs6eq]; exact hs5T
  have hs6Z : s6.mem.get 0 = 0 := by rw [hs6eq]; exact hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs6eq]; exact hpres5 a ha18 ha30 ha0
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide) (by decide)).trans hONE
  have hI6 : s6.mem.get 29 = 4 := (hpres6 29 (by decide) (by decide) (by decide)).trans hI
  have hCH6 : s6.mem.get 30 = 0 := by rw [hs6eq]; exact hCH5

  have gs6dec : ∀ k : Nat, 1989 ≤ k → k < 1992 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres6 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec1 := wn_dec_T_1989 (s := s6) hs6pc hs6h
    (fun k h1 h2 => gs6dec k h1 (by omega))
  have hrun7 : runN s 7 = step s6 := by
    have hmid : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    have hpcp : s6.pc.toNat < 32768 := by simp [hs6pc]
    exact hmid.trans (runN_one s6 hs6h hpcp)
  let s7 := runN s 7
  have hrun7_s : s7 = _ := hrun7
  have hs7eq' : s7 =
      { s6 with mem := s6.mem.set 18 (s6.mem.get 18 - s6.mem.get 3), pc := 1992 } := by
    have : s7 = step s6 := hrun7
    rw [this, hdec1]
  have hs7pc : s7.pc = 1992 := by rw [hs7eq']
  have hs7h : s7.halted = false := by rw [hs7eq']; exact hs6h
  have hs7T : s7.mem.get 18 = (3 : Word) := by
    rw [hs7eq', Mem.get_set_eq, hs6T, hONE6]
    rfl
  have hs7Z : s7.mem.get 0 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 0 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hs6Z
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 a (s6.mem.get 18 - s6.mem.get 3) ha18).trans
      (hpres6 a ha18 ha30 ha0)
  have hONE7 : s7.mem.get 3 = 1 := (hpres7 3 (by decide) (by decide) (by decide)).trans hONE
  have hI7 : s7.mem.get 29 = 4 := (hpres7 29 (by decide) (by decide) (by decide)).trans hI
  have hCH7 : s7.mem.get 30 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 30 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hCH6
  have gs7 : ∀ k : Nat, 1992 ≤ k → k < 1992+3 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres7 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc1 := wn_enc_jlez_1992 (s := s7) hs7pc gs7
  have hpc7 : s7.pc.toNat < 32768 := by simp [hs7pc]
  have hj1 :=
    step_JLEZ (s := s7) (x := 18) (dest := 2091)
      hs7h hpc7 hs7Z henc1.1 henc1.2.1 henc1.2.2 (by decide)

  have hle1 : (s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18) = false := by
    have : le0 (s7.mem.get 18) = false := by
      rw [hs7T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs8step : step s7 = { s7 with pc := s7.pc + 3 } := by
    have hif :
        (if s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18
          then (2091 : Word) else s7.pc + 3) = s7.pc + 3 := by
      simp [hle1]
    rw [hj1, hif]
  have hrun8 : runN s 8 = step s7 := by
    have hn : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hn.trans (runN_one s7 hs7h hpc7)
  let s8 := runN s 8
  have hrun8_s : s8 = _ := hrun8
  have hs8eq : s8 = { s7 with pc := 1995 } := by
    have : s8 = step s7 := hrun8
    have hp3 : s7.pc + 3 = (1995 : Word) := by simp [hs7pc]
    rw [this, hs8step, hp3]
  have hs8pc : s8.pc = 1995 := by rw [hs8eq]
  have hs8h : s8.halted = false := by rw [hs8eq]; exact hs7h
  have hs8T : s8.mem.get 18 = (3 : Word) := by rw [hs8eq]; exact hs7T
  have hs8Z : s8.mem.get 0 = 0 := by rw [hs8eq]; exact hs7Z
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs8eq]; exact hpres7 a ha18 ha30 ha0
  have hONE8 : s8.mem.get 3 = 1 := (hpres8 3 (by decide) (by decide) (by decide)).trans hONE
  have hI8 : s8.mem.get 29 = 4 := (hpres8 29 (by decide) (by decide) (by decide)).trans hI
  have hCH8 : s8.mem.get 30 = 0 := by rw [hs8eq]; exact hCH7

  have gs8dec : ∀ k : Nat, 1995 ≤ k → k < 1998 →
      s8.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres8 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec2 := wn_dec_T_1995 (s := s8) hs8pc hs8h
    (fun k h1 h2 => gs8dec k h1 (by omega))
  have hrun9 : runN s 9 = step s8 := by
    have hmid : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    have hpcp : s8.pc.toNat < 32768 := by simp [hs8pc]
    exact hmid.trans (runN_one s8 hs8h hpcp)
  let s9 := runN s 9
  have hrun9_s : s9 = _ := hrun9
  have hs9eq' : s9 =
      { s8 with mem := s8.mem.set 18 (s8.mem.get 18 - s8.mem.get 3), pc := 1998 } := by
    have : s9 = step s8 := hrun9
    rw [this, hdec2]
  have hs9pc : s9.pc = 1998 := by rw [hs9eq']
  have hs9h : s9.halted = false := by rw [hs9eq']; exact hs8h
  have hs9T : s9.mem.get 18 = (2 : Word) := by
    rw [hs9eq', Mem.get_set_eq, hs8T, hONE8]
    rfl
  have hs9Z : s9.mem.get 0 = 0 := by
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 0 (s8.mem.get 18 - s8.mem.get 3) (by decide)).trans hs8Z
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 a (s8.mem.get 18 - s8.mem.get 3) ha18).trans
      (hpres8 a ha18 ha30 ha0)
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide) (by decide)).trans hONE
  have hI9 : s9.mem.get 29 = 4 := (hpres9 29 (by decide) (by decide) (by decide)).trans hI
  have hCH9 : s9.mem.get 30 = 0 := by
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 30 (s8.mem.get 18 - s8.mem.get 3) (by decide)).trans hCH8
  have gs9 : ∀ k : Nat, 1998 ≤ k → k < 1998+3 →
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
  have henc2 := wn_enc_jlez_1998 (s := s9) hs9pc gs9
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hj2 :=
    step_JLEZ (s := s9) (x := 18) (dest := 2106)
      hs9h hpc9 hs9Z henc2.1 henc2.2.1 henc2.2.2 (by decide)

  have hle2 : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = false := by
    have : le0 (s9.mem.get 18) = false := by
      rw [hs9T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs10step : step s9 = { s9 with pc := s9.pc + 3 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18
          then (2106 : Word) else s9.pc + 3) = s9.pc + 3 := by
      simp [hle2]
    rw [hj2, hif]
  have hrun10 : runN s 10 = step s9 := by
    have hn : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hn.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hrun10_s : s10 = _ := hrun10
  have hs10eq : s10 = { s9 with pc := 2001 } := by
    have : s10 = step s9 := hrun10
    have hp3 : s9.pc + 3 = (2001 : Word) := by simp [hs9pc]
    rw [this, hs10step, hp3]
  have hs10pc : s10.pc = 2001 := by rw [hs10eq]
  have hs10h : s10.halted = false := by rw [hs10eq]; exact hs9h
  have hs10T : s10.mem.get 18 = (2 : Word) := by rw [hs10eq]; exact hs9T
  have hs10Z : s10.mem.get 0 = 0 := by rw [hs10eq]; exact hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs10eq]; exact hpres9 a ha18 ha30 ha0
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide) (by decide)).trans hONE
  have hI10 : s10.mem.get 29 = 4 := (hpres10 29 (by decide) (by decide) (by decide)).trans hI
  have hCH10 : s10.mem.get 30 = 0 := by rw [hs10eq]; exact hCH9

  have gs10dec : ∀ k : Nat, 2001 ≤ k → k < 2004 →
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
    exact (hpres10 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec3 := wn_dec_T_2001 (s := s10) hs10pc hs10h
    (fun k h1 h2 => gs10dec k h1 (by omega))
  have hrun11 : runN s 11 = step s10 := by
    have hmid : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    have hpcp : s10.pc.toNat < 32768 := by simp [hs10pc]
    exact hmid.trans (runN_one s10 hs10h hpcp)
  let s11 := runN s 11
  have hrun11_s : s11 = _ := hrun11
  have hs11eq' : s11 =
      { s10 with mem := s10.mem.set 18 (s10.mem.get 18 - s10.mem.get 3), pc := 2004 } := by
    have : s11 = step s10 := hrun11
    rw [this, hdec3]
  have hs11pc : s11.pc = 2004 := by rw [hs11eq']
  have hs11h : s11.halted = false := by rw [hs11eq']; exact hs10h
  have hs11T : s11.mem.get 18 = (1 : Word) := by
    rw [hs11eq', Mem.get_set_eq, hs10T, hONE10]
    rfl
  have hs11Z : s11.mem.get 0 = 0 := by
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 0 (s10.mem.get 18 - s10.mem.get 3) (by decide)).trans hs10Z
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 a (s10.mem.get 18 - s10.mem.get 3) ha18).trans
      (hpres10 a ha18 ha30 ha0)
  have hONE11 : s11.mem.get 3 = 1 := (hpres11 3 (by decide) (by decide) (by decide)).trans hONE
  have hI11 : s11.mem.get 29 = 4 := (hpres11 29 (by decide) (by decide) (by decide)).trans hI
  have hCH11 : s11.mem.get 30 = 0 := by
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 30 (s10.mem.get 18 - s10.mem.get 3) (by decide)).trans hCH10
  have gs11 : ∀ k : Nat, 2004 ≤ k → k < 2004+3 →
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
  have henc3 := wn_enc_jlez_2004 (s := s11) hs11pc gs11
  have hpc11 : s11.pc.toNat < 32768 := by simp [hs11pc]
  have hj3 :=
    step_JLEZ (s := s11) (x := 18) (dest := 2121)
      hs11h hpc11 hs11Z henc3.1 henc3.2.1 henc3.2.2 (by decide)

  have hle3 : (s11.mem.get 18 = 0 || 0x8000 ≤ s11.mem.get 18) = false := by
    have : le0 (s11.mem.get 18) = false := by
      rw [hs11T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs12step : step s11 = { s11 with pc := s11.pc + 3 } := by
    have hif :
        (if s11.mem.get 18 = 0 || 0x8000 ≤ s11.mem.get 18
          then (2121 : Word) else s11.pc + 3) = s11.pc + 3 := by
      simp [hle3]
    rw [hj3, hif]
  have hrun12 : runN s 12 = step s11 := by
    have hn : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hn.trans (runN_one s11 hs11h hpc11)
  let s12 := runN s 12
  have hrun12_s : s12 = _ := hrun12
  have hs12eq : s12 = { s11 with pc := 2007 } := by
    have : s12 = step s11 := hrun12
    have hp3 : s11.pc + 3 = (2007 : Word) := by simp [hs11pc]
    rw [this, hs12step, hp3]
  have hs12pc : s12.pc = 2007 := by rw [hs12eq]
  have hs12h : s12.halted = false := by rw [hs12eq]; exact hs11h
  have hs12T : s12.mem.get 18 = (1 : Word) := by rw [hs12eq]; exact hs11T
  have hs12Z : s12.mem.get 0 = 0 := by rw [hs12eq]; exact hs11Z
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs12eq]; exact hpres11 a ha18 ha30 ha0
  have hONE12 : s12.mem.get 3 = 1 := (hpres12 3 (by decide) (by decide) (by decide)).trans hONE
  have hI12 : s12.mem.get 29 = 4 := (hpres12 29 (by decide) (by decide) (by decide)).trans hI
  have hCH12 : s12.mem.get 30 = 0 := by rw [hs12eq]; exact hCH11

  have gs12dec : ∀ k : Nat, 2007 ≤ k → k < 2010 →
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
    exact (hpres12 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec4 := wn_dec_T_2007 (s := s12) hs12pc hs12h
    (fun k h1 h2 => gs12dec k h1 (by omega))
  have hrun13 : runN s 13 = step s12 := by
    have hmid : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    have hpcp : s12.pc.toNat < 32768 := by simp [hs12pc]
    exact hmid.trans (runN_one s12 hs12h hpcp)
  let s13 := runN s 13
  have hrun13_s : s13 = _ := hrun13
  have hs13eq' : s13 =
      { s12 with mem := s12.mem.set 18 (s12.mem.get 18 - s12.mem.get 3), pc := 2010 } := by
    have : s13 = step s12 := hrun13
    rw [this, hdec4]
  have hs13pc : s13.pc = 2010 := by rw [hs13eq']
  have hs13h : s13.halted = false := by rw [hs13eq']; exact hs12h
  have hs13T : s13.mem.get 18 = (0 : Word) := by
    rw [hs13eq', Mem.get_set_eq, hs12T, hONE12]
    rfl
  have hs13Z : s13.mem.get 0 = 0 := by
    rw [hs13eq']
    exact (Mem.get_set_ne s12.mem 18 0 (s12.mem.get 18 - s12.mem.get 3) (by decide)).trans hs12Z
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs13eq']
    exact (Mem.get_set_ne s12.mem 18 a (s12.mem.get 18 - s12.mem.get 3) ha18).trans
      (hpres12 a ha18 ha30 ha0)
  have hONE13 : s13.mem.get 3 = 1 := (hpres13 3 (by decide) (by decide) (by decide)).trans hONE
  have hI13 : s13.mem.get 29 = 4 := (hpres13 29 (by decide) (by decide) (by decide)).trans hI
  have hCH13 : s13.mem.get 30 = 0 := by
    rw [hs13eq']
    exact (Mem.get_set_ne s12.mem 18 30 (s12.mem.get 18 - s12.mem.get 3) (by decide)).trans hCH12
  have gs13 : ∀ k : Nat, 2010 ≤ k → k < 2010+3 →
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
  have henc4 := wn_enc_jlez_2010 (s := s13) hs13pc gs13
  have hpc13 : s13.pc.toNat < 32768 := by simp [hs13pc]
  have hj4 :=
    step_JLEZ (s := s13) (x := 18) (dest := 2136)
      hs13h hpc13 hs13Z henc4.1 henc4.2.1 henc4.2.2 (by decide)

  have hle4 : (s13.mem.get 18 = 0 || 0x8000 ≤ s13.mem.get 18) = true := by
    have : le0 (s13.mem.get 18) = true := by
      rw [hs13T]; exact le0_zero
    simpa [le0] using this
  have hs14step : step s13 = { s13 with pc := 2136 } := by
    have hif :
        (if s13.mem.get 18 = 0 || 0x8000 ≤ s13.mem.get 18
          then (2136 : Word) else s13.pc + 3) = (2136 : Word) := by
      simp [hle4]
    rw [hj4, hif]
  have hrun14 : runN s 14 = step s13 := by
    have hn : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hn.trans (runN_one s13 hs13h hpc13)
  let s14 := runN s 14
  have hrun14_s : s14 = _ := hrun14
  have hs14eq : s14 = { s13 with pc := 2136 } := by
    have : s14 = step s13 := hrun14
    rw [this, hs14step]
  have hsDpc : s14.pc = 2136 := by rw [hs14eq]
  have hsDh : s14.halted = false := by rw [hs14eq]; exact hs13h
  have hsDZ : s14.mem.get 0 = 0 := by rw [hs14eq]; exact hs13Z
  have hCHD : s14.mem.get 30 = 0 := by rw [hs14eq]; exact hCH13
  have hID : s14.mem.get 29 = 4 := by rw [hs14eq]; exact hI13
  have hpresD : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs14eq]; exact hpres13 a ha18 ha30 ha0

  have gsD : ∀ k : Nat, 2136 ≤ k → k < 2148 →
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
    exact (hpresD (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hm2 := wn_mov_CH_BUF4_2136 (s := s14) hsDpc hsDh hsDZ gsD
  have hrun18 : runN s 18 = runN s14 4 := runN_add_eq s 14 4 18 (by decide)
  let s18 := runN s 18
  have hrun18_s : s18 = _ := hrun18
  have hs18pc : s18.pc = 2148 := by rw [hrun18_s]; exact hm2.1
  have hs18h : s18.halted = false := by rw [hrun18_s]; exact hm2.2.1
  have hs18B : s18.mem.get 36 = 0 := by
    rw [hrun18_s, hm2.2.2.1, hCHD]
  have hs18Z : s18.mem.get 0 = 0 := by rw [hrun18_s]; exact hm2.2.2.2.1
  have hpres18mov := hm2.2.2.2.2.2
  have hpres18 : ∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hrun18_s]
    exact (hpres18mov a haB ha0).trans (hpresD a ha18 ha30 ha0)
  have hI18 : s18.mem.get 29 = 4 := (hpres18 29 (by decide) (by decide) (by decide) (by decide)).trans hI
  have hCH18 : s18.mem.get 30 = 0 := by
    rw [hrun18_s]
    exact (hpres18mov 30 (by decide) (by decide)).trans hCHD
  have gs18 : ∀ k : Nat, 2148 ≤ k → k < 2148+3 →
      s18.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres18 (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hencJ := wn_enc_jmp_2148 (s := s18) hs18pc gs18
  have hpc18 : s18.pc.toNat < 32768 := by simp [hs18pc]
  have hj3 :=
    step_JMP (s := s18) (dest := 2316)
      hs18h hpc18 hs18Z hencJ.1 hencJ.2.1 hencJ.2.2
  have hrunN : runN s 19 = runN s18 1 := runN_add_eq s 18 1 19 (by decide)
  have hsNeq : sN = step s18 := hrunN.trans (runN_one s18 hs18h hpc18)
  have hsNpc : sN.pc = 2316 := by rw [hsNeq, hj3]
  have hsNh : sN.halted = false := by rw [hsNeq, hj3]; exact hs18h
  have hsNZ : sN.mem.get 0 = 0 := by rw [hsNeq, hj3]; exact hs18Z
  have hsNB : sN.mem.get 36 = 0 := by rw [hsNeq, hj3]; exact hs18B
  have hsNI : sN.mem.get 29 = 4 := by rw [hsNeq, hj3]; exact hI18
  have hsNCH : sN.mem.get 30 = 0 := by rw [hsNeq, hj3]; exact hCH18
  have hpres : ∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsNeq, hj3]; exact hpres18 a haB ha18 ha30 ha0
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hsNCH, hpres⟩


/-- `WRITE_NUL` with `IDX = 5`: 21 steps, write `0` at `BUF+5`, pc = `DONE`. -/
theorem write_nul_idx5 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 5)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2316 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 21
    sN.pc = 2316 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 37 = 0 ∧
    sN.mem.get 29 = 5 ∧
    sN.mem.get 30 = 0 ∧
    (∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hz := wn_zero_CH_1971 (s := s) hpc hh
    (fun k h1 h2 => hcode k h1 (by omega))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hrun1 : runN s 1 = step s := runN_one s hh hpc0
  let s1 := runN s 1
  have hrun1_s : s1 = _ := hrun1
  have hs1eq : s1 = { s with mem := s.mem.set 30 0, pc := 1974 } := by
    have : s1 = step s := hrun1
    rw [this, hz]
  have hs1pc : s1.pc = 1974 := by rw [hs1eq]
  have hs1h : s1.halted = false := by rw [hs1eq]; exact hh
  have hs1Z : s1.mem.get 0 = 0 := by
    rw [hs1eq]
    exact (Mem.get_set_ne s.mem 30 0 0 (by decide)).trans hZ
  have hs1CH : s1.mem.get 30 = 0 := by rw [hs1eq, Mem.get_set_eq]
  have hpres1 : ∀ a, a ≠ 30 → a ≠ 0 → s1.mem.get a = s.mem.get a := by
    intro a ha30 ha0
    rw [hs1eq]
    exact Mem.get_set_ne s.mem 30 a 0 ha30
  have hONE1 : s1.mem.get 3 = 1 := (hpres1 3 (by decide) (by decide)).trans hONE
  have hI1 : s1.mem.get 29 = 5 := (hpres1 29 (by decide) (by decide)).trans hI
  -- g for MOV uses pres excluding 30 as well as 18, 0
  have gs1 : ∀ k : Nat, 1974 ≤ k → k < 1986 →
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres1 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hm := wn_mov_IDX_T_1974 (s := s1) hs1pc hs1h hs1Z gs1
  have hrun5 : runN s 5 = runN s1 4 := runN_add_eq s 1 4 5 (by decide)
  let s5 := runN s 5
  have hrun5_s : s5 = _ := hrun5
  have hs5pc : s5.pc = 1986 := by rw [hrun5_s]; exact hm.1
  have hs5h : s5.halted = false := by rw [hrun5_s]; exact hm.2.1
  have hs5T : s5.mem.get 18 = (5 : Word) := by
    rw [hrun5_s, hm.2.2.1, hI1]
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun5_s]; exact hm.2.2.2.1
  have hpres5mov := hm.2.2.2.2.2
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hrun5_s]
    exact (hpres5mov a ha18 ha0).trans (hpres1 a ha30 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 5 := (hpres5 29 (by decide) (by decide) (by decide)).trans hI
  have hCH5 : s5.mem.get 30 = 0 := by
    rw [hrun5_s]
    exact (hpres5mov 30 (by decide) (by decide)).trans hs1CH

  have gs5 : ∀ k : Nat, 1986 ≤ k → k < 1989 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres5 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc0 := wn_enc_jlez_1986 (s := s5) hs5pc gs5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj0 :=
    step_JLEZ (s := s5) (x := 18) (dest := 2076)
      hs5h hpc5 hs5Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = false := by
    have : le0 (s5.mem.get 18) = false := by
      rw [hs5T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs6step : step s5 = { s5 with pc := s5.pc + 3 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (2076 : Word) else s5.pc + 3) = s5.pc + 3 := by
      simp [hle0]
    rw [hj0, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hrun6_s : s6 = _ := hrun6
  have hs6eq : s6 = { s5 with pc := 1989 } := by
    have : s6 = step s5 := hrun6
    have hp3 : s5.pc + 3 = (1989 : Word) := by simp [hs5pc]
    rw [this, hs6step, hp3]
  have hs6pc : s6.pc = 1989 := by rw [hs6eq]
  have hs6h : s6.halted = false := by rw [hs6eq]; exact hs5h
  have hs6T : s6.mem.get 18 = (5 : Word) := by rw [hs6eq]; exact hs5T
  have hs6Z : s6.mem.get 0 = 0 := by rw [hs6eq]; exact hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs6eq]; exact hpres5 a ha18 ha30 ha0
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide) (by decide)).trans hONE
  have hI6 : s6.mem.get 29 = 5 := (hpres6 29 (by decide) (by decide) (by decide)).trans hI
  have hCH6 : s6.mem.get 30 = 0 := by rw [hs6eq]; exact hCH5

  have gs6dec : ∀ k : Nat, 1989 ≤ k → k < 1992 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres6 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec1 := wn_dec_T_1989 (s := s6) hs6pc hs6h
    (fun k h1 h2 => gs6dec k h1 (by omega))
  have hrun7 : runN s 7 = step s6 := by
    have hmid : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    have hpcp : s6.pc.toNat < 32768 := by simp [hs6pc]
    exact hmid.trans (runN_one s6 hs6h hpcp)
  let s7 := runN s 7
  have hrun7_s : s7 = _ := hrun7
  have hs7eq' : s7 =
      { s6 with mem := s6.mem.set 18 (s6.mem.get 18 - s6.mem.get 3), pc := 1992 } := by
    have : s7 = step s6 := hrun7
    rw [this, hdec1]
  have hs7pc : s7.pc = 1992 := by rw [hs7eq']
  have hs7h : s7.halted = false := by rw [hs7eq']; exact hs6h
  have hs7T : s7.mem.get 18 = (4 : Word) := by
    rw [hs7eq', Mem.get_set_eq, hs6T, hONE6]
    rfl
  have hs7Z : s7.mem.get 0 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 0 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hs6Z
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 a (s6.mem.get 18 - s6.mem.get 3) ha18).trans
      (hpres6 a ha18 ha30 ha0)
  have hONE7 : s7.mem.get 3 = 1 := (hpres7 3 (by decide) (by decide) (by decide)).trans hONE
  have hI7 : s7.mem.get 29 = 5 := (hpres7 29 (by decide) (by decide) (by decide)).trans hI
  have hCH7 : s7.mem.get 30 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 30 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hCH6
  have gs7 : ∀ k : Nat, 1992 ≤ k → k < 1992+3 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres7 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc1 := wn_enc_jlez_1992 (s := s7) hs7pc gs7
  have hpc7 : s7.pc.toNat < 32768 := by simp [hs7pc]
  have hj1 :=
    step_JLEZ (s := s7) (x := 18) (dest := 2091)
      hs7h hpc7 hs7Z henc1.1 henc1.2.1 henc1.2.2 (by decide)

  have hle1 : (s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18) = false := by
    have : le0 (s7.mem.get 18) = false := by
      rw [hs7T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs8step : step s7 = { s7 with pc := s7.pc + 3 } := by
    have hif :
        (if s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18
          then (2091 : Word) else s7.pc + 3) = s7.pc + 3 := by
      simp [hle1]
    rw [hj1, hif]
  have hrun8 : runN s 8 = step s7 := by
    have hn : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hn.trans (runN_one s7 hs7h hpc7)
  let s8 := runN s 8
  have hrun8_s : s8 = _ := hrun8
  have hs8eq : s8 = { s7 with pc := 1995 } := by
    have : s8 = step s7 := hrun8
    have hp3 : s7.pc + 3 = (1995 : Word) := by simp [hs7pc]
    rw [this, hs8step, hp3]
  have hs8pc : s8.pc = 1995 := by rw [hs8eq]
  have hs8h : s8.halted = false := by rw [hs8eq]; exact hs7h
  have hs8T : s8.mem.get 18 = (4 : Word) := by rw [hs8eq]; exact hs7T
  have hs8Z : s8.mem.get 0 = 0 := by rw [hs8eq]; exact hs7Z
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs8eq]; exact hpres7 a ha18 ha30 ha0
  have hONE8 : s8.mem.get 3 = 1 := (hpres8 3 (by decide) (by decide) (by decide)).trans hONE
  have hI8 : s8.mem.get 29 = 5 := (hpres8 29 (by decide) (by decide) (by decide)).trans hI
  have hCH8 : s8.mem.get 30 = 0 := by rw [hs8eq]; exact hCH7

  have gs8dec : ∀ k : Nat, 1995 ≤ k → k < 1998 →
      s8.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres8 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec2 := wn_dec_T_1995 (s := s8) hs8pc hs8h
    (fun k h1 h2 => gs8dec k h1 (by omega))
  have hrun9 : runN s 9 = step s8 := by
    have hmid : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    have hpcp : s8.pc.toNat < 32768 := by simp [hs8pc]
    exact hmid.trans (runN_one s8 hs8h hpcp)
  let s9 := runN s 9
  have hrun9_s : s9 = _ := hrun9
  have hs9eq' : s9 =
      { s8 with mem := s8.mem.set 18 (s8.mem.get 18 - s8.mem.get 3), pc := 1998 } := by
    have : s9 = step s8 := hrun9
    rw [this, hdec2]
  have hs9pc : s9.pc = 1998 := by rw [hs9eq']
  have hs9h : s9.halted = false := by rw [hs9eq']; exact hs8h
  have hs9T : s9.mem.get 18 = (3 : Word) := by
    rw [hs9eq', Mem.get_set_eq, hs8T, hONE8]
    rfl
  have hs9Z : s9.mem.get 0 = 0 := by
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 0 (s8.mem.get 18 - s8.mem.get 3) (by decide)).trans hs8Z
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 a (s8.mem.get 18 - s8.mem.get 3) ha18).trans
      (hpres8 a ha18 ha30 ha0)
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide) (by decide)).trans hONE
  have hI9 : s9.mem.get 29 = 5 := (hpres9 29 (by decide) (by decide) (by decide)).trans hI
  have hCH9 : s9.mem.get 30 = 0 := by
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 30 (s8.mem.get 18 - s8.mem.get 3) (by decide)).trans hCH8
  have gs9 : ∀ k : Nat, 1998 ≤ k → k < 1998+3 →
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
  have henc2 := wn_enc_jlez_1998 (s := s9) hs9pc gs9
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hj2 :=
    step_JLEZ (s := s9) (x := 18) (dest := 2106)
      hs9h hpc9 hs9Z henc2.1 henc2.2.1 henc2.2.2 (by decide)

  have hle2 : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = false := by
    have : le0 (s9.mem.get 18) = false := by
      rw [hs9T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs10step : step s9 = { s9 with pc := s9.pc + 3 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18
          then (2106 : Word) else s9.pc + 3) = s9.pc + 3 := by
      simp [hle2]
    rw [hj2, hif]
  have hrun10 : runN s 10 = step s9 := by
    have hn : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hn.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hrun10_s : s10 = _ := hrun10
  have hs10eq : s10 = { s9 with pc := 2001 } := by
    have : s10 = step s9 := hrun10
    have hp3 : s9.pc + 3 = (2001 : Word) := by simp [hs9pc]
    rw [this, hs10step, hp3]
  have hs10pc : s10.pc = 2001 := by rw [hs10eq]
  have hs10h : s10.halted = false := by rw [hs10eq]; exact hs9h
  have hs10T : s10.mem.get 18 = (3 : Word) := by rw [hs10eq]; exact hs9T
  have hs10Z : s10.mem.get 0 = 0 := by rw [hs10eq]; exact hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs10eq]; exact hpres9 a ha18 ha30 ha0
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide) (by decide)).trans hONE
  have hI10 : s10.mem.get 29 = 5 := (hpres10 29 (by decide) (by decide) (by decide)).trans hI
  have hCH10 : s10.mem.get 30 = 0 := by rw [hs10eq]; exact hCH9

  have gs10dec : ∀ k : Nat, 2001 ≤ k → k < 2004 →
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
    exact (hpres10 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec3 := wn_dec_T_2001 (s := s10) hs10pc hs10h
    (fun k h1 h2 => gs10dec k h1 (by omega))
  have hrun11 : runN s 11 = step s10 := by
    have hmid : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    have hpcp : s10.pc.toNat < 32768 := by simp [hs10pc]
    exact hmid.trans (runN_one s10 hs10h hpcp)
  let s11 := runN s 11
  have hrun11_s : s11 = _ := hrun11
  have hs11eq' : s11 =
      { s10 with mem := s10.mem.set 18 (s10.mem.get 18 - s10.mem.get 3), pc := 2004 } := by
    have : s11 = step s10 := hrun11
    rw [this, hdec3]
  have hs11pc : s11.pc = 2004 := by rw [hs11eq']
  have hs11h : s11.halted = false := by rw [hs11eq']; exact hs10h
  have hs11T : s11.mem.get 18 = (2 : Word) := by
    rw [hs11eq', Mem.get_set_eq, hs10T, hONE10]
    rfl
  have hs11Z : s11.mem.get 0 = 0 := by
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 0 (s10.mem.get 18 - s10.mem.get 3) (by decide)).trans hs10Z
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 a (s10.mem.get 18 - s10.mem.get 3) ha18).trans
      (hpres10 a ha18 ha30 ha0)
  have hONE11 : s11.mem.get 3 = 1 := (hpres11 3 (by decide) (by decide) (by decide)).trans hONE
  have hI11 : s11.mem.get 29 = 5 := (hpres11 29 (by decide) (by decide) (by decide)).trans hI
  have hCH11 : s11.mem.get 30 = 0 := by
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 30 (s10.mem.get 18 - s10.mem.get 3) (by decide)).trans hCH10
  have gs11 : ∀ k : Nat, 2004 ≤ k → k < 2004+3 →
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
  have henc3 := wn_enc_jlez_2004 (s := s11) hs11pc gs11
  have hpc11 : s11.pc.toNat < 32768 := by simp [hs11pc]
  have hj3 :=
    step_JLEZ (s := s11) (x := 18) (dest := 2121)
      hs11h hpc11 hs11Z henc3.1 henc3.2.1 henc3.2.2 (by decide)

  have hle3 : (s11.mem.get 18 = 0 || 0x8000 ≤ s11.mem.get 18) = false := by
    have : le0 (s11.mem.get 18) = false := by
      rw [hs11T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs12step : step s11 = { s11 with pc := s11.pc + 3 } := by
    have hif :
        (if s11.mem.get 18 = 0 || 0x8000 ≤ s11.mem.get 18
          then (2121 : Word) else s11.pc + 3) = s11.pc + 3 := by
      simp [hle3]
    rw [hj3, hif]
  have hrun12 : runN s 12 = step s11 := by
    have hn : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hn.trans (runN_one s11 hs11h hpc11)
  let s12 := runN s 12
  have hrun12_s : s12 = _ := hrun12
  have hs12eq : s12 = { s11 with pc := 2007 } := by
    have : s12 = step s11 := hrun12
    have hp3 : s11.pc + 3 = (2007 : Word) := by simp [hs11pc]
    rw [this, hs12step, hp3]
  have hs12pc : s12.pc = 2007 := by rw [hs12eq]
  have hs12h : s12.halted = false := by rw [hs12eq]; exact hs11h
  have hs12T : s12.mem.get 18 = (2 : Word) := by rw [hs12eq]; exact hs11T
  have hs12Z : s12.mem.get 0 = 0 := by rw [hs12eq]; exact hs11Z
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs12eq]; exact hpres11 a ha18 ha30 ha0
  have hONE12 : s12.mem.get 3 = 1 := (hpres12 3 (by decide) (by decide) (by decide)).trans hONE
  have hI12 : s12.mem.get 29 = 5 := (hpres12 29 (by decide) (by decide) (by decide)).trans hI
  have hCH12 : s12.mem.get 30 = 0 := by rw [hs12eq]; exact hCH11

  have gs12dec : ∀ k : Nat, 2007 ≤ k → k < 2010 →
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
    exact (hpres12 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec4 := wn_dec_T_2007 (s := s12) hs12pc hs12h
    (fun k h1 h2 => gs12dec k h1 (by omega))
  have hrun13 : runN s 13 = step s12 := by
    have hmid : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    have hpcp : s12.pc.toNat < 32768 := by simp [hs12pc]
    exact hmid.trans (runN_one s12 hs12h hpcp)
  let s13 := runN s 13
  have hrun13_s : s13 = _ := hrun13
  have hs13eq' : s13 =
      { s12 with mem := s12.mem.set 18 (s12.mem.get 18 - s12.mem.get 3), pc := 2010 } := by
    have : s13 = step s12 := hrun13
    rw [this, hdec4]
  have hs13pc : s13.pc = 2010 := by rw [hs13eq']
  have hs13h : s13.halted = false := by rw [hs13eq']; exact hs12h
  have hs13T : s13.mem.get 18 = (1 : Word) := by
    rw [hs13eq', Mem.get_set_eq, hs12T, hONE12]
    rfl
  have hs13Z : s13.mem.get 0 = 0 := by
    rw [hs13eq']
    exact (Mem.get_set_ne s12.mem 18 0 (s12.mem.get 18 - s12.mem.get 3) (by decide)).trans hs12Z
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs13eq']
    exact (Mem.get_set_ne s12.mem 18 a (s12.mem.get 18 - s12.mem.get 3) ha18).trans
      (hpres12 a ha18 ha30 ha0)
  have hONE13 : s13.mem.get 3 = 1 := (hpres13 3 (by decide) (by decide) (by decide)).trans hONE
  have hI13 : s13.mem.get 29 = 5 := (hpres13 29 (by decide) (by decide) (by decide)).trans hI
  have hCH13 : s13.mem.get 30 = 0 := by
    rw [hs13eq']
    exact (Mem.get_set_ne s12.mem 18 30 (s12.mem.get 18 - s12.mem.get 3) (by decide)).trans hCH12
  have gs13 : ∀ k : Nat, 2010 ≤ k → k < 2010+3 →
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
  have henc4 := wn_enc_jlez_2010 (s := s13) hs13pc gs13
  have hpc13 : s13.pc.toNat < 32768 := by simp [hs13pc]
  have hj4 :=
    step_JLEZ (s := s13) (x := 18) (dest := 2136)
      hs13h hpc13 hs13Z henc4.1 henc4.2.1 henc4.2.2 (by decide)

  have hle4 : (s13.mem.get 18 = 0 || 0x8000 ≤ s13.mem.get 18) = false := by
    have : le0 (s13.mem.get 18) = false := by
      rw [hs13T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs14step : step s13 = { s13 with pc := s13.pc + 3 } := by
    have hif :
        (if s13.mem.get 18 = 0 || 0x8000 ≤ s13.mem.get 18
          then (2136 : Word) else s13.pc + 3) = s13.pc + 3 := by
      simp [hle4]
    rw [hj4, hif]
  have hrun14 : runN s 14 = step s13 := by
    have hn : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hn.trans (runN_one s13 hs13h hpc13)
  let s14 := runN s 14
  have hrun14_s : s14 = _ := hrun14
  have hs14eq : s14 = { s13 with pc := 2013 } := by
    have : s14 = step s13 := hrun14
    have hp3 : s13.pc + 3 = (2013 : Word) := by simp [hs13pc]
    rw [this, hs14step, hp3]
  have hs14pc : s14.pc = 2013 := by rw [hs14eq]
  have hs14h : s14.halted = false := by rw [hs14eq]; exact hs13h
  have hs14T : s14.mem.get 18 = (1 : Word) := by rw [hs14eq]; exact hs13T
  have hs14Z : s14.mem.get 0 = 0 := by rw [hs14eq]; exact hs13Z
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs14eq]; exact hpres13 a ha18 ha30 ha0
  have hONE14 : s14.mem.get 3 = 1 := (hpres14 3 (by decide) (by decide) (by decide)).trans hONE
  have hI14 : s14.mem.get 29 = 5 := (hpres14 29 (by decide) (by decide) (by decide)).trans hI
  have hCH14 : s14.mem.get 30 = 0 := by rw [hs14eq]; exact hCH13

  have gs14dec : ∀ k : Nat, 2013 ≤ k → k < 2016 →
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
    exact (hpres14 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec5 := wn_dec_T_2013 (s := s14) hs14pc hs14h
    (fun k h1 h2 => gs14dec k h1 (by omega))
  have hrun15 : runN s 15 = step s14 := by
    have hmid : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    have hpcp : s14.pc.toNat < 32768 := by simp [hs14pc]
    exact hmid.trans (runN_one s14 hs14h hpcp)
  let s15 := runN s 15
  have hrun15_s : s15 = _ := hrun15
  have hs15eq' : s15 =
      { s14 with mem := s14.mem.set 18 (s14.mem.get 18 - s14.mem.get 3), pc := 2016 } := by
    have : s15 = step s14 := hrun15
    rw [this, hdec5]
  have hs15pc : s15.pc = 2016 := by rw [hs15eq']
  have hs15h : s15.halted = false := by rw [hs15eq']; exact hs14h
  have hs15T : s15.mem.get 18 = (0 : Word) := by
    rw [hs15eq', Mem.get_set_eq, hs14T, hONE14]
    rfl
  have hs15Z : s15.mem.get 0 = 0 := by
    rw [hs15eq']
    exact (Mem.get_set_ne s14.mem 18 0 (s14.mem.get 18 - s14.mem.get 3) (by decide)).trans hs14Z
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs15eq']
    exact (Mem.get_set_ne s14.mem 18 a (s14.mem.get 18 - s14.mem.get 3) ha18).trans
      (hpres14 a ha18 ha30 ha0)
  have hONE15 : s15.mem.get 3 = 1 := (hpres15 3 (by decide) (by decide) (by decide)).trans hONE
  have hI15 : s15.mem.get 29 = 5 := (hpres15 29 (by decide) (by decide) (by decide)).trans hI
  have hCH15 : s15.mem.get 30 = 0 := by
    rw [hs15eq']
    exact (Mem.get_set_ne s14.mem 18 30 (s14.mem.get 18 - s14.mem.get 3) (by decide)).trans hCH14
  have gs15 : ∀ k : Nat, 2016 ≤ k → k < 2016+3 →
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
  have henc5 := wn_enc_jlez_2016 (s := s15) hs15pc gs15
  have hpc15 : s15.pc.toNat < 32768 := by simp [hs15pc]
  have hj5 :=
    step_JLEZ (s := s15) (x := 18) (dest := 2151)
      hs15h hpc15 hs15Z henc5.1 henc5.2.1 henc5.2.2 (by decide)

  have hle5 : (s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18) = true := by
    have : le0 (s15.mem.get 18) = true := by
      rw [hs15T]; exact le0_zero
    simpa [le0] using this
  have hs16step : step s15 = { s15 with pc := 2151 } := by
    have hif :
        (if s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18
          then (2151 : Word) else s15.pc + 3) = (2151 : Word) := by
      simp [hle5]
    rw [hj5, hif]
  have hrun16 : runN s 16 = step s15 := by
    have hn : runN s 16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
    exact hn.trans (runN_one s15 hs15h hpc15)
  let s16 := runN s 16
  have hrun16_s : s16 = _ := hrun16
  have hs16eq : s16 = { s15 with pc := 2151 } := by
    have : s16 = step s15 := hrun16
    rw [this, hs16step]
  have hsDpc : s16.pc = 2151 := by rw [hs16eq]
  have hsDh : s16.halted = false := by rw [hs16eq]; exact hs15h
  have hsDZ : s16.mem.get 0 = 0 := by rw [hs16eq]; exact hs15Z
  have hCHD : s16.mem.get 30 = 0 := by rw [hs16eq]; exact hCH15
  have hID : s16.mem.get 29 = 5 := by rw [hs16eq]; exact hI15
  have hpresD : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs16eq]; exact hpres15 a ha18 ha30 ha0

  have gsD : ∀ k : Nat, 2151 ≤ k → k < 2163 →
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
    exact (hpresD (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hm2 := wn_mov_CH_BUF5_2151 (s := s16) hsDpc hsDh hsDZ gsD
  have hrun20 : runN s 20 = runN s16 4 := runN_add_eq s 16 4 20 (by decide)
  let s20 := runN s 20
  have hrun20_s : s20 = _ := hrun20
  have hs20pc : s20.pc = 2163 := by rw [hrun20_s]; exact hm2.1
  have hs20h : s20.halted = false := by rw [hrun20_s]; exact hm2.2.1
  have hs20B : s20.mem.get 37 = 0 := by
    rw [hrun20_s, hm2.2.2.1, hCHD]
  have hs20Z : s20.mem.get 0 = 0 := by rw [hrun20_s]; exact hm2.2.2.2.1
  have hpres20mov := hm2.2.2.2.2.2
  have hpres20 : ∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hrun20_s]
    exact (hpres20mov a haB ha0).trans (hpresD a ha18 ha30 ha0)
  have hI20 : s20.mem.get 29 = 5 := (hpres20 29 (by decide) (by decide) (by decide) (by decide)).trans hI
  have hCH20 : s20.mem.get 30 = 0 := by
    rw [hrun20_s]
    exact (hpres20mov 30 (by decide) (by decide)).trans hCHD
  have gs20 : ∀ k : Nat, 2163 ≤ k → k < 2163+3 →
      s20.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres20 (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hencJ := wn_enc_jmp_2163 (s := s20) hs20pc gs20
  have hpc20 : s20.pc.toNat < 32768 := by simp [hs20pc]
  have hj3 :=
    step_JMP (s := s20) (dest := 2316)
      hs20h hpc20 hs20Z hencJ.1 hencJ.2.1 hencJ.2.2
  have hrunN : runN s 21 = runN s20 1 := runN_add_eq s 20 1 21 (by decide)
  have hsNeq : sN = step s20 := hrunN.trans (runN_one s20 hs20h hpc20)
  have hsNpc : sN.pc = 2316 := by rw [hsNeq, hj3]
  have hsNh : sN.halted = false := by rw [hsNeq, hj3]; exact hs20h
  have hsNZ : sN.mem.get 0 = 0 := by rw [hsNeq, hj3]; exact hs20Z
  have hsNB : sN.mem.get 37 = 0 := by rw [hsNeq, hj3]; exact hs20B
  have hsNI : sN.mem.get 29 = 5 := by rw [hsNeq, hj3]; exact hI20
  have hsNCH : sN.mem.get 30 = 0 := by rw [hsNeq, hj3]; exact hCH20
  have hpres : ∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsNeq, hj3]; exact hpres20 a haB ha18 ha30 ha0
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hsNCH, hpres⟩


/-- `WRITE_NUL` with `IDX = 6`: 23 steps, write `0` at `BUF+6`, pc = `DONE`. -/
theorem write_nul_idx6 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 6)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2316 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 23
    sN.pc = 2316 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 38 = 0 ∧
    sN.mem.get 29 = 6 ∧
    sN.mem.get 30 = 0 ∧
    (∀ a, a ≠ 38 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hz := wn_zero_CH_1971 (s := s) hpc hh
    (fun k h1 h2 => hcode k h1 (by omega))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hrun1 : runN s 1 = step s := runN_one s hh hpc0
  let s1 := runN s 1
  have hrun1_s : s1 = _ := hrun1
  have hs1eq : s1 = { s with mem := s.mem.set 30 0, pc := 1974 } := by
    have : s1 = step s := hrun1
    rw [this, hz]
  have hs1pc : s1.pc = 1974 := by rw [hs1eq]
  have hs1h : s1.halted = false := by rw [hs1eq]; exact hh
  have hs1Z : s1.mem.get 0 = 0 := by
    rw [hs1eq]
    exact (Mem.get_set_ne s.mem 30 0 0 (by decide)).trans hZ
  have hs1CH : s1.mem.get 30 = 0 := by rw [hs1eq, Mem.get_set_eq]
  have hpres1 : ∀ a, a ≠ 30 → a ≠ 0 → s1.mem.get a = s.mem.get a := by
    intro a ha30 ha0
    rw [hs1eq]
    exact Mem.get_set_ne s.mem 30 a 0 ha30
  have hONE1 : s1.mem.get 3 = 1 := (hpres1 3 (by decide) (by decide)).trans hONE
  have hI1 : s1.mem.get 29 = 6 := (hpres1 29 (by decide) (by decide)).trans hI
  -- g for MOV uses pres excluding 30 as well as 18, 0
  have gs1 : ∀ k : Nat, 1974 ≤ k → k < 1986 →
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres1 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hm := wn_mov_IDX_T_1974 (s := s1) hs1pc hs1h hs1Z gs1
  have hrun5 : runN s 5 = runN s1 4 := runN_add_eq s 1 4 5 (by decide)
  let s5 := runN s 5
  have hrun5_s : s5 = _ := hrun5
  have hs5pc : s5.pc = 1986 := by rw [hrun5_s]; exact hm.1
  have hs5h : s5.halted = false := by rw [hrun5_s]; exact hm.2.1
  have hs5T : s5.mem.get 18 = (6 : Word) := by
    rw [hrun5_s, hm.2.2.1, hI1]
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun5_s]; exact hm.2.2.2.1
  have hpres5mov := hm.2.2.2.2.2
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hrun5_s]
    exact (hpres5mov a ha18 ha0).trans (hpres1 a ha30 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 6 := (hpres5 29 (by decide) (by decide) (by decide)).trans hI
  have hCH5 : s5.mem.get 30 = 0 := by
    rw [hrun5_s]
    exact (hpres5mov 30 (by decide) (by decide)).trans hs1CH

  have gs5 : ∀ k : Nat, 1986 ≤ k → k < 1989 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres5 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc0 := wn_enc_jlez_1986 (s := s5) hs5pc gs5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj0 :=
    step_JLEZ (s := s5) (x := 18) (dest := 2076)
      hs5h hpc5 hs5Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = false := by
    have : le0 (s5.mem.get 18) = false := by
      rw [hs5T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs6step : step s5 = { s5 with pc := s5.pc + 3 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (2076 : Word) else s5.pc + 3) = s5.pc + 3 := by
      simp [hle0]
    rw [hj0, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hrun6_s : s6 = _ := hrun6
  have hs6eq : s6 = { s5 with pc := 1989 } := by
    have : s6 = step s5 := hrun6
    have hp3 : s5.pc + 3 = (1989 : Word) := by simp [hs5pc]
    rw [this, hs6step, hp3]
  have hs6pc : s6.pc = 1989 := by rw [hs6eq]
  have hs6h : s6.halted = false := by rw [hs6eq]; exact hs5h
  have hs6T : s6.mem.get 18 = (6 : Word) := by rw [hs6eq]; exact hs5T
  have hs6Z : s6.mem.get 0 = 0 := by rw [hs6eq]; exact hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs6eq]; exact hpres5 a ha18 ha30 ha0
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide) (by decide)).trans hONE
  have hI6 : s6.mem.get 29 = 6 := (hpres6 29 (by decide) (by decide) (by decide)).trans hI
  have hCH6 : s6.mem.get 30 = 0 := by rw [hs6eq]; exact hCH5

  have gs6dec : ∀ k : Nat, 1989 ≤ k → k < 1992 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres6 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec1 := wn_dec_T_1989 (s := s6) hs6pc hs6h
    (fun k h1 h2 => gs6dec k h1 (by omega))
  have hrun7 : runN s 7 = step s6 := by
    have hmid : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    have hpcp : s6.pc.toNat < 32768 := by simp [hs6pc]
    exact hmid.trans (runN_one s6 hs6h hpcp)
  let s7 := runN s 7
  have hrun7_s : s7 = _ := hrun7
  have hs7eq' : s7 =
      { s6 with mem := s6.mem.set 18 (s6.mem.get 18 - s6.mem.get 3), pc := 1992 } := by
    have : s7 = step s6 := hrun7
    rw [this, hdec1]
  have hs7pc : s7.pc = 1992 := by rw [hs7eq']
  have hs7h : s7.halted = false := by rw [hs7eq']; exact hs6h
  have hs7T : s7.mem.get 18 = (5 : Word) := by
    rw [hs7eq', Mem.get_set_eq, hs6T, hONE6]
    rfl
  have hs7Z : s7.mem.get 0 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 0 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hs6Z
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 a (s6.mem.get 18 - s6.mem.get 3) ha18).trans
      (hpres6 a ha18 ha30 ha0)
  have hONE7 : s7.mem.get 3 = 1 := (hpres7 3 (by decide) (by decide) (by decide)).trans hONE
  have hI7 : s7.mem.get 29 = 6 := (hpres7 29 (by decide) (by decide) (by decide)).trans hI
  have hCH7 : s7.mem.get 30 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 30 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hCH6
  have gs7 : ∀ k : Nat, 1992 ≤ k → k < 1992+3 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres7 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc1 := wn_enc_jlez_1992 (s := s7) hs7pc gs7
  have hpc7 : s7.pc.toNat < 32768 := by simp [hs7pc]
  have hj1 :=
    step_JLEZ (s := s7) (x := 18) (dest := 2091)
      hs7h hpc7 hs7Z henc1.1 henc1.2.1 henc1.2.2 (by decide)

  have hle1 : (s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18) = false := by
    have : le0 (s7.mem.get 18) = false := by
      rw [hs7T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs8step : step s7 = { s7 with pc := s7.pc + 3 } := by
    have hif :
        (if s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18
          then (2091 : Word) else s7.pc + 3) = s7.pc + 3 := by
      simp [hle1]
    rw [hj1, hif]
  have hrun8 : runN s 8 = step s7 := by
    have hn : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hn.trans (runN_one s7 hs7h hpc7)
  let s8 := runN s 8
  have hrun8_s : s8 = _ := hrun8
  have hs8eq : s8 = { s7 with pc := 1995 } := by
    have : s8 = step s7 := hrun8
    have hp3 : s7.pc + 3 = (1995 : Word) := by simp [hs7pc]
    rw [this, hs8step, hp3]
  have hs8pc : s8.pc = 1995 := by rw [hs8eq]
  have hs8h : s8.halted = false := by rw [hs8eq]; exact hs7h
  have hs8T : s8.mem.get 18 = (5 : Word) := by rw [hs8eq]; exact hs7T
  have hs8Z : s8.mem.get 0 = 0 := by rw [hs8eq]; exact hs7Z
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs8eq]; exact hpres7 a ha18 ha30 ha0
  have hONE8 : s8.mem.get 3 = 1 := (hpres8 3 (by decide) (by decide) (by decide)).trans hONE
  have hI8 : s8.mem.get 29 = 6 := (hpres8 29 (by decide) (by decide) (by decide)).trans hI
  have hCH8 : s8.mem.get 30 = 0 := by rw [hs8eq]; exact hCH7

  have gs8dec : ∀ k : Nat, 1995 ≤ k → k < 1998 →
      s8.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres8 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec2 := wn_dec_T_1995 (s := s8) hs8pc hs8h
    (fun k h1 h2 => gs8dec k h1 (by omega))
  have hrun9 : runN s 9 = step s8 := by
    have hmid : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    have hpcp : s8.pc.toNat < 32768 := by simp [hs8pc]
    exact hmid.trans (runN_one s8 hs8h hpcp)
  let s9 := runN s 9
  have hrun9_s : s9 = _ := hrun9
  have hs9eq' : s9 =
      { s8 with mem := s8.mem.set 18 (s8.mem.get 18 - s8.mem.get 3), pc := 1998 } := by
    have : s9 = step s8 := hrun9
    rw [this, hdec2]
  have hs9pc : s9.pc = 1998 := by rw [hs9eq']
  have hs9h : s9.halted = false := by rw [hs9eq']; exact hs8h
  have hs9T : s9.mem.get 18 = (4 : Word) := by
    rw [hs9eq', Mem.get_set_eq, hs8T, hONE8]
    rfl
  have hs9Z : s9.mem.get 0 = 0 := by
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 0 (s8.mem.get 18 - s8.mem.get 3) (by decide)).trans hs8Z
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 a (s8.mem.get 18 - s8.mem.get 3) ha18).trans
      (hpres8 a ha18 ha30 ha0)
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide) (by decide)).trans hONE
  have hI9 : s9.mem.get 29 = 6 := (hpres9 29 (by decide) (by decide) (by decide)).trans hI
  have hCH9 : s9.mem.get 30 = 0 := by
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 30 (s8.mem.get 18 - s8.mem.get 3) (by decide)).trans hCH8
  have gs9 : ∀ k : Nat, 1998 ≤ k → k < 1998+3 →
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
  have henc2 := wn_enc_jlez_1998 (s := s9) hs9pc gs9
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hj2 :=
    step_JLEZ (s := s9) (x := 18) (dest := 2106)
      hs9h hpc9 hs9Z henc2.1 henc2.2.1 henc2.2.2 (by decide)

  have hle2 : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = false := by
    have : le0 (s9.mem.get 18) = false := by
      rw [hs9T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs10step : step s9 = { s9 with pc := s9.pc + 3 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18
          then (2106 : Word) else s9.pc + 3) = s9.pc + 3 := by
      simp [hle2]
    rw [hj2, hif]
  have hrun10 : runN s 10 = step s9 := by
    have hn : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hn.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hrun10_s : s10 = _ := hrun10
  have hs10eq : s10 = { s9 with pc := 2001 } := by
    have : s10 = step s9 := hrun10
    have hp3 : s9.pc + 3 = (2001 : Word) := by simp [hs9pc]
    rw [this, hs10step, hp3]
  have hs10pc : s10.pc = 2001 := by rw [hs10eq]
  have hs10h : s10.halted = false := by rw [hs10eq]; exact hs9h
  have hs10T : s10.mem.get 18 = (4 : Word) := by rw [hs10eq]; exact hs9T
  have hs10Z : s10.mem.get 0 = 0 := by rw [hs10eq]; exact hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs10eq]; exact hpres9 a ha18 ha30 ha0
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide) (by decide)).trans hONE
  have hI10 : s10.mem.get 29 = 6 := (hpres10 29 (by decide) (by decide) (by decide)).trans hI
  have hCH10 : s10.mem.get 30 = 0 := by rw [hs10eq]; exact hCH9

  have gs10dec : ∀ k : Nat, 2001 ≤ k → k < 2004 →
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
    exact (hpres10 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec3 := wn_dec_T_2001 (s := s10) hs10pc hs10h
    (fun k h1 h2 => gs10dec k h1 (by omega))
  have hrun11 : runN s 11 = step s10 := by
    have hmid : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    have hpcp : s10.pc.toNat < 32768 := by simp [hs10pc]
    exact hmid.trans (runN_one s10 hs10h hpcp)
  let s11 := runN s 11
  have hrun11_s : s11 = _ := hrun11
  have hs11eq' : s11 =
      { s10 with mem := s10.mem.set 18 (s10.mem.get 18 - s10.mem.get 3), pc := 2004 } := by
    have : s11 = step s10 := hrun11
    rw [this, hdec3]
  have hs11pc : s11.pc = 2004 := by rw [hs11eq']
  have hs11h : s11.halted = false := by rw [hs11eq']; exact hs10h
  have hs11T : s11.mem.get 18 = (3 : Word) := by
    rw [hs11eq', Mem.get_set_eq, hs10T, hONE10]
    rfl
  have hs11Z : s11.mem.get 0 = 0 := by
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 0 (s10.mem.get 18 - s10.mem.get 3) (by decide)).trans hs10Z
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 a (s10.mem.get 18 - s10.mem.get 3) ha18).trans
      (hpres10 a ha18 ha30 ha0)
  have hONE11 : s11.mem.get 3 = 1 := (hpres11 3 (by decide) (by decide) (by decide)).trans hONE
  have hI11 : s11.mem.get 29 = 6 := (hpres11 29 (by decide) (by decide) (by decide)).trans hI
  have hCH11 : s11.mem.get 30 = 0 := by
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 30 (s10.mem.get 18 - s10.mem.get 3) (by decide)).trans hCH10
  have gs11 : ∀ k : Nat, 2004 ≤ k → k < 2004+3 →
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
  have henc3 := wn_enc_jlez_2004 (s := s11) hs11pc gs11
  have hpc11 : s11.pc.toNat < 32768 := by simp [hs11pc]
  have hj3 :=
    step_JLEZ (s := s11) (x := 18) (dest := 2121)
      hs11h hpc11 hs11Z henc3.1 henc3.2.1 henc3.2.2 (by decide)

  have hle3 : (s11.mem.get 18 = 0 || 0x8000 ≤ s11.mem.get 18) = false := by
    have : le0 (s11.mem.get 18) = false := by
      rw [hs11T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs12step : step s11 = { s11 with pc := s11.pc + 3 } := by
    have hif :
        (if s11.mem.get 18 = 0 || 0x8000 ≤ s11.mem.get 18
          then (2121 : Word) else s11.pc + 3) = s11.pc + 3 := by
      simp [hle3]
    rw [hj3, hif]
  have hrun12 : runN s 12 = step s11 := by
    have hn : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hn.trans (runN_one s11 hs11h hpc11)
  let s12 := runN s 12
  have hrun12_s : s12 = _ := hrun12
  have hs12eq : s12 = { s11 with pc := 2007 } := by
    have : s12 = step s11 := hrun12
    have hp3 : s11.pc + 3 = (2007 : Word) := by simp [hs11pc]
    rw [this, hs12step, hp3]
  have hs12pc : s12.pc = 2007 := by rw [hs12eq]
  have hs12h : s12.halted = false := by rw [hs12eq]; exact hs11h
  have hs12T : s12.mem.get 18 = (3 : Word) := by rw [hs12eq]; exact hs11T
  have hs12Z : s12.mem.get 0 = 0 := by rw [hs12eq]; exact hs11Z
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs12eq]; exact hpres11 a ha18 ha30 ha0
  have hONE12 : s12.mem.get 3 = 1 := (hpres12 3 (by decide) (by decide) (by decide)).trans hONE
  have hI12 : s12.mem.get 29 = 6 := (hpres12 29 (by decide) (by decide) (by decide)).trans hI
  have hCH12 : s12.mem.get 30 = 0 := by rw [hs12eq]; exact hCH11

  have gs12dec : ∀ k : Nat, 2007 ≤ k → k < 2010 →
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
    exact (hpres12 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec4 := wn_dec_T_2007 (s := s12) hs12pc hs12h
    (fun k h1 h2 => gs12dec k h1 (by omega))
  have hrun13 : runN s 13 = step s12 := by
    have hmid : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    have hpcp : s12.pc.toNat < 32768 := by simp [hs12pc]
    exact hmid.trans (runN_one s12 hs12h hpcp)
  let s13 := runN s 13
  have hrun13_s : s13 = _ := hrun13
  have hs13eq' : s13 =
      { s12 with mem := s12.mem.set 18 (s12.mem.get 18 - s12.mem.get 3), pc := 2010 } := by
    have : s13 = step s12 := hrun13
    rw [this, hdec4]
  have hs13pc : s13.pc = 2010 := by rw [hs13eq']
  have hs13h : s13.halted = false := by rw [hs13eq']; exact hs12h
  have hs13T : s13.mem.get 18 = (2 : Word) := by
    rw [hs13eq', Mem.get_set_eq, hs12T, hONE12]
    rfl
  have hs13Z : s13.mem.get 0 = 0 := by
    rw [hs13eq']
    exact (Mem.get_set_ne s12.mem 18 0 (s12.mem.get 18 - s12.mem.get 3) (by decide)).trans hs12Z
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs13eq']
    exact (Mem.get_set_ne s12.mem 18 a (s12.mem.get 18 - s12.mem.get 3) ha18).trans
      (hpres12 a ha18 ha30 ha0)
  have hONE13 : s13.mem.get 3 = 1 := (hpres13 3 (by decide) (by decide) (by decide)).trans hONE
  have hI13 : s13.mem.get 29 = 6 := (hpres13 29 (by decide) (by decide) (by decide)).trans hI
  have hCH13 : s13.mem.get 30 = 0 := by
    rw [hs13eq']
    exact (Mem.get_set_ne s12.mem 18 30 (s12.mem.get 18 - s12.mem.get 3) (by decide)).trans hCH12
  have gs13 : ∀ k : Nat, 2010 ≤ k → k < 2010+3 →
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
  have henc4 := wn_enc_jlez_2010 (s := s13) hs13pc gs13
  have hpc13 : s13.pc.toNat < 32768 := by simp [hs13pc]
  have hj4 :=
    step_JLEZ (s := s13) (x := 18) (dest := 2136)
      hs13h hpc13 hs13Z henc4.1 henc4.2.1 henc4.2.2 (by decide)

  have hle4 : (s13.mem.get 18 = 0 || 0x8000 ≤ s13.mem.get 18) = false := by
    have : le0 (s13.mem.get 18) = false := by
      rw [hs13T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs14step : step s13 = { s13 with pc := s13.pc + 3 } := by
    have hif :
        (if s13.mem.get 18 = 0 || 0x8000 ≤ s13.mem.get 18
          then (2136 : Word) else s13.pc + 3) = s13.pc + 3 := by
      simp [hle4]
    rw [hj4, hif]
  have hrun14 : runN s 14 = step s13 := by
    have hn : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hn.trans (runN_one s13 hs13h hpc13)
  let s14 := runN s 14
  have hrun14_s : s14 = _ := hrun14
  have hs14eq : s14 = { s13 with pc := 2013 } := by
    have : s14 = step s13 := hrun14
    have hp3 : s13.pc + 3 = (2013 : Word) := by simp [hs13pc]
    rw [this, hs14step, hp3]
  have hs14pc : s14.pc = 2013 := by rw [hs14eq]
  have hs14h : s14.halted = false := by rw [hs14eq]; exact hs13h
  have hs14T : s14.mem.get 18 = (2 : Word) := by rw [hs14eq]; exact hs13T
  have hs14Z : s14.mem.get 0 = 0 := by rw [hs14eq]; exact hs13Z
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs14eq]; exact hpres13 a ha18 ha30 ha0
  have hONE14 : s14.mem.get 3 = 1 := (hpres14 3 (by decide) (by decide) (by decide)).trans hONE
  have hI14 : s14.mem.get 29 = 6 := (hpres14 29 (by decide) (by decide) (by decide)).trans hI
  have hCH14 : s14.mem.get 30 = 0 := by rw [hs14eq]; exact hCH13

  have gs14dec : ∀ k : Nat, 2013 ≤ k → k < 2016 →
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
    exact (hpres14 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec5 := wn_dec_T_2013 (s := s14) hs14pc hs14h
    (fun k h1 h2 => gs14dec k h1 (by omega))
  have hrun15 : runN s 15 = step s14 := by
    have hmid : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    have hpcp : s14.pc.toNat < 32768 := by simp [hs14pc]
    exact hmid.trans (runN_one s14 hs14h hpcp)
  let s15 := runN s 15
  have hrun15_s : s15 = _ := hrun15
  have hs15eq' : s15 =
      { s14 with mem := s14.mem.set 18 (s14.mem.get 18 - s14.mem.get 3), pc := 2016 } := by
    have : s15 = step s14 := hrun15
    rw [this, hdec5]
  have hs15pc : s15.pc = 2016 := by rw [hs15eq']
  have hs15h : s15.halted = false := by rw [hs15eq']; exact hs14h
  have hs15T : s15.mem.get 18 = (1 : Word) := by
    rw [hs15eq', Mem.get_set_eq, hs14T, hONE14]
    rfl
  have hs15Z : s15.mem.get 0 = 0 := by
    rw [hs15eq']
    exact (Mem.get_set_ne s14.mem 18 0 (s14.mem.get 18 - s14.mem.get 3) (by decide)).trans hs14Z
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs15eq']
    exact (Mem.get_set_ne s14.mem 18 a (s14.mem.get 18 - s14.mem.get 3) ha18).trans
      (hpres14 a ha18 ha30 ha0)
  have hONE15 : s15.mem.get 3 = 1 := (hpres15 3 (by decide) (by decide) (by decide)).trans hONE
  have hI15 : s15.mem.get 29 = 6 := (hpres15 29 (by decide) (by decide) (by decide)).trans hI
  have hCH15 : s15.mem.get 30 = 0 := by
    rw [hs15eq']
    exact (Mem.get_set_ne s14.mem 18 30 (s14.mem.get 18 - s14.mem.get 3) (by decide)).trans hCH14
  have gs15 : ∀ k : Nat, 2016 ≤ k → k < 2016+3 →
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
  have henc5 := wn_enc_jlez_2016 (s := s15) hs15pc gs15
  have hpc15 : s15.pc.toNat < 32768 := by simp [hs15pc]
  have hj5 :=
    step_JLEZ (s := s15) (x := 18) (dest := 2151)
      hs15h hpc15 hs15Z henc5.1 henc5.2.1 henc5.2.2 (by decide)

  have hle5 : (s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18) = false := by
    have : le0 (s15.mem.get 18) = false := by
      rw [hs15T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs16step : step s15 = { s15 with pc := s15.pc + 3 } := by
    have hif :
        (if s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18
          then (2151 : Word) else s15.pc + 3) = s15.pc + 3 := by
      simp [hle5]
    rw [hj5, hif]
  have hrun16 : runN s 16 = step s15 := by
    have hn : runN s 16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
    exact hn.trans (runN_one s15 hs15h hpc15)
  let s16 := runN s 16
  have hrun16_s : s16 = _ := hrun16
  have hs16eq : s16 = { s15 with pc := 2019 } := by
    have : s16 = step s15 := hrun16
    have hp3 : s15.pc + 3 = (2019 : Word) := by simp [hs15pc]
    rw [this, hs16step, hp3]
  have hs16pc : s16.pc = 2019 := by rw [hs16eq]
  have hs16h : s16.halted = false := by rw [hs16eq]; exact hs15h
  have hs16T : s16.mem.get 18 = (1 : Word) := by rw [hs16eq]; exact hs15T
  have hs16Z : s16.mem.get 0 = 0 := by rw [hs16eq]; exact hs15Z
  have hpres16 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs16eq]; exact hpres15 a ha18 ha30 ha0
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 6 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hCH16 : s16.mem.get 30 = 0 := by rw [hs16eq]; exact hCH15

  have gs16dec : ∀ k : Nat, 2019 ≤ k → k < 2022 →
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
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec6 := wn_dec_T_2019 (s := s16) hs16pc hs16h
    (fun k h1 h2 => gs16dec k h1 (by omega))
  have hrun17 : runN s 17 = step s16 := by
    have hmid : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
    have hpcp : s16.pc.toNat < 32768 := by simp [hs16pc]
    exact hmid.trans (runN_one s16 hs16h hpcp)
  let s17 := runN s 17
  have hrun17_s : s17 = _ := hrun17
  have hs17eq' : s17 =
      { s16 with mem := s16.mem.set 18 (s16.mem.get 18 - s16.mem.get 3), pc := 2022 } := by
    have : s17 = step s16 := hrun17
    rw [this, hdec6]
  have hs17pc : s17.pc = 2022 := by rw [hs17eq']
  have hs17h : s17.halted = false := by rw [hs17eq']; exact hs16h
  have hs17T : s17.mem.get 18 = (0 : Word) := by
    rw [hs17eq', Mem.get_set_eq, hs16T, hONE16]
    rfl
  have hs17Z : s17.mem.get 0 = 0 := by
    rw [hs17eq']
    exact (Mem.get_set_ne s16.mem 18 0 (s16.mem.get 18 - s16.mem.get 3) (by decide)).trans hs16Z
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs17eq']
    exact (Mem.get_set_ne s16.mem 18 a (s16.mem.get 18 - s16.mem.get 3) ha18).trans
      (hpres16 a ha18 ha30 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 6 := (hpres17 29 (by decide) (by decide) (by decide)).trans hI
  have hCH17 : s17.mem.get 30 = 0 := by
    rw [hs17eq']
    exact (Mem.get_set_ne s16.mem 18 30 (s16.mem.get 18 - s16.mem.get 3) (by decide)).trans hCH16
  have gs17 : ∀ k : Nat, 2022 ≤ k → k < 2022+3 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres17 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc6 := wn_enc_jlez_2022 (s := s17) hs17pc gs17
  have hpc17 : s17.pc.toNat < 32768 := by simp [hs17pc]
  have hj6 :=
    step_JLEZ (s := s17) (x := 18) (dest := 2166)
      hs17h hpc17 hs17Z henc6.1 henc6.2.1 henc6.2.2 (by decide)

  have hle6 : (s17.mem.get 18 = 0 || 0x8000 ≤ s17.mem.get 18) = true := by
    have : le0 (s17.mem.get 18) = true := by
      rw [hs17T]; exact le0_zero
    simpa [le0] using this
  have hs18step : step s17 = { s17 with pc := 2166 } := by
    have hif :
        (if s17.mem.get 18 = 0 || 0x8000 ≤ s17.mem.get 18
          then (2166 : Word) else s17.pc + 3) = (2166 : Word) := by
      simp [hle6]
    rw [hj6, hif]
  have hrun18 : runN s 18 = step s17 := by
    have hn : runN s 18 = runN s17 1 := runN_add_eq s 17 1 18 (by decide)
    exact hn.trans (runN_one s17 hs17h hpc17)
  let s18 := runN s 18
  have hrun18_s : s18 = _ := hrun18
  have hs18eq : s18 = { s17 with pc := 2166 } := by
    have : s18 = step s17 := hrun18
    rw [this, hs18step]
  have hsDpc : s18.pc = 2166 := by rw [hs18eq]
  have hsDh : s18.halted = false := by rw [hs18eq]; exact hs17h
  have hsDZ : s18.mem.get 0 = 0 := by rw [hs18eq]; exact hs17Z
  have hCHD : s18.mem.get 30 = 0 := by rw [hs18eq]; exact hCH17
  have hID : s18.mem.get 29 = 6 := by rw [hs18eq]; exact hI17
  have hpresD : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs18eq]; exact hpres17 a ha18 ha30 ha0

  have gsD : ∀ k : Nat, 2166 ≤ k → k < 2178 →
      s18.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpresD (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hm2 := wn_mov_CH_BUF6_2166 (s := s18) hsDpc hsDh hsDZ gsD
  have hrun22 : runN s 22 = runN s18 4 := runN_add_eq s 18 4 22 (by decide)
  let s22 := runN s 22
  have hrun22_s : s22 = _ := hrun22
  have hs22pc : s22.pc = 2178 := by rw [hrun22_s]; exact hm2.1
  have hs22h : s22.halted = false := by rw [hrun22_s]; exact hm2.2.1
  have hs22B : s22.mem.get 38 = 0 := by
    rw [hrun22_s, hm2.2.2.1, hCHD]
  have hs22Z : s22.mem.get 0 = 0 := by rw [hrun22_s]; exact hm2.2.2.2.1
  have hpres22mov := hm2.2.2.2.2.2
  have hpres22 : ∀ a, a ≠ 38 → a ≠ 18 → a ≠ 30 → a ≠ 0 → s22.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hrun22_s]
    exact (hpres22mov a haB ha0).trans (hpresD a ha18 ha30 ha0)
  have hI22 : s22.mem.get 29 = 6 := (hpres22 29 (by decide) (by decide) (by decide) (by decide)).trans hI
  have hCH22 : s22.mem.get 30 = 0 := by
    rw [hrun22_s]
    exact (hpres22mov 30 (by decide) (by decide)).trans hCHD
  have gs22 : ∀ k : Nat, 2178 ≤ k → k < 2178+3 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (38 : Word) := by
      have : (38 : Word) = UInt16.ofNat 38 := rfl
      rw [this]; exact ofNat_ne k 38 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hencJ := wn_enc_jmp_2178 (s := s22) hs22pc gs22
  have hpc22 : s22.pc.toNat < 32768 := by simp [hs22pc]
  have hj3 :=
    step_JMP (s := s22) (dest := 2316)
      hs22h hpc22 hs22Z hencJ.1 hencJ.2.1 hencJ.2.2
  have hrunN : runN s 23 = runN s22 1 := runN_add_eq s 22 1 23 (by decide)
  have hsNeq : sN = step s22 := hrunN.trans (runN_one s22 hs22h hpc22)
  have hsNpc : sN.pc = 2316 := by rw [hsNeq, hj3]
  have hsNh : sN.halted = false := by rw [hsNeq, hj3]; exact hs22h
  have hsNZ : sN.mem.get 0 = 0 := by rw [hsNeq, hj3]; exact hs22Z
  have hsNB : sN.mem.get 38 = 0 := by rw [hsNeq, hj3]; exact hs22B
  have hsNI : sN.mem.get 29 = 6 := by rw [hsNeq, hj3]; exact hI22
  have hsNCH : sN.mem.get 30 = 0 := by rw [hsNeq, hj3]; exact hCH22
  have hpres : ∀ a, a ≠ 38 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsNeq, hj3]; exact hpres22 a haB ha18 ha30 ha0
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hsNCH, hpres⟩


/-- `WRITE_NUL` with `IDX = 7`: 25 steps, write `0` at `BUF+7`, pc = `DONE`. -/
theorem write_nul_idx7 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 7)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2316 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 25
    sN.pc = 2316 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 39 = 0 ∧
    sN.mem.get 29 = 7 ∧
    sN.mem.get 30 = 0 ∧
    (∀ a, a ≠ 39 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hz := wn_zero_CH_1971 (s := s) hpc hh
    (fun k h1 h2 => hcode k h1 (by omega))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hrun1 : runN s 1 = step s := runN_one s hh hpc0
  let s1 := runN s 1
  have hrun1_s : s1 = _ := hrun1
  have hs1eq : s1 = { s with mem := s.mem.set 30 0, pc := 1974 } := by
    have : s1 = step s := hrun1
    rw [this, hz]
  have hs1pc : s1.pc = 1974 := by rw [hs1eq]
  have hs1h : s1.halted = false := by rw [hs1eq]; exact hh
  have hs1Z : s1.mem.get 0 = 0 := by
    rw [hs1eq]
    exact (Mem.get_set_ne s.mem 30 0 0 (by decide)).trans hZ
  have hs1CH : s1.mem.get 30 = 0 := by rw [hs1eq, Mem.get_set_eq]
  have hpres1 : ∀ a, a ≠ 30 → a ≠ 0 → s1.mem.get a = s.mem.get a := by
    intro a ha30 ha0
    rw [hs1eq]
    exact Mem.get_set_ne s.mem 30 a 0 ha30
  have hONE1 : s1.mem.get 3 = 1 := (hpres1 3 (by decide) (by decide)).trans hONE
  have hI1 : s1.mem.get 29 = 7 := (hpres1 29 (by decide) (by decide)).trans hI
  -- g for MOV uses pres excluding 30 as well as 18, 0
  have gs1 : ∀ k : Nat, 1974 ≤ k → k < 1986 →
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres1 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hm := wn_mov_IDX_T_1974 (s := s1) hs1pc hs1h hs1Z gs1
  have hrun5 : runN s 5 = runN s1 4 := runN_add_eq s 1 4 5 (by decide)
  let s5 := runN s 5
  have hrun5_s : s5 = _ := hrun5
  have hs5pc : s5.pc = 1986 := by rw [hrun5_s]; exact hm.1
  have hs5h : s5.halted = false := by rw [hrun5_s]; exact hm.2.1
  have hs5T : s5.mem.get 18 = (7 : Word) := by
    rw [hrun5_s, hm.2.2.1, hI1]
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun5_s]; exact hm.2.2.2.1
  have hpres5mov := hm.2.2.2.2.2
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hrun5_s]
    exact (hpres5mov a ha18 ha0).trans (hpres1 a ha30 ha0)
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 7 := (hpres5 29 (by decide) (by decide) (by decide)).trans hI
  have hCH5 : s5.mem.get 30 = 0 := by
    rw [hrun5_s]
    exact (hpres5mov 30 (by decide) (by decide)).trans hs1CH

  have gs5 : ∀ k : Nat, 1986 ≤ k → k < 1989 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres5 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc0 := wn_enc_jlez_1986 (s := s5) hs5pc gs5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hj0 :=
    step_JLEZ (s := s5) (x := 18) (dest := 2076)
      hs5h hpc5 hs5Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = false := by
    have : le0 (s5.mem.get 18) = false := by
      rw [hs5T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs6step : step s5 = { s5 with pc := s5.pc + 3 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (2076 : Word) else s5.pc + 3) = s5.pc + 3 := by
      simp [hle0]
    rw [hj0, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hrun6_s : s6 = _ := hrun6
  have hs6eq : s6 = { s5 with pc := 1989 } := by
    have : s6 = step s5 := hrun6
    have hp3 : s5.pc + 3 = (1989 : Word) := by simp [hs5pc]
    rw [this, hs6step, hp3]
  have hs6pc : s6.pc = 1989 := by rw [hs6eq]
  have hs6h : s6.halted = false := by rw [hs6eq]; exact hs5h
  have hs6T : s6.mem.get 18 = (7 : Word) := by rw [hs6eq]; exact hs5T
  have hs6Z : s6.mem.get 0 = 0 := by rw [hs6eq]; exact hs5Z
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs6eq]; exact hpres5 a ha18 ha30 ha0
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide) (by decide)).trans hONE
  have hI6 : s6.mem.get 29 = 7 := (hpres6 29 (by decide) (by decide) (by decide)).trans hI
  have hCH6 : s6.mem.get 30 = 0 := by rw [hs6eq]; exact hCH5

  have gs6dec : ∀ k : Nat, 1989 ≤ k → k < 1992 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres6 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec1 := wn_dec_T_1989 (s := s6) hs6pc hs6h
    (fun k h1 h2 => gs6dec k h1 (by omega))
  have hrun7 : runN s 7 = step s6 := by
    have hmid : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    have hpcp : s6.pc.toNat < 32768 := by simp [hs6pc]
    exact hmid.trans (runN_one s6 hs6h hpcp)
  let s7 := runN s 7
  have hrun7_s : s7 = _ := hrun7
  have hs7eq' : s7 =
      { s6 with mem := s6.mem.set 18 (s6.mem.get 18 - s6.mem.get 3), pc := 1992 } := by
    have : s7 = step s6 := hrun7
    rw [this, hdec1]
  have hs7pc : s7.pc = 1992 := by rw [hs7eq']
  have hs7h : s7.halted = false := by rw [hs7eq']; exact hs6h
  have hs7T : s7.mem.get 18 = (6 : Word) := by
    rw [hs7eq', Mem.get_set_eq, hs6T, hONE6]
    rfl
  have hs7Z : s7.mem.get 0 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 0 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hs6Z
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 a (s6.mem.get 18 - s6.mem.get 3) ha18).trans
      (hpres6 a ha18 ha30 ha0)
  have hONE7 : s7.mem.get 3 = 1 := (hpres7 3 (by decide) (by decide) (by decide)).trans hONE
  have hI7 : s7.mem.get 29 = 7 := (hpres7 29 (by decide) (by decide) (by decide)).trans hI
  have hCH7 : s7.mem.get 30 = 0 := by
    rw [hs7eq']
    exact (Mem.get_set_ne s6.mem 18 30 (s6.mem.get 18 - s6.mem.get 3) (by decide)).trans hCH6
  have gs7 : ∀ k : Nat, 1992 ≤ k → k < 1992+3 →
      s7.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres7 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc1 := wn_enc_jlez_1992 (s := s7) hs7pc gs7
  have hpc7 : s7.pc.toNat < 32768 := by simp [hs7pc]
  have hj1 :=
    step_JLEZ (s := s7) (x := 18) (dest := 2091)
      hs7h hpc7 hs7Z henc1.1 henc1.2.1 henc1.2.2 (by decide)

  have hle1 : (s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18) = false := by
    have : le0 (s7.mem.get 18) = false := by
      rw [hs7T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs8step : step s7 = { s7 with pc := s7.pc + 3 } := by
    have hif :
        (if s7.mem.get 18 = 0 || 0x8000 ≤ s7.mem.get 18
          then (2091 : Word) else s7.pc + 3) = s7.pc + 3 := by
      simp [hle1]
    rw [hj1, hif]
  have hrun8 : runN s 8 = step s7 := by
    have hn : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hn.trans (runN_one s7 hs7h hpc7)
  let s8 := runN s 8
  have hrun8_s : s8 = _ := hrun8
  have hs8eq : s8 = { s7 with pc := 1995 } := by
    have : s8 = step s7 := hrun8
    have hp3 : s7.pc + 3 = (1995 : Word) := by simp [hs7pc]
    rw [this, hs8step, hp3]
  have hs8pc : s8.pc = 1995 := by rw [hs8eq]
  have hs8h : s8.halted = false := by rw [hs8eq]; exact hs7h
  have hs8T : s8.mem.get 18 = (6 : Word) := by rw [hs8eq]; exact hs7T
  have hs8Z : s8.mem.get 0 = 0 := by rw [hs8eq]; exact hs7Z
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs8eq]; exact hpres7 a ha18 ha30 ha0
  have hONE8 : s8.mem.get 3 = 1 := (hpres8 3 (by decide) (by decide) (by decide)).trans hONE
  have hI8 : s8.mem.get 29 = 7 := (hpres8 29 (by decide) (by decide) (by decide)).trans hI
  have hCH8 : s8.mem.get 30 = 0 := by rw [hs8eq]; exact hCH7

  have gs8dec : ∀ k : Nat, 1995 ≤ k → k < 1998 →
      s8.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres8 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec2 := wn_dec_T_1995 (s := s8) hs8pc hs8h
    (fun k h1 h2 => gs8dec k h1 (by omega))
  have hrun9 : runN s 9 = step s8 := by
    have hmid : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    have hpcp : s8.pc.toNat < 32768 := by simp [hs8pc]
    exact hmid.trans (runN_one s8 hs8h hpcp)
  let s9 := runN s 9
  have hrun9_s : s9 = _ := hrun9
  have hs9eq' : s9 =
      { s8 with mem := s8.mem.set 18 (s8.mem.get 18 - s8.mem.get 3), pc := 1998 } := by
    have : s9 = step s8 := hrun9
    rw [this, hdec2]
  have hs9pc : s9.pc = 1998 := by rw [hs9eq']
  have hs9h : s9.halted = false := by rw [hs9eq']; exact hs8h
  have hs9T : s9.mem.get 18 = (5 : Word) := by
    rw [hs9eq', Mem.get_set_eq, hs8T, hONE8]
    rfl
  have hs9Z : s9.mem.get 0 = 0 := by
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 0 (s8.mem.get 18 - s8.mem.get 3) (by decide)).trans hs8Z
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 a (s8.mem.get 18 - s8.mem.get 3) ha18).trans
      (hpres8 a ha18 ha30 ha0)
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide) (by decide)).trans hONE
  have hI9 : s9.mem.get 29 = 7 := (hpres9 29 (by decide) (by decide) (by decide)).trans hI
  have hCH9 : s9.mem.get 30 = 0 := by
    rw [hs9eq']
    exact (Mem.get_set_ne s8.mem 18 30 (s8.mem.get 18 - s8.mem.get 3) (by decide)).trans hCH8
  have gs9 : ∀ k : Nat, 1998 ≤ k → k < 1998+3 →
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
  have henc2 := wn_enc_jlez_1998 (s := s9) hs9pc gs9
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hj2 :=
    step_JLEZ (s := s9) (x := 18) (dest := 2106)
      hs9h hpc9 hs9Z henc2.1 henc2.2.1 henc2.2.2 (by decide)

  have hle2 : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = false := by
    have : le0 (s9.mem.get 18) = false := by
      rw [hs9T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs10step : step s9 = { s9 with pc := s9.pc + 3 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18
          then (2106 : Word) else s9.pc + 3) = s9.pc + 3 := by
      simp [hle2]
    rw [hj2, hif]
  have hrun10 : runN s 10 = step s9 := by
    have hn : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hn.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hrun10_s : s10 = _ := hrun10
  have hs10eq : s10 = { s9 with pc := 2001 } := by
    have : s10 = step s9 := hrun10
    have hp3 : s9.pc + 3 = (2001 : Word) := by simp [hs9pc]
    rw [this, hs10step, hp3]
  have hs10pc : s10.pc = 2001 := by rw [hs10eq]
  have hs10h : s10.halted = false := by rw [hs10eq]; exact hs9h
  have hs10T : s10.mem.get 18 = (5 : Word) := by rw [hs10eq]; exact hs9T
  have hs10Z : s10.mem.get 0 = 0 := by rw [hs10eq]; exact hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs10eq]; exact hpres9 a ha18 ha30 ha0
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide) (by decide)).trans hONE
  have hI10 : s10.mem.get 29 = 7 := (hpres10 29 (by decide) (by decide) (by decide)).trans hI
  have hCH10 : s10.mem.get 30 = 0 := by rw [hs10eq]; exact hCH9

  have gs10dec : ∀ k : Nat, 2001 ≤ k → k < 2004 →
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
    exact (hpres10 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec3 := wn_dec_T_2001 (s := s10) hs10pc hs10h
    (fun k h1 h2 => gs10dec k h1 (by omega))
  have hrun11 : runN s 11 = step s10 := by
    have hmid : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    have hpcp : s10.pc.toNat < 32768 := by simp [hs10pc]
    exact hmid.trans (runN_one s10 hs10h hpcp)
  let s11 := runN s 11
  have hrun11_s : s11 = _ := hrun11
  have hs11eq' : s11 =
      { s10 with mem := s10.mem.set 18 (s10.mem.get 18 - s10.mem.get 3), pc := 2004 } := by
    have : s11 = step s10 := hrun11
    rw [this, hdec3]
  have hs11pc : s11.pc = 2004 := by rw [hs11eq']
  have hs11h : s11.halted = false := by rw [hs11eq']; exact hs10h
  have hs11T : s11.mem.get 18 = (4 : Word) := by
    rw [hs11eq', Mem.get_set_eq, hs10T, hONE10]
    rfl
  have hs11Z : s11.mem.get 0 = 0 := by
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 0 (s10.mem.get 18 - s10.mem.get 3) (by decide)).trans hs10Z
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 a (s10.mem.get 18 - s10.mem.get 3) ha18).trans
      (hpres10 a ha18 ha30 ha0)
  have hONE11 : s11.mem.get 3 = 1 := (hpres11 3 (by decide) (by decide) (by decide)).trans hONE
  have hI11 : s11.mem.get 29 = 7 := (hpres11 29 (by decide) (by decide) (by decide)).trans hI
  have hCH11 : s11.mem.get 30 = 0 := by
    rw [hs11eq']
    exact (Mem.get_set_ne s10.mem 18 30 (s10.mem.get 18 - s10.mem.get 3) (by decide)).trans hCH10
  have gs11 : ∀ k : Nat, 2004 ≤ k → k < 2004+3 →
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
  have henc3 := wn_enc_jlez_2004 (s := s11) hs11pc gs11
  have hpc11 : s11.pc.toNat < 32768 := by simp [hs11pc]
  have hj3 :=
    step_JLEZ (s := s11) (x := 18) (dest := 2121)
      hs11h hpc11 hs11Z henc3.1 henc3.2.1 henc3.2.2 (by decide)

  have hle3 : (s11.mem.get 18 = 0 || 0x8000 ≤ s11.mem.get 18) = false := by
    have : le0 (s11.mem.get 18) = false := by
      rw [hs11T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs12step : step s11 = { s11 with pc := s11.pc + 3 } := by
    have hif :
        (if s11.mem.get 18 = 0 || 0x8000 ≤ s11.mem.get 18
          then (2121 : Word) else s11.pc + 3) = s11.pc + 3 := by
      simp [hle3]
    rw [hj3, hif]
  have hrun12 : runN s 12 = step s11 := by
    have hn : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hn.trans (runN_one s11 hs11h hpc11)
  let s12 := runN s 12
  have hrun12_s : s12 = _ := hrun12
  have hs12eq : s12 = { s11 with pc := 2007 } := by
    have : s12 = step s11 := hrun12
    have hp3 : s11.pc + 3 = (2007 : Word) := by simp [hs11pc]
    rw [this, hs12step, hp3]
  have hs12pc : s12.pc = 2007 := by rw [hs12eq]
  have hs12h : s12.halted = false := by rw [hs12eq]; exact hs11h
  have hs12T : s12.mem.get 18 = (4 : Word) := by rw [hs12eq]; exact hs11T
  have hs12Z : s12.mem.get 0 = 0 := by rw [hs12eq]; exact hs11Z
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs12eq]; exact hpres11 a ha18 ha30 ha0
  have hONE12 : s12.mem.get 3 = 1 := (hpres12 3 (by decide) (by decide) (by decide)).trans hONE
  have hI12 : s12.mem.get 29 = 7 := (hpres12 29 (by decide) (by decide) (by decide)).trans hI
  have hCH12 : s12.mem.get 30 = 0 := by rw [hs12eq]; exact hCH11

  have gs12dec : ∀ k : Nat, 2007 ≤ k → k < 2010 →
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
    exact (hpres12 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec4 := wn_dec_T_2007 (s := s12) hs12pc hs12h
    (fun k h1 h2 => gs12dec k h1 (by omega))
  have hrun13 : runN s 13 = step s12 := by
    have hmid : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    have hpcp : s12.pc.toNat < 32768 := by simp [hs12pc]
    exact hmid.trans (runN_one s12 hs12h hpcp)
  let s13 := runN s 13
  have hrun13_s : s13 = _ := hrun13
  have hs13eq' : s13 =
      { s12 with mem := s12.mem.set 18 (s12.mem.get 18 - s12.mem.get 3), pc := 2010 } := by
    have : s13 = step s12 := hrun13
    rw [this, hdec4]
  have hs13pc : s13.pc = 2010 := by rw [hs13eq']
  have hs13h : s13.halted = false := by rw [hs13eq']; exact hs12h
  have hs13T : s13.mem.get 18 = (3 : Word) := by
    rw [hs13eq', Mem.get_set_eq, hs12T, hONE12]
    rfl
  have hs13Z : s13.mem.get 0 = 0 := by
    rw [hs13eq']
    exact (Mem.get_set_ne s12.mem 18 0 (s12.mem.get 18 - s12.mem.get 3) (by decide)).trans hs12Z
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs13eq']
    exact (Mem.get_set_ne s12.mem 18 a (s12.mem.get 18 - s12.mem.get 3) ha18).trans
      (hpres12 a ha18 ha30 ha0)
  have hONE13 : s13.mem.get 3 = 1 := (hpres13 3 (by decide) (by decide) (by decide)).trans hONE
  have hI13 : s13.mem.get 29 = 7 := (hpres13 29 (by decide) (by decide) (by decide)).trans hI
  have hCH13 : s13.mem.get 30 = 0 := by
    rw [hs13eq']
    exact (Mem.get_set_ne s12.mem 18 30 (s12.mem.get 18 - s12.mem.get 3) (by decide)).trans hCH12
  have gs13 : ∀ k : Nat, 2010 ≤ k → k < 2010+3 →
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
  have henc4 := wn_enc_jlez_2010 (s := s13) hs13pc gs13
  have hpc13 : s13.pc.toNat < 32768 := by simp [hs13pc]
  have hj4 :=
    step_JLEZ (s := s13) (x := 18) (dest := 2136)
      hs13h hpc13 hs13Z henc4.1 henc4.2.1 henc4.2.2 (by decide)

  have hle4 : (s13.mem.get 18 = 0 || 0x8000 ≤ s13.mem.get 18) = false := by
    have : le0 (s13.mem.get 18) = false := by
      rw [hs13T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs14step : step s13 = { s13 with pc := s13.pc + 3 } := by
    have hif :
        (if s13.mem.get 18 = 0 || 0x8000 ≤ s13.mem.get 18
          then (2136 : Word) else s13.pc + 3) = s13.pc + 3 := by
      simp [hle4]
    rw [hj4, hif]
  have hrun14 : runN s 14 = step s13 := by
    have hn : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hn.trans (runN_one s13 hs13h hpc13)
  let s14 := runN s 14
  have hrun14_s : s14 = _ := hrun14
  have hs14eq : s14 = { s13 with pc := 2013 } := by
    have : s14 = step s13 := hrun14
    have hp3 : s13.pc + 3 = (2013 : Word) := by simp [hs13pc]
    rw [this, hs14step, hp3]
  have hs14pc : s14.pc = 2013 := by rw [hs14eq]
  have hs14h : s14.halted = false := by rw [hs14eq]; exact hs13h
  have hs14T : s14.mem.get 18 = (3 : Word) := by rw [hs14eq]; exact hs13T
  have hs14Z : s14.mem.get 0 = 0 := by rw [hs14eq]; exact hs13Z
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs14eq]; exact hpres13 a ha18 ha30 ha0
  have hONE14 : s14.mem.get 3 = 1 := (hpres14 3 (by decide) (by decide) (by decide)).trans hONE
  have hI14 : s14.mem.get 29 = 7 := (hpres14 29 (by decide) (by decide) (by decide)).trans hI
  have hCH14 : s14.mem.get 30 = 0 := by rw [hs14eq]; exact hCH13

  have gs14dec : ∀ k : Nat, 2013 ≤ k → k < 2016 →
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
    exact (hpres14 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec5 := wn_dec_T_2013 (s := s14) hs14pc hs14h
    (fun k h1 h2 => gs14dec k h1 (by omega))
  have hrun15 : runN s 15 = step s14 := by
    have hmid : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    have hpcp : s14.pc.toNat < 32768 := by simp [hs14pc]
    exact hmid.trans (runN_one s14 hs14h hpcp)
  let s15 := runN s 15
  have hrun15_s : s15 = _ := hrun15
  have hs15eq' : s15 =
      { s14 with mem := s14.mem.set 18 (s14.mem.get 18 - s14.mem.get 3), pc := 2016 } := by
    have : s15 = step s14 := hrun15
    rw [this, hdec5]
  have hs15pc : s15.pc = 2016 := by rw [hs15eq']
  have hs15h : s15.halted = false := by rw [hs15eq']; exact hs14h
  have hs15T : s15.mem.get 18 = (2 : Word) := by
    rw [hs15eq', Mem.get_set_eq, hs14T, hONE14]
    rfl
  have hs15Z : s15.mem.get 0 = 0 := by
    rw [hs15eq']
    exact (Mem.get_set_ne s14.mem 18 0 (s14.mem.get 18 - s14.mem.get 3) (by decide)).trans hs14Z
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs15eq']
    exact (Mem.get_set_ne s14.mem 18 a (s14.mem.get 18 - s14.mem.get 3) ha18).trans
      (hpres14 a ha18 ha30 ha0)
  have hONE15 : s15.mem.get 3 = 1 := (hpres15 3 (by decide) (by decide) (by decide)).trans hONE
  have hI15 : s15.mem.get 29 = 7 := (hpres15 29 (by decide) (by decide) (by decide)).trans hI
  have hCH15 : s15.mem.get 30 = 0 := by
    rw [hs15eq']
    exact (Mem.get_set_ne s14.mem 18 30 (s14.mem.get 18 - s14.mem.get 3) (by decide)).trans hCH14
  have gs15 : ∀ k : Nat, 2016 ≤ k → k < 2016+3 →
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
  have henc5 := wn_enc_jlez_2016 (s := s15) hs15pc gs15
  have hpc15 : s15.pc.toNat < 32768 := by simp [hs15pc]
  have hj5 :=
    step_JLEZ (s := s15) (x := 18) (dest := 2151)
      hs15h hpc15 hs15Z henc5.1 henc5.2.1 henc5.2.2 (by decide)

  have hle5 : (s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18) = false := by
    have : le0 (s15.mem.get 18) = false := by
      rw [hs15T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs16step : step s15 = { s15 with pc := s15.pc + 3 } := by
    have hif :
        (if s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18
          then (2151 : Word) else s15.pc + 3) = s15.pc + 3 := by
      simp [hle5]
    rw [hj5, hif]
  have hrun16 : runN s 16 = step s15 := by
    have hn : runN s 16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
    exact hn.trans (runN_one s15 hs15h hpc15)
  let s16 := runN s 16
  have hrun16_s : s16 = _ := hrun16
  have hs16eq : s16 = { s15 with pc := 2019 } := by
    have : s16 = step s15 := hrun16
    have hp3 : s15.pc + 3 = (2019 : Word) := by simp [hs15pc]
    rw [this, hs16step, hp3]
  have hs16pc : s16.pc = 2019 := by rw [hs16eq]
  have hs16h : s16.halted = false := by rw [hs16eq]; exact hs15h
  have hs16T : s16.mem.get 18 = (2 : Word) := by rw [hs16eq]; exact hs15T
  have hs16Z : s16.mem.get 0 = 0 := by rw [hs16eq]; exact hs15Z
  have hpres16 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs16eq]; exact hpres15 a ha18 ha30 ha0
  have hONE16 : s16.mem.get 3 = 1 := (hpres16 3 (by decide) (by decide) (by decide)).trans hONE
  have hI16 : s16.mem.get 29 = 7 := (hpres16 29 (by decide) (by decide) (by decide)).trans hI
  have hCH16 : s16.mem.get 30 = 0 := by rw [hs16eq]; exact hCH15

  have gs16dec : ∀ k : Nat, 2019 ≤ k → k < 2022 →
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
    exact (hpres16 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec6 := wn_dec_T_2019 (s := s16) hs16pc hs16h
    (fun k h1 h2 => gs16dec k h1 (by omega))
  have hrun17 : runN s 17 = step s16 := by
    have hmid : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
    have hpcp : s16.pc.toNat < 32768 := by simp [hs16pc]
    exact hmid.trans (runN_one s16 hs16h hpcp)
  let s17 := runN s 17
  have hrun17_s : s17 = _ := hrun17
  have hs17eq' : s17 =
      { s16 with mem := s16.mem.set 18 (s16.mem.get 18 - s16.mem.get 3), pc := 2022 } := by
    have : s17 = step s16 := hrun17
    rw [this, hdec6]
  have hs17pc : s17.pc = 2022 := by rw [hs17eq']
  have hs17h : s17.halted = false := by rw [hs17eq']; exact hs16h
  have hs17T : s17.mem.get 18 = (1 : Word) := by
    rw [hs17eq', Mem.get_set_eq, hs16T, hONE16]
    rfl
  have hs17Z : s17.mem.get 0 = 0 := by
    rw [hs17eq']
    exact (Mem.get_set_ne s16.mem 18 0 (s16.mem.get 18 - s16.mem.get 3) (by decide)).trans hs16Z
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs17eq']
    exact (Mem.get_set_ne s16.mem 18 a (s16.mem.get 18 - s16.mem.get 3) ha18).trans
      (hpres16 a ha18 ha30 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 7 := (hpres17 29 (by decide) (by decide) (by decide)).trans hI
  have hCH17 : s17.mem.get 30 = 0 := by
    rw [hs17eq']
    exact (Mem.get_set_ne s16.mem 18 30 (s16.mem.get 18 - s16.mem.get 3) (by decide)).trans hCH16
  have gs17 : ∀ k : Nat, 2022 ≤ k → k < 2022+3 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres17 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc6 := wn_enc_jlez_2022 (s := s17) hs17pc gs17
  have hpc17 : s17.pc.toNat < 32768 := by simp [hs17pc]
  have hj6 :=
    step_JLEZ (s := s17) (x := 18) (dest := 2166)
      hs17h hpc17 hs17Z henc6.1 henc6.2.1 henc6.2.2 (by decide)

  have hle6 : (s17.mem.get 18 = 0 || 0x8000 ≤ s17.mem.get 18) = false := by
    have : le0 (s17.mem.get 18) = false := by
      rw [hs17T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs18step : step s17 = { s17 with pc := s17.pc + 3 } := by
    have hif :
        (if s17.mem.get 18 = 0 || 0x8000 ≤ s17.mem.get 18
          then (2166 : Word) else s17.pc + 3) = s17.pc + 3 := by
      simp [hle6]
    rw [hj6, hif]
  have hrun18 : runN s 18 = step s17 := by
    have hn : runN s 18 = runN s17 1 := runN_add_eq s 17 1 18 (by decide)
    exact hn.trans (runN_one s17 hs17h hpc17)
  let s18 := runN s 18
  have hrun18_s : s18 = _ := hrun18
  have hs18eq : s18 = { s17 with pc := 2025 } := by
    have : s18 = step s17 := hrun18
    have hp3 : s17.pc + 3 = (2025 : Word) := by simp [hs17pc]
    rw [this, hs18step, hp3]
  have hs18pc : s18.pc = 2025 := by rw [hs18eq]
  have hs18h : s18.halted = false := by rw [hs18eq]; exact hs17h
  have hs18T : s18.mem.get 18 = (1 : Word) := by rw [hs18eq]; exact hs17T
  have hs18Z : s18.mem.get 0 = 0 := by rw [hs18eq]; exact hs17Z
  have hpres18 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs18eq]; exact hpres17 a ha18 ha30 ha0
  have hONE18 : s18.mem.get 3 = 1 := (hpres18 3 (by decide) (by decide) (by decide)).trans hONE
  have hI18 : s18.mem.get 29 = 7 := (hpres18 29 (by decide) (by decide) (by decide)).trans hI
  have hCH18 : s18.mem.get 30 = 0 := by rw [hs18eq]; exact hCH17

  have gs18dec : ∀ k : Nat, 2025 ≤ k → k < 2028 →
      s18.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres18 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hdec7 := wn_dec_T_2025 (s := s18) hs18pc hs18h
    (fun k h1 h2 => gs18dec k h1 (by omega))
  have hrun19 : runN s 19 = step s18 := by
    have hmid : runN s 19 = runN s18 1 := runN_add_eq s 18 1 19 (by decide)
    have hpcp : s18.pc.toNat < 32768 := by simp [hs18pc]
    exact hmid.trans (runN_one s18 hs18h hpcp)
  let s19 := runN s 19
  have hrun19_s : s19 = _ := hrun19
  have hs19eq' : s19 =
      { s18 with mem := s18.mem.set 18 (s18.mem.get 18 - s18.mem.get 3), pc := 2028 } := by
    have : s19 = step s18 := hrun19
    rw [this, hdec7]
  have hs19pc : s19.pc = 2028 := by rw [hs19eq']
  have hs19h : s19.halted = false := by rw [hs19eq']; exact hs18h
  have hs19T : s19.mem.get 18 = (0 : Word) := by
    rw [hs19eq', Mem.get_set_eq, hs18T, hONE18]
    rfl
  have hs19Z : s19.mem.get 0 = 0 := by
    rw [hs19eq']
    exact (Mem.get_set_ne s18.mem 18 0 (s18.mem.get 18 - s18.mem.get 3) (by decide)).trans hs18Z
  have hpres19 : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s19.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs19eq']
    exact (Mem.get_set_ne s18.mem 18 a (s18.mem.get 18 - s18.mem.get 3) ha18).trans
      (hpres18 a ha18 ha30 ha0)
  have hONE19 : s19.mem.get 3 = 1 := (hpres19 3 (by decide) (by decide) (by decide)).trans hONE
  have hI19 : s19.mem.get 29 = 7 := (hpres19 29 (by decide) (by decide) (by decide)).trans hI
  have hCH19 : s19.mem.get 30 = 0 := by
    rw [hs19eq']
    exact (Mem.get_set_ne s18.mem 18 30 (s18.mem.get 18 - s18.mem.get 3) (by decide)).trans hCH18
  have gs19 : ∀ k : Nat, 2028 ≤ k → k < 2028+3 →
      s19.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres19 (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc7 := wn_enc_jlez_2028 (s := s19) hs19pc gs19
  have hpc19 : s19.pc.toNat < 32768 := by simp [hs19pc]
  have hj7 :=
    step_JLEZ (s := s19) (x := 18) (dest := 2181)
      hs19h hpc19 hs19Z henc7.1 henc7.2.1 henc7.2.2 (by decide)

  have hle7 : (s19.mem.get 18 = 0 || 0x8000 ≤ s19.mem.get 18) = true := by
    have : le0 (s19.mem.get 18) = true := by
      rw [hs19T]; exact le0_zero
    simpa [le0] using this
  have hs20step : step s19 = { s19 with pc := 2181 } := by
    have hif :
        (if s19.mem.get 18 = 0 || 0x8000 ≤ s19.mem.get 18
          then (2181 : Word) else s19.pc + 3) = (2181 : Word) := by
      simp [hle7]
    rw [hj7, hif]
  have hrun20 : runN s 20 = step s19 := by
    have hn : runN s 20 = runN s19 1 := runN_add_eq s 19 1 20 (by decide)
    exact hn.trans (runN_one s19 hs19h hpc19)
  let s20 := runN s 20
  have hrun20_s : s20 = _ := hrun20
  have hs20eq : s20 = { s19 with pc := 2181 } := by
    have : s20 = step s19 := hrun20
    rw [this, hs20step]
  have hsDpc : s20.pc = 2181 := by rw [hs20eq]
  have hsDh : s20.halted = false := by rw [hs20eq]; exact hs19h
  have hsDZ : s20.mem.get 0 = 0 := by rw [hs20eq]; exact hs19Z
  have hCHD : s20.mem.get 30 = 0 := by rw [hs20eq]; exact hCH19
  have hID : s20.mem.get 29 = 7 := by rw [hs20eq]; exact hI19
  have hpresD : ∀ a, a ≠ 18 → a ≠ 30 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a ha18 ha30 ha0
    rw [hs20eq]; exact hpres19 a ha18 ha30 ha0

  have gsD : ∀ k : Nat, 2181 ≤ k → k < 2193 →
      s20.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpresD (UInt16.ofNat k) n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hm2 := wn_mov_CH_BUF7_2181 (s := s20) hsDpc hsDh hsDZ gsD
  have hrun24 : runN s 24 = runN s20 4 := runN_add_eq s 20 4 24 (by decide)
  let s24 := runN s 24
  have hrun24_s : s24 = _ := hrun24
  have hs24pc : s24.pc = 2193 := by rw [hrun24_s]; exact hm2.1
  have hs24h : s24.halted = false := by rw [hrun24_s]; exact hm2.2.1
  have hs24B : s24.mem.get 39 = 0 := by
    rw [hrun24_s, hm2.2.2.1, hCHD]
  have hs24Z : s24.mem.get 0 = 0 := by rw [hrun24_s]; exact hm2.2.2.2.1
  have hpres24mov := hm2.2.2.2.2.2
  have hpres24 : ∀ a, a ≠ 39 → a ≠ 18 → a ≠ 30 → a ≠ 0 → s24.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hrun24_s]
    exact (hpres24mov a haB ha0).trans (hpresD a ha18 ha30 ha0)
  have hI24 : s24.mem.get 29 = 7 := (hpres24 29 (by decide) (by decide) (by decide) (by decide)).trans hI
  have hCH24 : s24.mem.get 30 = 0 := by
    rw [hrun24_s]
    exact (hpres24mov 30 (by decide) (by decide)).trans hCHD
  have gs24 : ∀ k : Nat, 2193 ≤ k → k < 2193+3 →
      s24.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (39 : Word) := by
      have : (39 : Word) = UInt16.ofNat 39 := rfl
      rw [this]; exact ofNat_ne k 39 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres24 (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hencJ := wn_enc_jmp_2193 (s := s24) hs24pc gs24
  have hpc24 : s24.pc.toNat < 32768 := by simp [hs24pc]
  have hj3 :=
    step_JMP (s := s24) (dest := 2316)
      hs24h hpc24 hs24Z hencJ.1 hencJ.2.1 hencJ.2.2
  have hrunN : runN s 25 = runN s24 1 := runN_add_eq s 24 1 25 (by decide)
  have hsNeq : sN = step s24 := hrunN.trans (runN_one s24 hs24h hpc24)
  have hsNpc : sN.pc = 2316 := by rw [hsNeq, hj3]
  have hsNh : sN.halted = false := by rw [hsNeq, hj3]; exact hs24h
  have hsNZ : sN.mem.get 0 = 0 := by rw [hsNeq, hj3]; exact hs24Z
  have hsNB : sN.mem.get 39 = 0 := by rw [hsNeq, hj3]; exact hs24B
  have hsNI : sN.mem.get 29 = 7 := by rw [hsNeq, hj3]; exact hI24
  have hsNCH : sN.mem.get 30 = 0 := by rw [hsNeq, hj3]; exact hCH24
  have hpres : ∀ a, a ≠ 39 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsNeq, hj3]; exact hpres24 a haB ha18 ha30 ha0
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hsNCH, hpres⟩


/-- `WRITE_NUL` at `IDX = 0` plus the `HALT` at `DONE`: 12 steps, `pc = 32768`. -/
theorem write_nul_halt_idx0 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 0)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sH := runN s 12
    sH.pc = 32768 ∧
    sH.halted = false ∧
    sH.mem.get 0 = 0 ∧
    sH.mem.get 32 = 0 ∧
    sH.mem.get 29 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a) := by
  intro sH
  have hw := write_nul_idx0 (s := s) hpc hh hZ hONE hI
    (fun k h1 h2 => hcode k h1 (by omega))
  let sN := runN s 11
  have hrun : sH = runN sN 1 := runN_add_eq s 11 1 12 (by decide)
  have hsNpc : sN.pc = 2316 := hw.1
  have hsNh : sN.halted = false := hw.2.1
  have hsNZ : sN.mem.get 0 = 0 := hw.2.2.1
  have hpresN := hw.2.2.2.2.2.2
  have gsN : ∀ k : Nat, 2316 ≤ k → k < 2319 →
      sN.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresN (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_halt_2316 (s := sN) hsNpc gsN
  have hpcN : sN.pc.toNat < 32768 := by simp [hsNpc]
  have hhalt :=
    step_HALT (s := sN) hsNh hpcN hsNZ henc.1 henc.2.1 henc.2.2
  have hsHeq : sH = step sN := hrun.trans (runN_one sN hsNh hpcN)
  have hsHpc : sH.pc = 32768 := by rw [hsHeq, hhalt]
  have hsHh : sH.halted = false := by rw [hsHeq, hhalt]; exact hsNh
  have hsHZ : sH.mem.get 0 = 0 := by rw [hsHeq, hhalt]; exact hsNZ
  have hsHB : sH.mem.get 32 = 0 := by rw [hsHeq, hhalt]; exact hw.2.2.2.1
  have hsHI : sH.mem.get 29 = 0 := by rw [hsHeq, hhalt]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsHeq, hhalt]; exact hpresN a haB ha18 ha30 ha0
  exact ⟨hsHpc, hsHh, hsHZ, hsHB, hsHI, hpres⟩

/-- One more `runN` tick after the `HALT` instruction sets `halted`. -/
theorem write_nul_done_idx0 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 0)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 13
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = 0 ∧
    sD.mem.get 29 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hw := write_nul_halt_idx0 (s := s) hpc hh hZ hONE hI hcode
  let sH := runN s 12
  have hrun : sD = runN sH 1 := runN_add_eq s 12 1 13 (by decide)
  have hpcH : 32768 ≤ sH.pc.toNat := by
    have : sH.pc = 32768 := hw.1
    simp [this]
  have hsDeq : sD = { sH with halted := true } := by
    rw [hrun, runN_succ_halt sH 0 (Or.inr hpcH)]
  have hsDpc : sD.pc = 32768 := by rw [hsDeq]; exact hw.1
  have hsDh : sD.halted = true := by rw [hsDeq]
  have hsDZ : sD.mem.get 0 = 0 := by rw [hsDeq]; exact hw.2.2.1
  have hsDB : sD.mem.get 32 = 0 := by rw [hsDeq]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 0 := by rw [hsDeq]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsDeq]; exact hw.2.2.2.2.2 a haB ha18 ha30 ha0
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hpres⟩


/-- `AFTER_DIGS` with `LEN = 0 < CAP`, through `WRITE_NUL` and `DONE`, to a halted machine. 28 steps. -/
theorem after_digs_write_nul_done_len0 {s : Machine}
    (hpc : s.pc = 1905)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hL : s.mem.get 16 = 0)
    (hLlt : (0 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 28
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = 0 ∧
    sD.mem.get 29 = 0 ∧
    sD.mem.get 16 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hLlt' : (s.mem.get 16).toNat < (s.mem.get 13).toNat := by
    have : (s.mem.get 16).toNat = 0 := by simp [hL]
    omega
  have ha := after_digs_nul_at_len (s := s) hpc hh hZ hONE hLlt' hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s15 := runN s 15
  have hs15pc : s15.pc = 1971 := ha.1
  have hs15h : s15.halted = false := ha.2.1
  have hs15Z : s15.mem.get 0 = 0 := ha.2.2.1
  have hs15I : s15.mem.get 29 = 0 := ha.2.2.2.1.trans hL
  have hs15L : s15.mem.get 16 = 0 := ha.2.2.2.2.1.trans hL
  have hpres15 := ha.2.2.2.2.2.2
  have hONE15 : s15.mem.get 3 = 1 := (hpres15 3 (by decide) (by decide) (by decide)).trans hONE
  have g15 : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres15 (UInt16.ofNat k) n18 n29 n0).trans (hcode k (by omega) (by omega))
  have hw := write_nul_done_idx0 (s := s15) hs15pc hs15h hs15Z hONE15 hs15I g15
  have hrun : sD = runN s15 13 := runN_add_eq s 15 13 28 (by decide)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDB : sD.mem.get 32 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 0 := by rw [hrun]; exact hw.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2
  have hsDL : sD.mem.get 16 = 0 := by
    rw [hrun]
    have h16 : s15.mem.get 16 = 0 := hs15L
    exact (hpresw 16 (by decide) (by decide) (by decide) (by decide)).trans h16
  have hpres : ∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha29 ha0
    rw [hrun]
    exact (hpresw a haB ha18 ha30 ha0).trans (hpres15 a ha18 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hsDL, hpres⟩


/-- `WRITE_NUL` at `IDX = 1` plus the `HALT` at `DONE`: 14 steps, `pc = 32768`. -/
theorem write_nul_halt_idx1 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 1)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sH := runN s 14
    sH.pc = 32768 ∧
    sH.halted = false ∧
    sH.mem.get 0 = 0 ∧
    sH.mem.get 33 = 0 ∧
    sH.mem.get 29 = 1 ∧
    (∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a) := by
  intro sH
  have hw := write_nul_idx1 (s := s) hpc hh hZ hONE hI
    (fun k h1 h2 => hcode k h1 (by omega))
  let sN := runN s 13
  have hrun : sH = runN sN 1 := runN_add_eq s 13 1 14 (by decide)
  have hsNpc : sN.pc = 2316 := hw.1
  have hsNh : sN.halted = false := hw.2.1
  have hsNZ : sN.mem.get 0 = 0 := hw.2.2.1
  have hpresN := hw.2.2.2.2.2.2
  have gsN : ∀ k : Nat, 2316 ≤ k → k < 2319 →
      sN.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresN (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_halt_2316 (s := sN) hsNpc gsN
  have hpcN : sN.pc.toNat < 32768 := by simp [hsNpc]
  have hhalt :=
    step_HALT (s := sN) hsNh hpcN hsNZ henc.1 henc.2.1 henc.2.2
  have hsHeq : sH = step sN := hrun.trans (runN_one sN hsNh hpcN)
  have hsHpc : sH.pc = 32768 := by rw [hsHeq, hhalt]
  have hsHh : sH.halted = false := by rw [hsHeq, hhalt]; exact hsNh
  have hsHZ : sH.mem.get 0 = 0 := by rw [hsHeq, hhalt]; exact hsNZ
  have hsHB : sH.mem.get 33 = 0 := by rw [hsHeq, hhalt]; exact hw.2.2.2.1
  have hsHI : sH.mem.get 29 = 1 := by rw [hsHeq, hhalt]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsHeq, hhalt]; exact hpresN a haB ha18 ha30 ha0
  exact ⟨hsHpc, hsHh, hsHZ, hsHB, hsHI, hpres⟩

/-- One more `runN` tick after the `HALT` instruction sets `halted`. -/
theorem write_nul_done_idx1 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 1)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 15
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 33 = 0 ∧
    sD.mem.get 29 = 1 ∧
    (∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hw := write_nul_halt_idx1 (s := s) hpc hh hZ hONE hI hcode
  let sH := runN s 14
  have hrun : sD = runN sH 1 := runN_add_eq s 14 1 15 (by decide)
  have hpcH : 32768 ≤ sH.pc.toNat := by
    have : sH.pc = 32768 := hw.1
    simp [this]
  have hsDeq : sD = { sH with halted := true } := by
    rw [hrun, runN_succ_halt sH 0 (Or.inr hpcH)]
  have hsDpc : sD.pc = 32768 := by rw [hsDeq]; exact hw.1
  have hsDh : sD.halted = true := by rw [hsDeq]
  have hsDZ : sD.mem.get 0 = 0 := by rw [hsDeq]; exact hw.2.2.1
  have hsDB : sD.mem.get 33 = 0 := by rw [hsDeq]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 1 := by rw [hsDeq]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsDeq]; exact hw.2.2.2.2.2 a haB ha18 ha30 ha0
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hpres⟩


/-- `AFTER_DIGS` with `LEN = 1 < CAP`, through `WRITE_NUL` and `DONE`, to a halted machine. 30 steps. -/
theorem after_digs_write_nul_done_len1 {s : Machine}
    (hpc : s.pc = 1905)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hL : s.mem.get 16 = 1)
    (hLlt : (1 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 30
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 33 = 0 ∧
    sD.mem.get 29 = 1 ∧
    sD.mem.get 16 = 1 ∧
    (∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hLlt' : (s.mem.get 16).toNat < (s.mem.get 13).toNat := by
    have : (s.mem.get 16).toNat = 1 := by simp [hL]
    omega
  have ha := after_digs_nul_at_len (s := s) hpc hh hZ hONE hLlt' hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s15 := runN s 15
  have hs15pc : s15.pc = 1971 := ha.1
  have hs15h : s15.halted = false := ha.2.1
  have hs15Z : s15.mem.get 0 = 0 := ha.2.2.1
  have hs15I : s15.mem.get 29 = 1 := ha.2.2.2.1.trans hL
  have hs15L : s15.mem.get 16 = 1 := ha.2.2.2.2.1.trans hL
  have hpres15 := ha.2.2.2.2.2.2
  have hONE15 : s15.mem.get 3 = 1 := (hpres15 3 (by decide) (by decide) (by decide)).trans hONE
  have g15 : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres15 (UInt16.ofNat k) n18 n29 n0).trans (hcode k (by omega) (by omega))
  have hw := write_nul_done_idx1 (s := s15) hs15pc hs15h hs15Z hONE15 hs15I g15
  have hrun : sD = runN s15 15 := runN_add_eq s 15 15 30 (by decide)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDB : sD.mem.get 33 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 1 := by rw [hrun]; exact hw.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2
  have hsDL : sD.mem.get 16 = 1 := by
    rw [hrun]
    have h16 : s15.mem.get 16 = 1 := hs15L
    exact (hpresw 16 (by decide) (by decide) (by decide) (by decide)).trans h16
  have hpres : ∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha29 ha0
    rw [hrun]
    exact (hpresw a haB ha18 ha30 ha0).trans (hpres15 a ha18 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hsDL, hpres⟩


/-- `WRITE_NUL` at `IDX = 2` plus the `HALT` at `DONE`: 16 steps, `pc = 32768`. -/
theorem write_nul_halt_idx2 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 2)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sH := runN s 16
    sH.pc = 32768 ∧
    sH.halted = false ∧
    sH.mem.get 0 = 0 ∧
    sH.mem.get 34 = 0 ∧
    sH.mem.get 29 = 2 ∧
    (∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a) := by
  intro sH
  have hw := write_nul_idx2 (s := s) hpc hh hZ hONE hI
    (fun k h1 h2 => hcode k h1 (by omega))
  let sN := runN s 15
  have hrun : sH = runN sN 1 := runN_add_eq s 15 1 16 (by decide)
  have hsNpc : sN.pc = 2316 := hw.1
  have hsNh : sN.halted = false := hw.2.1
  have hsNZ : sN.mem.get 0 = 0 := hw.2.2.1
  have hpresN := hw.2.2.2.2.2.2
  have gsN : ∀ k : Nat, 2316 ≤ k → k < 2319 →
      sN.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresN (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_halt_2316 (s := sN) hsNpc gsN
  have hpcN : sN.pc.toNat < 32768 := by simp [hsNpc]
  have hhalt :=
    step_HALT (s := sN) hsNh hpcN hsNZ henc.1 henc.2.1 henc.2.2
  have hsHeq : sH = step sN := hrun.trans (runN_one sN hsNh hpcN)
  have hsHpc : sH.pc = 32768 := by rw [hsHeq, hhalt]
  have hsHh : sH.halted = false := by rw [hsHeq, hhalt]; exact hsNh
  have hsHZ : sH.mem.get 0 = 0 := by rw [hsHeq, hhalt]; exact hsNZ
  have hsHB : sH.mem.get 34 = 0 := by rw [hsHeq, hhalt]; exact hw.2.2.2.1
  have hsHI : sH.mem.get 29 = 2 := by rw [hsHeq, hhalt]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsHeq, hhalt]; exact hpresN a haB ha18 ha30 ha0
  exact ⟨hsHpc, hsHh, hsHZ, hsHB, hsHI, hpres⟩

/-- One more `runN` tick after the `HALT` instruction sets `halted`. -/
theorem write_nul_done_idx2 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 2)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 17
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 34 = 0 ∧
    sD.mem.get 29 = 2 ∧
    (∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hw := write_nul_halt_idx2 (s := s) hpc hh hZ hONE hI hcode
  let sH := runN s 16
  have hrun : sD = runN sH 1 := runN_add_eq s 16 1 17 (by decide)
  have hpcH : 32768 ≤ sH.pc.toNat := by
    have : sH.pc = 32768 := hw.1
    simp [this]
  have hsDeq : sD = { sH with halted := true } := by
    rw [hrun, runN_succ_halt sH 0 (Or.inr hpcH)]
  have hsDpc : sD.pc = 32768 := by rw [hsDeq]; exact hw.1
  have hsDh : sD.halted = true := by rw [hsDeq]
  have hsDZ : sD.mem.get 0 = 0 := by rw [hsDeq]; exact hw.2.2.1
  have hsDB : sD.mem.get 34 = 0 := by rw [hsDeq]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 2 := by rw [hsDeq]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsDeq]; exact hw.2.2.2.2.2 a haB ha18 ha30 ha0
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hpres⟩


/-- `AFTER_DIGS` with `LEN = 2 < CAP`, through `WRITE_NUL` and `DONE`, to a halted machine. 32 steps. -/
theorem after_digs_write_nul_done_len2 {s : Machine}
    (hpc : s.pc = 1905)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hL : s.mem.get 16 = 2)
    (hLlt : (2 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 32
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 34 = 0 ∧
    sD.mem.get 29 = 2 ∧
    sD.mem.get 16 = 2 ∧
    (∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hLlt' : (s.mem.get 16).toNat < (s.mem.get 13).toNat := by
    have : (s.mem.get 16).toNat = 2 := by simp [hL]
    omega
  have ha := after_digs_nul_at_len (s := s) hpc hh hZ hONE hLlt' hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s15 := runN s 15
  have hs15pc : s15.pc = 1971 := ha.1
  have hs15h : s15.halted = false := ha.2.1
  have hs15Z : s15.mem.get 0 = 0 := ha.2.2.1
  have hs15I : s15.mem.get 29 = 2 := ha.2.2.2.1.trans hL
  have hs15L : s15.mem.get 16 = 2 := ha.2.2.2.2.1.trans hL
  have hpres15 := ha.2.2.2.2.2.2
  have hONE15 : s15.mem.get 3 = 1 := (hpres15 3 (by decide) (by decide) (by decide)).trans hONE
  have g15 : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres15 (UInt16.ofNat k) n18 n29 n0).trans (hcode k (by omega) (by omega))
  have hw := write_nul_done_idx2 (s := s15) hs15pc hs15h hs15Z hONE15 hs15I g15
  have hrun : sD = runN s15 17 := runN_add_eq s 15 17 32 (by decide)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDB : sD.mem.get 34 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 2 := by rw [hrun]; exact hw.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2
  have hsDL : sD.mem.get 16 = 2 := by
    rw [hrun]
    have h16 : s15.mem.get 16 = 2 := hs15L
    exact (hpresw 16 (by decide) (by decide) (by decide) (by decide)).trans h16
  have hpres : ∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha29 ha0
    rw [hrun]
    exact (hpresw a haB ha18 ha30 ha0).trans (hpres15 a ha18 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hsDL, hpres⟩


/-- `WRITE_NUL` at `IDX = 3` plus the `HALT` at `DONE`: 18 steps, `pc = 32768`. -/
theorem write_nul_halt_idx3 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 3)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sH := runN s 18
    sH.pc = 32768 ∧
    sH.halted = false ∧
    sH.mem.get 0 = 0 ∧
    sH.mem.get 35 = 0 ∧
    sH.mem.get 29 = 3 ∧
    (∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a) := by
  intro sH
  have hw := write_nul_idx3 (s := s) hpc hh hZ hONE hI
    (fun k h1 h2 => hcode k h1 (by omega))
  let sN := runN s 17
  have hrun : sH = runN sN 1 := runN_add_eq s 17 1 18 (by decide)
  have hsNpc : sN.pc = 2316 := hw.1
  have hsNh : sN.halted = false := hw.2.1
  have hsNZ : sN.mem.get 0 = 0 := hw.2.2.1
  have hpresN := hw.2.2.2.2.2.2
  have gsN : ∀ k : Nat, 2316 ≤ k → k < 2319 →
      sN.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresN (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_halt_2316 (s := sN) hsNpc gsN
  have hpcN : sN.pc.toNat < 32768 := by simp [hsNpc]
  have hhalt :=
    step_HALT (s := sN) hsNh hpcN hsNZ henc.1 henc.2.1 henc.2.2
  have hsHeq : sH = step sN := hrun.trans (runN_one sN hsNh hpcN)
  have hsHpc : sH.pc = 32768 := by rw [hsHeq, hhalt]
  have hsHh : sH.halted = false := by rw [hsHeq, hhalt]; exact hsNh
  have hsHZ : sH.mem.get 0 = 0 := by rw [hsHeq, hhalt]; exact hsNZ
  have hsHB : sH.mem.get 35 = 0 := by rw [hsHeq, hhalt]; exact hw.2.2.2.1
  have hsHI : sH.mem.get 29 = 3 := by rw [hsHeq, hhalt]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsHeq, hhalt]; exact hpresN a haB ha18 ha30 ha0
  exact ⟨hsHpc, hsHh, hsHZ, hsHB, hsHI, hpres⟩

/-- One more `runN` tick after the `HALT` instruction sets `halted`. -/
theorem write_nul_done_idx3 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 3)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 19
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 35 = 0 ∧
    sD.mem.get 29 = 3 ∧
    (∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hw := write_nul_halt_idx3 (s := s) hpc hh hZ hONE hI hcode
  let sH := runN s 18
  have hrun : sD = runN sH 1 := runN_add_eq s 18 1 19 (by decide)
  have hpcH : 32768 ≤ sH.pc.toNat := by
    have : sH.pc = 32768 := hw.1
    simp [this]
  have hsDeq : sD = { sH with halted := true } := by
    rw [hrun, runN_succ_halt sH 0 (Or.inr hpcH)]
  have hsDpc : sD.pc = 32768 := by rw [hsDeq]; exact hw.1
  have hsDh : sD.halted = true := by rw [hsDeq]
  have hsDZ : sD.mem.get 0 = 0 := by rw [hsDeq]; exact hw.2.2.1
  have hsDB : sD.mem.get 35 = 0 := by rw [hsDeq]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 3 := by rw [hsDeq]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsDeq]; exact hw.2.2.2.2.2 a haB ha18 ha30 ha0
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hpres⟩


/-- `AFTER_DIGS` with `LEN = 3 < CAP`, through `WRITE_NUL` and `DONE`, to a halted machine. 34 steps. -/
theorem after_digs_write_nul_done_len3 {s : Machine}
    (hpc : s.pc = 1905)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hL : s.mem.get 16 = 3)
    (hLlt : (3 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 34
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 35 = 0 ∧
    sD.mem.get 29 = 3 ∧
    sD.mem.get 16 = 3 ∧
    (∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hLlt' : (s.mem.get 16).toNat < (s.mem.get 13).toNat := by
    have : (s.mem.get 16).toNat = 3 := by simp [hL]
    omega
  have ha := after_digs_nul_at_len (s := s) hpc hh hZ hONE hLlt' hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s15 := runN s 15
  have hs15pc : s15.pc = 1971 := ha.1
  have hs15h : s15.halted = false := ha.2.1
  have hs15Z : s15.mem.get 0 = 0 := ha.2.2.1
  have hs15I : s15.mem.get 29 = 3 := ha.2.2.2.1.trans hL
  have hs15L : s15.mem.get 16 = 3 := ha.2.2.2.2.1.trans hL
  have hpres15 := ha.2.2.2.2.2.2
  have hONE15 : s15.mem.get 3 = 1 := (hpres15 3 (by decide) (by decide) (by decide)).trans hONE
  have g15 : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres15 (UInt16.ofNat k) n18 n29 n0).trans (hcode k (by omega) (by omega))
  have hw := write_nul_done_idx3 (s := s15) hs15pc hs15h hs15Z hONE15 hs15I g15
  have hrun : sD = runN s15 19 := runN_add_eq s 15 19 34 (by decide)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDB : sD.mem.get 35 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 3 := by rw [hrun]; exact hw.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2
  have hsDL : sD.mem.get 16 = 3 := by
    rw [hrun]
    have h16 : s15.mem.get 16 = 3 := hs15L
    exact (hpresw 16 (by decide) (by decide) (by decide) (by decide)).trans h16
  have hpres : ∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha29 ha0
    rw [hrun]
    exact (hpresw a haB ha18 ha30 ha0).trans (hpres15 a ha18 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hsDL, hpres⟩


/-- `WRITE_NUL` at `IDX = 4` plus the `HALT` at `DONE`: 20 steps, `pc = 32768`. -/
theorem write_nul_halt_idx4 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 4)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sH := runN s 20
    sH.pc = 32768 ∧
    sH.halted = false ∧
    sH.mem.get 0 = 0 ∧
    sH.mem.get 36 = 0 ∧
    sH.mem.get 29 = 4 ∧
    (∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a) := by
  intro sH
  have hw := write_nul_idx4 (s := s) hpc hh hZ hONE hI
    (fun k h1 h2 => hcode k h1 (by omega))
  let sN := runN s 19
  have hrun : sH = runN sN 1 := runN_add_eq s 19 1 20 (by decide)
  have hsNpc : sN.pc = 2316 := hw.1
  have hsNh : sN.halted = false := hw.2.1
  have hsNZ : sN.mem.get 0 = 0 := hw.2.2.1
  have hpresN := hw.2.2.2.2.2.2
  have gsN : ∀ k : Nat, 2316 ≤ k → k < 2319 →
      sN.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresN (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_halt_2316 (s := sN) hsNpc gsN
  have hpcN : sN.pc.toNat < 32768 := by simp [hsNpc]
  have hhalt :=
    step_HALT (s := sN) hsNh hpcN hsNZ henc.1 henc.2.1 henc.2.2
  have hsHeq : sH = step sN := hrun.trans (runN_one sN hsNh hpcN)
  have hsHpc : sH.pc = 32768 := by rw [hsHeq, hhalt]
  have hsHh : sH.halted = false := by rw [hsHeq, hhalt]; exact hsNh
  have hsHZ : sH.mem.get 0 = 0 := by rw [hsHeq, hhalt]; exact hsNZ
  have hsHB : sH.mem.get 36 = 0 := by rw [hsHeq, hhalt]; exact hw.2.2.2.1
  have hsHI : sH.mem.get 29 = 4 := by rw [hsHeq, hhalt]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsHeq, hhalt]; exact hpresN a haB ha18 ha30 ha0
  exact ⟨hsHpc, hsHh, hsHZ, hsHB, hsHI, hpres⟩

/-- One more `runN` tick after the `HALT` instruction sets `halted`. -/
theorem write_nul_done_idx4 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 4)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 21
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 36 = 0 ∧
    sD.mem.get 29 = 4 ∧
    (∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hw := write_nul_halt_idx4 (s := s) hpc hh hZ hONE hI hcode
  let sH := runN s 20
  have hrun : sD = runN sH 1 := runN_add_eq s 20 1 21 (by decide)
  have hpcH : 32768 ≤ sH.pc.toNat := by
    have : sH.pc = 32768 := hw.1
    simp [this]
  have hsDeq : sD = { sH with halted := true } := by
    rw [hrun, runN_succ_halt sH 0 (Or.inr hpcH)]
  have hsDpc : sD.pc = 32768 := by rw [hsDeq]; exact hw.1
  have hsDh : sD.halted = true := by rw [hsDeq]
  have hsDZ : sD.mem.get 0 = 0 := by rw [hsDeq]; exact hw.2.2.1
  have hsDB : sD.mem.get 36 = 0 := by rw [hsDeq]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 4 := by rw [hsDeq]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsDeq]; exact hw.2.2.2.2.2 a haB ha18 ha30 ha0
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hpres⟩


/-- `AFTER_DIGS` with `LEN = 4 < CAP`, through `WRITE_NUL` and `DONE`, to a halted machine. 36 steps. -/
theorem after_digs_write_nul_done_len4 {s : Machine}
    (hpc : s.pc = 1905)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hL : s.mem.get 16 = 4)
    (hLlt : (4 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 36
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 36 = 0 ∧
    sD.mem.get 29 = 4 ∧
    sD.mem.get 16 = 4 ∧
    (∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hLlt' : (s.mem.get 16).toNat < (s.mem.get 13).toNat := by
    have : (s.mem.get 16).toNat = 4 := by simp [hL]
    omega
  have ha := after_digs_nul_at_len (s := s) hpc hh hZ hONE hLlt' hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s15 := runN s 15
  have hs15pc : s15.pc = 1971 := ha.1
  have hs15h : s15.halted = false := ha.2.1
  have hs15Z : s15.mem.get 0 = 0 := ha.2.2.1
  have hs15I : s15.mem.get 29 = 4 := ha.2.2.2.1.trans hL
  have hs15L : s15.mem.get 16 = 4 := ha.2.2.2.2.1.trans hL
  have hpres15 := ha.2.2.2.2.2.2
  have hONE15 : s15.mem.get 3 = 1 := (hpres15 3 (by decide) (by decide) (by decide)).trans hONE
  have g15 : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres15 (UInt16.ofNat k) n18 n29 n0).trans (hcode k (by omega) (by omega))
  have hw := write_nul_done_idx4 (s := s15) hs15pc hs15h hs15Z hONE15 hs15I g15
  have hrun : sD = runN s15 21 := runN_add_eq s 15 21 36 (by decide)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDB : sD.mem.get 36 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 4 := by rw [hrun]; exact hw.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2
  have hsDL : sD.mem.get 16 = 4 := by
    rw [hrun]
    have h16 : s15.mem.get 16 = 4 := hs15L
    exact (hpresw 16 (by decide) (by decide) (by decide) (by decide)).trans h16
  have hpres : ∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha29 ha0
    rw [hrun]
    exact (hpresw a haB ha18 ha30 ha0).trans (hpres15 a ha18 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hsDL, hpres⟩


/-- `WRITE_NUL` at `IDX = 5` plus the `HALT` at `DONE`: 22 steps, `pc = 32768`. -/
theorem write_nul_halt_idx5 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 5)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sH := runN s 22
    sH.pc = 32768 ∧
    sH.halted = false ∧
    sH.mem.get 0 = 0 ∧
    sH.mem.get 37 = 0 ∧
    sH.mem.get 29 = 5 ∧
    (∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a) := by
  intro sH
  have hw := write_nul_idx5 (s := s) hpc hh hZ hONE hI
    (fun k h1 h2 => hcode k h1 (by omega))
  let sN := runN s 21
  have hrun : sH = runN sN 1 := runN_add_eq s 21 1 22 (by decide)
  have hsNpc : sN.pc = 2316 := hw.1
  have hsNh : sN.halted = false := hw.2.1
  have hsNZ : sN.mem.get 0 = 0 := hw.2.2.1
  have hpresN := hw.2.2.2.2.2.2
  have gsN : ∀ k : Nat, 2316 ≤ k → k < 2319 →
      sN.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresN (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_halt_2316 (s := sN) hsNpc gsN
  have hpcN : sN.pc.toNat < 32768 := by simp [hsNpc]
  have hhalt :=
    step_HALT (s := sN) hsNh hpcN hsNZ henc.1 henc.2.1 henc.2.2
  have hsHeq : sH = step sN := hrun.trans (runN_one sN hsNh hpcN)
  have hsHpc : sH.pc = 32768 := by rw [hsHeq, hhalt]
  have hsHh : sH.halted = false := by rw [hsHeq, hhalt]; exact hsNh
  have hsHZ : sH.mem.get 0 = 0 := by rw [hsHeq, hhalt]; exact hsNZ
  have hsHB : sH.mem.get 37 = 0 := by rw [hsHeq, hhalt]; exact hw.2.2.2.1
  have hsHI : sH.mem.get 29 = 5 := by rw [hsHeq, hhalt]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsHeq, hhalt]; exact hpresN a haB ha18 ha30 ha0
  exact ⟨hsHpc, hsHh, hsHZ, hsHB, hsHI, hpres⟩

/-- One more `runN` tick after the `HALT` instruction sets `halted`. -/
theorem write_nul_done_idx5 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 5)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 23
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 37 = 0 ∧
    sD.mem.get 29 = 5 ∧
    (∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hw := write_nul_halt_idx5 (s := s) hpc hh hZ hONE hI hcode
  let sH := runN s 22
  have hrun : sD = runN sH 1 := runN_add_eq s 22 1 23 (by decide)
  have hpcH : 32768 ≤ sH.pc.toNat := by
    have : sH.pc = 32768 := hw.1
    simp [this]
  have hsDeq : sD = { sH with halted := true } := by
    rw [hrun, runN_succ_halt sH 0 (Or.inr hpcH)]
  have hsDpc : sD.pc = 32768 := by rw [hsDeq]; exact hw.1
  have hsDh : sD.halted = true := by rw [hsDeq]
  have hsDZ : sD.mem.get 0 = 0 := by rw [hsDeq]; exact hw.2.2.1
  have hsDB : sD.mem.get 37 = 0 := by rw [hsDeq]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 5 := by rw [hsDeq]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsDeq]; exact hw.2.2.2.2.2 a haB ha18 ha30 ha0
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hpres⟩


/-- `AFTER_DIGS` with `LEN = 5 < CAP`, through `WRITE_NUL` and `DONE`, to a halted machine. 38 steps. -/
theorem after_digs_write_nul_done_len5 {s : Machine}
    (hpc : s.pc = 1905)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hL : s.mem.get 16 = 5)
    (hLlt : (5 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 38
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 37 = 0 ∧
    sD.mem.get 29 = 5 ∧
    sD.mem.get 16 = 5 ∧
    (∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hLlt' : (s.mem.get 16).toNat < (s.mem.get 13).toNat := by
    have : (s.mem.get 16).toNat = 5 := by simp [hL]
    omega
  have ha := after_digs_nul_at_len (s := s) hpc hh hZ hONE hLlt' hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s15 := runN s 15
  have hs15pc : s15.pc = 1971 := ha.1
  have hs15h : s15.halted = false := ha.2.1
  have hs15Z : s15.mem.get 0 = 0 := ha.2.2.1
  have hs15I : s15.mem.get 29 = 5 := ha.2.2.2.1.trans hL
  have hs15L : s15.mem.get 16 = 5 := ha.2.2.2.2.1.trans hL
  have hpres15 := ha.2.2.2.2.2.2
  have hONE15 : s15.mem.get 3 = 1 := (hpres15 3 (by decide) (by decide) (by decide)).trans hONE
  have g15 : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres15 (UInt16.ofNat k) n18 n29 n0).trans (hcode k (by omega) (by omega))
  have hw := write_nul_done_idx5 (s := s15) hs15pc hs15h hs15Z hONE15 hs15I g15
  have hrun : sD = runN s15 23 := runN_add_eq s 15 23 38 (by decide)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDB : sD.mem.get 37 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 5 := by rw [hrun]; exact hw.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2
  have hsDL : sD.mem.get 16 = 5 := by
    rw [hrun]
    have h16 : s15.mem.get 16 = 5 := hs15L
    exact (hpresw 16 (by decide) (by decide) (by decide) (by decide)).trans h16
  have hpres : ∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha29 ha0
    rw [hrun]
    exact (hpresw a haB ha18 ha30 ha0).trans (hpres15 a ha18 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hsDL, hpres⟩


/-- `WRITE_NUL` at `IDX = 6` plus the `HALT` at `DONE`: 24 steps, `pc = 32768`. -/
theorem write_nul_halt_idx6 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 6)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sH := runN s 24
    sH.pc = 32768 ∧
    sH.halted = false ∧
    sH.mem.get 0 = 0 ∧
    sH.mem.get 38 = 0 ∧
    sH.mem.get 29 = 6 ∧
    (∀ a, a ≠ 38 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a) := by
  intro sH
  have hw := write_nul_idx6 (s := s) hpc hh hZ hONE hI
    (fun k h1 h2 => hcode k h1 (by omega))
  let sN := runN s 23
  have hrun : sH = runN sN 1 := runN_add_eq s 23 1 24 (by decide)
  have hsNpc : sN.pc = 2316 := hw.1
  have hsNh : sN.halted = false := hw.2.1
  have hsNZ : sN.mem.get 0 = 0 := hw.2.2.1
  have hpresN := hw.2.2.2.2.2.2
  have gsN : ∀ k : Nat, 2316 ≤ k → k < 2319 →
      sN.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (38 : Word) := by
      have : (38 : Word) = UInt16.ofNat 38 := rfl
      rw [this]; exact ofNat_ne k 38 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresN (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_halt_2316 (s := sN) hsNpc gsN
  have hpcN : sN.pc.toNat < 32768 := by simp [hsNpc]
  have hhalt :=
    step_HALT (s := sN) hsNh hpcN hsNZ henc.1 henc.2.1 henc.2.2
  have hsHeq : sH = step sN := hrun.trans (runN_one sN hsNh hpcN)
  have hsHpc : sH.pc = 32768 := by rw [hsHeq, hhalt]
  have hsHh : sH.halted = false := by rw [hsHeq, hhalt]; exact hsNh
  have hsHZ : sH.mem.get 0 = 0 := by rw [hsHeq, hhalt]; exact hsNZ
  have hsHB : sH.mem.get 38 = 0 := by rw [hsHeq, hhalt]; exact hw.2.2.2.1
  have hsHI : sH.mem.get 29 = 6 := by rw [hsHeq, hhalt]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 38 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsHeq, hhalt]; exact hpresN a haB ha18 ha30 ha0
  exact ⟨hsHpc, hsHh, hsHZ, hsHB, hsHI, hpres⟩

/-- One more `runN` tick after the `HALT` instruction sets `halted`. -/
theorem write_nul_done_idx6 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 6)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 25
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 38 = 0 ∧
    sD.mem.get 29 = 6 ∧
    (∀ a, a ≠ 38 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hw := write_nul_halt_idx6 (s := s) hpc hh hZ hONE hI hcode
  let sH := runN s 24
  have hrun : sD = runN sH 1 := runN_add_eq s 24 1 25 (by decide)
  have hpcH : 32768 ≤ sH.pc.toNat := by
    have : sH.pc = 32768 := hw.1
    simp [this]
  have hsDeq : sD = { sH with halted := true } := by
    rw [hrun, runN_succ_halt sH 0 (Or.inr hpcH)]
  have hsDpc : sD.pc = 32768 := by rw [hsDeq]; exact hw.1
  have hsDh : sD.halted = true := by rw [hsDeq]
  have hsDZ : sD.mem.get 0 = 0 := by rw [hsDeq]; exact hw.2.2.1
  have hsDB : sD.mem.get 38 = 0 := by rw [hsDeq]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 6 := by rw [hsDeq]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 38 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsDeq]; exact hw.2.2.2.2.2 a haB ha18 ha30 ha0
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hpres⟩


/-- `AFTER_DIGS` with `LEN = 6 < CAP`, through `WRITE_NUL` and `DONE`, to a halted machine. 40 steps. -/
theorem after_digs_write_nul_done_len6 {s : Machine}
    (hpc : s.pc = 1905)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hL : s.mem.get 16 = 6)
    (hLlt : (6 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 40
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 38 = 0 ∧
    sD.mem.get 29 = 6 ∧
    sD.mem.get 16 = 6 ∧
    (∀ a, a ≠ 38 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hLlt' : (s.mem.get 16).toNat < (s.mem.get 13).toNat := by
    have : (s.mem.get 16).toNat = 6 := by simp [hL]
    omega
  have ha := after_digs_nul_at_len (s := s) hpc hh hZ hONE hLlt' hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s15 := runN s 15
  have hs15pc : s15.pc = 1971 := ha.1
  have hs15h : s15.halted = false := ha.2.1
  have hs15Z : s15.mem.get 0 = 0 := ha.2.2.1
  have hs15I : s15.mem.get 29 = 6 := ha.2.2.2.1.trans hL
  have hs15L : s15.mem.get 16 = 6 := ha.2.2.2.2.1.trans hL
  have hpres15 := ha.2.2.2.2.2.2
  have hONE15 : s15.mem.get 3 = 1 := (hpres15 3 (by decide) (by decide) (by decide)).trans hONE
  have g15 : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres15 (UInt16.ofNat k) n18 n29 n0).trans (hcode k (by omega) (by omega))
  have hw := write_nul_done_idx6 (s := s15) hs15pc hs15h hs15Z hONE15 hs15I g15
  have hrun : sD = runN s15 25 := runN_add_eq s 15 25 40 (by decide)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDB : sD.mem.get 38 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 6 := by rw [hrun]; exact hw.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2
  have hsDL : sD.mem.get 16 = 6 := by
    rw [hrun]
    have h16 : s15.mem.get 16 = 6 := hs15L
    exact (hpresw 16 (by decide) (by decide) (by decide) (by decide)).trans h16
  have hpres : ∀ a, a ≠ 38 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha29 ha0
    rw [hrun]
    exact (hpresw a haB ha18 ha30 ha0).trans (hpres15 a ha18 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hsDL, hpres⟩


/-- `WRITE_NUL` at `IDX = 7` plus the `HALT` at `DONE`: 26 steps, `pc = 32768`. -/
theorem write_nul_halt_idx7 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 7)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sH := runN s 26
    sH.pc = 32768 ∧
    sH.halted = false ∧
    sH.mem.get 0 = 0 ∧
    sH.mem.get 39 = 0 ∧
    sH.mem.get 29 = 7 ∧
    (∀ a, a ≠ 39 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a) := by
  intro sH
  have hw := write_nul_idx7 (s := s) hpc hh hZ hONE hI
    (fun k h1 h2 => hcode k h1 (by omega))
  let sN := runN s 25
  have hrun : sH = runN sN 1 := runN_add_eq s 25 1 26 (by decide)
  have hsNpc : sN.pc = 2316 := hw.1
  have hsNh : sN.halted = false := hw.2.1
  have hsNZ : sN.mem.get 0 = 0 := hw.2.2.1
  have hpresN := hw.2.2.2.2.2.2
  have gsN : ∀ k : Nat, 2316 ≤ k → k < 2319 →
      sN.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nB : UInt16.ofNat k ≠ (39 : Word) := by
      have : (39 : Word) = UInt16.ofNat 39 := rfl
      rw [this]; exact ofNat_ne k 39 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresN (UInt16.ofNat k) nB n18 n30 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_halt_2316 (s := sN) hsNpc gsN
  have hpcN : sN.pc.toNat < 32768 := by simp [hsNpc]
  have hhalt :=
    step_HALT (s := sN) hsNh hpcN hsNZ henc.1 henc.2.1 henc.2.2
  have hsHeq : sH = step sN := hrun.trans (runN_one sN hsNh hpcN)
  have hsHpc : sH.pc = 32768 := by rw [hsHeq, hhalt]
  have hsHh : sH.halted = false := by rw [hsHeq, hhalt]; exact hsNh
  have hsHZ : sH.mem.get 0 = 0 := by rw [hsHeq, hhalt]; exact hsNZ
  have hsHB : sH.mem.get 39 = 0 := by rw [hsHeq, hhalt]; exact hw.2.2.2.1
  have hsHI : sH.mem.get 29 = 7 := by rw [hsHeq, hhalt]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 39 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sH.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsHeq, hhalt]; exact hpresN a haB ha18 ha30 ha0
  exact ⟨hsHpc, hsHh, hsHZ, hsHB, hsHI, hpres⟩

/-- One more `runN` tick after the `HALT` instruction sets `halted`. -/
theorem write_nul_done_idx7 {s : Machine}
    (hpc : s.pc = 1971)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 7)
    (hcode : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 27
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 39 = 0 ∧
    sD.mem.get 29 = 7 ∧
    (∀ a, a ≠ 39 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hw := write_nul_halt_idx7 (s := s) hpc hh hZ hONE hI hcode
  let sH := runN s 26
  have hrun : sD = runN sH 1 := runN_add_eq s 26 1 27 (by decide)
  have hpcH : 32768 ≤ sH.pc.toNat := by
    have : sH.pc = 32768 := hw.1
    simp [this]
  have hsDeq : sD = { sH with halted := true } := by
    rw [hrun, runN_succ_halt sH 0 (Or.inr hpcH)]
  have hsDpc : sD.pc = 32768 := by rw [hsDeq]; exact hw.1
  have hsDh : sD.halted = true := by rw [hsDeq]
  have hsDZ : sD.mem.get 0 = 0 := by rw [hsDeq]; exact hw.2.2.1
  have hsDB : sD.mem.get 39 = 0 := by rw [hsDeq]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 7 := by rw [hsDeq]; exact hw.2.2.2.2.1
  have hpres : ∀ a, a ≠ 39 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    rw [hsDeq]; exact hw.2.2.2.2.2 a haB ha18 ha30 ha0
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hpres⟩


/-- `AFTER_DIGS` with `LEN = 7 < CAP`, through `WRITE_NUL` and `DONE`, to a halted machine. 42 steps. -/
theorem after_digs_write_nul_done_len7 {s : Machine}
    (hpc : s.pc = 1905)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hL : s.mem.get 16 = 7)
    (hLlt : (7 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 42
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 39 = 0 ∧
    sD.mem.get 29 = 7 ∧
    sD.mem.get 16 = 7 ∧
    (∀ a, a ≠ 39 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hLlt' : (s.mem.get 16).toNat < (s.mem.get 13).toNat := by
    have : (s.mem.get 16).toNat = 7 := by simp [hL]
    omega
  have ha := after_digs_nul_at_len (s := s) hpc hh hZ hONE hLlt' hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s15 := runN s 15
  have hs15pc : s15.pc = 1971 := ha.1
  have hs15h : s15.halted = false := ha.2.1
  have hs15Z : s15.mem.get 0 = 0 := ha.2.2.1
  have hs15I : s15.mem.get 29 = 7 := ha.2.2.2.1.trans hL
  have hs15L : s15.mem.get 16 = 7 := ha.2.2.2.2.1.trans hL
  have hpres15 := ha.2.2.2.2.2.2
  have hONE15 : s15.mem.get 3 = 1 := (hpres15 3 (by decide) (by decide) (by decide)).trans hONE
  have g15 : ∀ k : Nat, 1971 ≤ k → k < 2319 →
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres15 (UInt16.ofNat k) n18 n29 n0).trans (hcode k (by omega) (by omega))
  have hw := write_nul_done_idx7 (s := s15) hs15pc hs15h hs15Z hONE15 hs15I g15
  have hrun : sD = runN s15 27 := runN_add_eq s 15 27 42 (by decide)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDB : sD.mem.get 39 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 7 := by rw [hrun]; exact hw.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2
  have hsDL : sD.mem.get 16 = 7 := by
    rw [hrun]
    have h16 : s15.mem.get 16 = 7 := hs15L
    exact (hpresw 16 (by decide) (by decide) (by decide) (by decide)).trans h16
  have hpres : ∀ a, a ≠ 39 → a ≠ 18 → a ≠ 30 → a ≠ 29 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha29 ha0
    rw [hrun]
    exact (hpresw a haB ha18 ha30 ha0).trans (hpres15 a ha18 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsDB, hsDI, hsDL, hpres⟩


/-- `EMIT_DIGS` with `NDIG = 1` and `IDX = 0`, then `AFTER_DIGS`/`WRITE_NUL`/`DONE`
when `LEN = 1 < CAP`. 248 steps to a halted machine with NUL at `BUF+1`. -/
theorem emit_ndig1_idx0_write_nul_done {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 1)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 1)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (1 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 248
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 24 ∧
    sD.mem.get 33 = 0 ∧
    sD.mem.get 29 = 1 ∧
    sD.mem.get 16 = 1 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have he := emit_ndig1_idx0 (s := s) hpc hh hZ hONE hK5 hN hI hRlo hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sE := runN s 218
  have hsEpc : sE.pc = 1905 := he.1
  have hsEh : sE.halted = false := he.2.1
  have hsEZ : sE.mem.get 0 = 0 := he.2.2.1
  have hpresE := he.2.2.2.2.2
  have hONE_E : sE.mem.get 3 = 1 := (hpresE 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hL_E : sE.mem.get 16 = 1 := (hpresE 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hC_E : sE.mem.get 13 = s.mem.get 13 := hpresE 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hLlt_E : (1 : Nat) < (sE.mem.get 13).toNat := by
    rw [hC_E]; exact hLlt
  have hChi_E : (sE.mem.get 13).toNat < 32768 := by
    rw [hC_E]; exact hChi
  have gE : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      sE.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresE (UInt16.ofNat k) n32 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hw := after_digs_write_nul_done_len1 (s := sE) hsEpc hsEh hsEZ hONE_E hL_E hLlt_E hChi_E gE
  have hrun : sD = runN sE 30 := runN_add_eq s 218 30 248 (by decide)
  have hpresw := hw.2.2.2.2.2.2
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD32 : sD.mem.get 32 = s.mem.get 24 := by
    rw [hrun]
    exact (hpresw 32 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.1)
  have hsDNUL : sD.mem.get 33 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 1 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 1 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha33 ha18 ha30 ha29 ha0).trans
      (hpresE a ha32 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsDNUL, hsDI, hsDL, hpres⟩


/-- `EMIT_DIGS` with `NDIG = 1` and `IDX = 1`, then `AFTER_DIGS`/`WRITE_NUL`/`DONE`
when `LEN = 2 < CAP`. 252 steps to a halted machine with NUL at `BUF+2`. -/
theorem emit_ndig1_idx1_write_nul_done {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 1)
    (hI : s.mem.get 29 = 1)
    (hL : s.mem.get 16 = 2)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (2 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 252
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 33 = s.mem.get 24 ∧
    sD.mem.get 34 = 0 ∧
    sD.mem.get 29 = 2 ∧
    sD.mem.get 16 = 2 ∧
    (∀ a, a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have he := emit_ndig1_idx1 (s := s) hpc hh hZ hONE hK5 hN hI hRlo hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sE := runN s 220
  have hsEpc : sE.pc = 1905 := he.1
  have hsEh : sE.halted = false := he.2.1
  have hsEZ : sE.mem.get 0 = 0 := he.2.2.1
  have hpresE := he.2.2.2.2.2
  have hONE_E : sE.mem.get 3 = 1 := (hpresE 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hL_E : sE.mem.get 16 = 2 := (hpresE 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hC_E : sE.mem.get 13 = s.mem.get 13 := hpresE 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hLlt_E : (2 : Nat) < (sE.mem.get 13).toNat := by
    rw [hC_E]; exact hLlt
  have hChi_E : (sE.mem.get 13).toNat < 32768 := by
    rw [hC_E]; exact hChi
  have gE : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      sE.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresE (UInt16.ofNat k) n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hw := after_digs_write_nul_done_len2 (s := sE) hsEpc hsEh hsEZ hONE_E hL_E hLlt_E hChi_E gE
  have hrun : sD = runN sE 32 := runN_add_eq s 220 32 252 (by decide)
  have hpresw := hw.2.2.2.2.2.2
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 24 := by
    rw [hrun]
    exact (hpresw 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.1)
  have hsDNUL : sD.mem.get 34 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 2 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 2 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha33 ha34 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha34 ha18 ha30 ha29 ha0).trans
      (hpresE a ha33 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD33, hsDNUL, hsDI, hsDL, hpres⟩


/-- `EMIT_DIGS` with `NDIG = 2` and `IDX = 0`, then `AFTER_DIGS`/`WRITE_NUL`/`DONE`
when `LEN = 2 < CAP`. 308 steps to a halted machine with NUL at `BUF+2`. -/
theorem emit_ndig2_idx0_write_nul_done {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 2)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 2)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (2 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 308
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 23 ∧
    sD.mem.get 33 = s.mem.get 24 ∧
    sD.mem.get 34 = 0 ∧
    sD.mem.get 29 = 2 ∧
    sD.mem.get 16 = 2 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have he := emit_ndig2_idx0 (s := s) hpc hh hZ hONE hK5 hN hI hRlo hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sE := runN s 276
  have hsEpc : sE.pc = 1905 := he.1
  have hsEh : sE.halted = false := he.2.1
  have hsEZ : sE.mem.get 0 = 0 := he.2.2.1
  have hpresE := he.2.2.2.2.2.2
  have hONE_E : sE.mem.get 3 = 1 := (hpresE 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hL_E : sE.mem.get 16 = 2 := (hpresE 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hC_E : sE.mem.get 13 = s.mem.get 13 := hpresE 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hLlt_E : (2 : Nat) < (sE.mem.get 13).toNat := by
    rw [hC_E]; exact hLlt
  have hChi_E : (sE.mem.get 13).toNat < 32768 := by
    rw [hC_E]; exact hChi
  have gE : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      sE.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
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
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresE (UInt16.ofNat k) n32 n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hw := after_digs_write_nul_done_len2 (s := sE) hsEpc hsEh hsEZ hONE_E hL_E hLlt_E hChi_E gE
  have hrun : sD = runN sE 32 := runN_add_eq s 276 32 308 (by decide)
  have hpresw := hw.2.2.2.2.2.2
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD32 : sD.mem.get 32 = s.mem.get 23 := by
    rw [hrun]
    exact (hpresw 32 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.1)
  have hsD33 : sD.mem.get 33 = s.mem.get 24 := by
    rw [hrun]
    exact (hpresw 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.1)
  have hsDNUL : sD.mem.get 34 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 2 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 2 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha34 ha18 ha30 ha29 ha0).trans
      (hpresE a ha32 ha33 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsDNUL, hsDI, hsDL, hpres⟩


/-- `EMIT_DIGS` with `NDIG = 2` and `IDX = 1`, then `AFTER_DIGS`/`WRITE_NUL`/`DONE`
when `LEN = 3 < CAP`. 314 steps to a halted machine with NUL at `BUF+3`. -/
theorem emit_ndig2_idx1_write_nul_done {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 2)
    (hI : s.mem.get 29 = 1)
    (hL : s.mem.get 16 = 3)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (3 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 314
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 33 = s.mem.get 23 ∧
    sD.mem.get 34 = s.mem.get 24 ∧
    sD.mem.get 35 = 0 ∧
    sD.mem.get 29 = 3 ∧
    sD.mem.get 16 = 3 ∧
    (∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have he := emit_ndig2_idx1 (s := s) hpc hh hZ hONE hK5 hN hI hRlo hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sE := runN s 280
  have hsEpc : sE.pc = 1905 := he.1
  have hsEh : sE.halted = false := he.2.1
  have hsEZ : sE.mem.get 0 = 0 := he.2.2.1
  have hpresE := he.2.2.2.2.2.2
  have hONE_E : sE.mem.get 3 = 1 := (hpresE 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hL_E : sE.mem.get 16 = 3 := (hpresE 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hC_E : sE.mem.get 13 = s.mem.get 13 := hpresE 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hLlt_E : (3 : Nat) < (sE.mem.get 13).toNat := by
    rw [hC_E]; exact hLlt
  have hChi_E : (sE.mem.get 13).toNat < 32768 := by
    rw [hC_E]; exact hChi
  have gE : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      sE.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
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
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresE (UInt16.ofNat k) n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hw := after_digs_write_nul_done_len3 (s := sE) hsEpc hsEh hsEZ hONE_E hL_E hLlt_E hChi_E gE
  have hrun : sD = runN sE 34 := runN_add_eq s 280 34 314 (by decide)
  have hpresw := hw.2.2.2.2.2.2
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 23 := by
    rw [hrun]
    exact (hpresw 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.1)
  have hsD34 : sD.mem.get 34 = s.mem.get 24 := by
    rw [hrun]
    exact (hpresw 34 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.1)
  have hsDNUL : sD.mem.get 35 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 3 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 3 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha33 ha34 ha35 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha35 ha18 ha30 ha29 ha0).trans
      (hpresE a ha33 ha34 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD33, hsD34, hsDNUL, hsDI, hsDL, hpres⟩


/-- `EMIT_DIGS` with `NDIG = 3` and `IDX = 0`, then `AFTER_DIGS`/`WRITE_NUL`/`DONE`
when `LEN = 3 < CAP`. 368 steps to a halted machine with NUL at `BUF+3`. -/
theorem emit_ndig3_idx0_write_nul_done {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 3)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 3)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (3 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 368
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 22 ∧
    sD.mem.get 33 = s.mem.get 23 ∧
    sD.mem.get 34 = s.mem.get 24 ∧
    sD.mem.get 35 = 0 ∧
    sD.mem.get 29 = 3 ∧
    sD.mem.get 16 = 3 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have he := emit_ndig3_idx0 (s := s) hpc hh hZ hONE hK5 hN hI hRlo hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sE := runN s 334
  have hsEpc : sE.pc = 1905 := he.1
  have hsEh : sE.halted = false := he.2.1
  have hsEZ : sE.mem.get 0 = 0 := he.2.2.1
  have hpresE := he.2.2.2.2.2.2.2
  have hONE_E : sE.mem.get 3 = 1 := (hpresE 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hL_E : sE.mem.get 16 = 3 := (hpresE 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hC_E : sE.mem.get 13 = s.mem.get 13 := hpresE 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hLlt_E : (3 : Nat) < (sE.mem.get 13).toNat := by
    rw [hC_E]; exact hLlt
  have hChi_E : (sE.mem.get 13).toNat < 32768 := by
    rw [hC_E]; exact hChi
  have gE : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      sE.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
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
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresE (UInt16.ofNat k) n32 n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hw := after_digs_write_nul_done_len3 (s := sE) hsEpc hsEh hsEZ hONE_E hL_E hLlt_E hChi_E gE
  have hrun : sD = runN sE 34 := runN_add_eq s 334 34 368 (by decide)
  have hpresw := hw.2.2.2.2.2.2
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD32 : sD.mem.get 32 = s.mem.get 22 := by
    rw [hrun]
    exact (hpresw 32 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.1)
  have hsD33 : sD.mem.get 33 = s.mem.get 23 := by
    rw [hrun]
    exact (hpresw 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.1)
  have hsD34 : sD.mem.get 34 = s.mem.get 24 := by
    rw [hrun]
    exact (hpresw 34 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.2.1)
  have hsDNUL : sD.mem.get 35 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 3 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 3 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha35 ha18 ha30 ha29 ha0).trans
      (hpresE a ha32 ha33 ha34 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsDNUL, hsDI, hsDL, hpres⟩


/-- `EMIT_DIGS` with `NDIG = 3` and `IDX = 1`, then `AFTER_DIGS`/`WRITE_NUL`/`DONE`
when `LEN = 4 < CAP`. 376 steps to a halted machine with NUL at `BUF+4`. -/
theorem emit_ndig3_idx1_write_nul_done {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 3)
    (hI : s.mem.get 29 = 1)
    (hL : s.mem.get 16 = 4)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (4 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 376
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 33 = s.mem.get 22 ∧
    sD.mem.get 34 = s.mem.get 23 ∧
    sD.mem.get 35 = s.mem.get 24 ∧
    sD.mem.get 36 = 0 ∧
    sD.mem.get 29 = 4 ∧
    sD.mem.get 16 = 4 ∧
    (∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have he := emit_ndig3_idx1 (s := s) hpc hh hZ hONE hK5 hN hI hRlo hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sE := runN s 340
  have hsEpc : sE.pc = 1905 := he.1
  have hsEh : sE.halted = false := he.2.1
  have hsEZ : sE.mem.get 0 = 0 := he.2.2.1
  have hpresE := he.2.2.2.2.2.2.2
  have hONE_E : sE.mem.get 3 = 1 := (hpresE 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hL_E : sE.mem.get 16 = 4 := (hpresE 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hC_E : sE.mem.get 13 = s.mem.get 13 := hpresE 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hLlt_E : (4 : Nat) < (sE.mem.get 13).toNat := by
    rw [hC_E]; exact hLlt
  have hChi_E : (sE.mem.get 13).toNat < 32768 := by
    rw [hC_E]; exact hChi
  have gE : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      sE.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
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
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresE (UInt16.ofNat k) n33 n34 n35 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hw := after_digs_write_nul_done_len4 (s := sE) hsEpc hsEh hsEZ hONE_E hL_E hLlt_E hChi_E gE
  have hrun : sD = runN sE 36 := runN_add_eq s 340 36 376 (by decide)
  have hpresw := hw.2.2.2.2.2.2
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 22 := by
    rw [hrun]
    exact (hpresw 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.1)
  have hsD34 : sD.mem.get 34 = s.mem.get 23 := by
    rw [hrun]
    exact (hpresw 34 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.1)
  have hsD35 : sD.mem.get 35 = s.mem.get 24 := by
    rw [hrun]
    exact (hpresw 35 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.2.1)
  have hsDNUL : sD.mem.get 36 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 4 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 4 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha36 ha18 ha30 ha29 ha0).trans
      (hpresE a ha33 ha34 ha35 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD33, hsD34, hsD35, hsDNUL, hsDI, hsDL, hpres⟩


/-- `EMIT_DIGS` with `NDIG = 4` and `IDX = 0`, then `AFTER_DIGS`/`WRITE_NUL`/`DONE`
when `LEN = 4 < CAP`. 428 steps to a halted machine with NUL at `BUF+4`. -/
theorem emit_ndig4_idx0_write_nul_done {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 4)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 4)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (4 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 428
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 21 ∧
    sD.mem.get 33 = s.mem.get 22 ∧
    sD.mem.get 34 = s.mem.get 23 ∧
    sD.mem.get 35 = s.mem.get 24 ∧
    sD.mem.get 36 = 0 ∧
    sD.mem.get 29 = 4 ∧
    sD.mem.get 16 = 4 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have he := emit_ndig4_idx0 (s := s) hpc hh hZ hONE hK5 hN hI hRlo hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sE := runN s 392
  have hsEpc : sE.pc = 1905 := he.1
  have hsEh : sE.halted = false := he.2.1
  have hsEZ : sE.mem.get 0 = 0 := he.2.2.1
  have hpresE := he.2.2.2.2.2.2.2.2
  have hONE_E : sE.mem.get 3 = 1 := (hpresE 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hL_E : sE.mem.get 16 = 4 := (hpresE 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hC_E : sE.mem.get 13 = s.mem.get 13 := hpresE 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hLlt_E : (4 : Nat) < (sE.mem.get 13).toNat := by
    rw [hC_E]; exact hLlt
  have hChi_E : (sE.mem.get 13).toNat < 32768 := by
    rw [hC_E]; exact hChi
  have gE : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      sE.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
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
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresE (UInt16.ofNat k) n32 n33 n34 n35 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hw := after_digs_write_nul_done_len4 (s := sE) hsEpc hsEh hsEZ hONE_E hL_E hLlt_E hChi_E gE
  have hrun : sD = runN sE 36 := runN_add_eq s 392 36 428 (by decide)
  have hpresw := hw.2.2.2.2.2.2
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD32 : sD.mem.get 32 = s.mem.get 21 := by
    rw [hrun]
    exact (hpresw 32 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.1)
  have hsD33 : sD.mem.get 33 = s.mem.get 22 := by
    rw [hrun]
    exact (hpresw 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.1)
  have hsD34 : sD.mem.get 34 = s.mem.get 23 := by
    rw [hrun]
    exact (hpresw 34 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.2.1)
  have hsD35 : sD.mem.get 35 = s.mem.get 24 := by
    rw [hrun]
    exact (hpresw 35 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.2.2.1)
  have hsDNUL : sD.mem.get 36 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 4 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 4 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha36 ha18 ha30 ha29 ha0).trans
      (hpresE a ha32 ha33 ha34 ha35 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsDNUL, hsDI, hsDL, hpres⟩


/-- `EMIT_DIGS` with `NDIG = 4` and `IDX = 1`, then `AFTER_DIGS`/`WRITE_NUL`/`DONE`
when `LEN = 5 < CAP`. 438 steps to a halted machine with NUL at `BUF+5`. -/
theorem emit_ndig4_idx1_write_nul_done {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 4)
    (hI : s.mem.get 29 = 1)
    (hL : s.mem.get 16 = 5)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (5 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 438
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 33 = s.mem.get 21 ∧
    sD.mem.get 34 = s.mem.get 22 ∧
    sD.mem.get 35 = s.mem.get 23 ∧
    sD.mem.get 36 = s.mem.get 24 ∧
    sD.mem.get 37 = 0 ∧
    sD.mem.get 29 = 5 ∧
    sD.mem.get 16 = 5 ∧
    (∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have he := emit_ndig4_idx1 (s := s) hpc hh hZ hONE hK5 hN hI hRlo hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sE := runN s 400
  have hsEpc : sE.pc = 1905 := he.1
  have hsEh : sE.halted = false := he.2.1
  have hsEZ : sE.mem.get 0 = 0 := he.2.2.1
  have hpresE := he.2.2.2.2.2.2.2.2
  have hONE_E : sE.mem.get 3 = 1 := (hpresE 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hL_E : sE.mem.get 16 = 5 := (hpresE 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hC_E : sE.mem.get 13 = s.mem.get 13 := hpresE 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hLlt_E : (5 : Nat) < (sE.mem.get 13).toNat := by
    rw [hC_E]; exact hLlt
  have hChi_E : (sE.mem.get 13).toNat < 32768 := by
    rw [hC_E]; exact hChi
  have gE : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      sE.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
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
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresE (UInt16.ofNat k) n33 n34 n35 n36 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hw := after_digs_write_nul_done_len5 (s := sE) hsEpc hsEh hsEZ hONE_E hL_E hLlt_E hChi_E gE
  have hrun : sD = runN sE 38 := runN_add_eq s 400 38 438 (by decide)
  have hpresw := hw.2.2.2.2.2.2
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 21 := by
    rw [hrun]
    exact (hpresw 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.1)
  have hsD34 : sD.mem.get 34 = s.mem.get 22 := by
    rw [hrun]
    exact (hpresw 34 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.1)
  have hsD35 : sD.mem.get 35 = s.mem.get 23 := by
    rw [hrun]
    exact (hpresw 35 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.2.1)
  have hsD36 : sD.mem.get 36 = s.mem.get 24 := by
    rw [hrun]
    exact (hpresw 36 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.2.2.1)
  have hsDNUL : sD.mem.get 37 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 5 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 5 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha37 ha18 ha30 ha29 ha0).trans
      (hpresE a ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD33, hsD34, hsD35, hsD36, hsDNUL, hsDI, hsDL, hpres⟩


/-- `EMIT_DIGS` with `NDIG = 5` and `IDX = 0`, then `AFTER_DIGS`/`WRITE_NUL`/`DONE`
when `LEN = 5 < CAP`. 488 steps to a halted machine with NUL at `BUF+5`. -/
theorem emit_ndig5_idx0_write_nul_done {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 5)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 5)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (5 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 488
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 20 ∧
    sD.mem.get 33 = s.mem.get 21 ∧
    sD.mem.get 34 = s.mem.get 22 ∧
    sD.mem.get 35 = s.mem.get 23 ∧
    sD.mem.get 36 = s.mem.get 24 ∧
    sD.mem.get 37 = 0 ∧
    sD.mem.get 29 = 5 ∧
    sD.mem.get 16 = 5 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have he := emit_ndig5_idx0 (s := s) hpc hh hZ hONE hK5 hN hI hRlo hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sE := runN s 450
  have hsEpc : sE.pc = 1905 := he.1
  have hsEh : sE.halted = false := he.2.1
  have hsEZ : sE.mem.get 0 = 0 := he.2.2.1
  have hpresE := he.2.2.2.2.2.2.2.2.2
  have hONE_E : sE.mem.get 3 = 1 := (hpresE 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hL_E : sE.mem.get 16 = 5 := (hpresE 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hC_E : sE.mem.get 13 = s.mem.get 13 := hpresE 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hLlt_E : (5 : Nat) < (sE.mem.get 13).toNat := by
    rw [hC_E]; exact hLlt
  have hChi_E : (sE.mem.get 13).toNat < 32768 := by
    rw [hC_E]; exact hChi
  have gE : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      sE.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
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
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresE (UInt16.ofNat k) n32 n33 n34 n35 n36 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hw := after_digs_write_nul_done_len5 (s := sE) hsEpc hsEh hsEZ hONE_E hL_E hLlt_E hChi_E gE
  have hrun : sD = runN sE 38 := runN_add_eq s 450 38 488 (by decide)
  have hpresw := hw.2.2.2.2.2.2
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD32 : sD.mem.get 32 = s.mem.get 20 := by
    rw [hrun]
    exact (hpresw 32 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.1)
  have hsD33 : sD.mem.get 33 = s.mem.get 21 := by
    rw [hrun]
    exact (hpresw 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.1)
  have hsD34 : sD.mem.get 34 = s.mem.get 22 := by
    rw [hrun]
    exact (hpresw 34 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.2.1)
  have hsD35 : sD.mem.get 35 = s.mem.get 23 := by
    rw [hrun]
    exact (hpresw 35 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.2.2.1)
  have hsD36 : sD.mem.get 36 = s.mem.get 24 := by
    rw [hrun]
    exact (hpresw 36 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.2.2.2.1)
  have hsDNUL : sD.mem.get 37 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 5 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 5 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha37 ha18 ha30 ha29 ha0).trans
      (hpresE a ha32 ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsD36, hsDNUL, hsDI, hsDL, hpres⟩


/-- `EMIT_DIGS` with `NDIG = 5` and `IDX = 1`, then `AFTER_DIGS`/`WRITE_NUL`/`DONE`
when `LEN = 6 < CAP`. 500 steps to a halted machine with NUL at `BUF+6`. -/
theorem emit_ndig5_idx1_write_nul_done {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 5)
    (hI : s.mem.get 29 = 1)
    (hL : s.mem.get 16 = 6)
    (hRlo : 5 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (6 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 500
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 33 = s.mem.get 20 ∧
    sD.mem.get 34 = s.mem.get 21 ∧
    sD.mem.get 35 = s.mem.get 22 ∧
    sD.mem.get 36 = s.mem.get 23 ∧
    sD.mem.get 37 = s.mem.get 24 ∧
    sD.mem.get 38 = 0 ∧
    sD.mem.get 29 = 6 ∧
    sD.mem.get 16 = 6 ∧
    (∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 38 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have he := emit_ndig5_idx1 (s := s) hpc hh hZ hONE hK5 hN hI hRlo hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sE := runN s 460
  have hsEpc : sE.pc = 1905 := he.1
  have hsEh : sE.halted = false := he.2.1
  have hsEZ : sE.mem.get 0 = 0 := he.2.2.1
  have hpresE := he.2.2.2.2.2.2.2.2.2
  have hONE_E : sE.mem.get 3 = 1 := (hpresE 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hL_E : sE.mem.get 16 = 6 := (hpresE 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hC_E : sE.mem.get 13 = s.mem.get 13 := hpresE 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hLlt_E : (6 : Nat) < (sE.mem.get 13).toNat := by
    rw [hC_E]; exact hLlt
  have hChi_E : (sE.mem.get 13).toNat < 32768 := by
    rw [hC_E]; exact hChi
  have gE : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      sE.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
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
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresE (UInt16.ofNat k) n33 n34 n35 n36 n37 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hw := after_digs_write_nul_done_len6 (s := sE) hsEpc hsEh hsEZ hONE_E hL_E hLlt_E hChi_E gE
  have hrun : sD = runN sE 40 := runN_add_eq s 460 40 500 (by decide)
  have hpresw := hw.2.2.2.2.2.2
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 20 := by
    rw [hrun]
    exact (hpresw 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.1)
  have hsD34 : sD.mem.get 34 = s.mem.get 21 := by
    rw [hrun]
    exact (hpresw 34 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.1)
  have hsD35 : sD.mem.get 35 = s.mem.get 22 := by
    rw [hrun]
    exact (hpresw 35 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.2.1)
  have hsD36 : sD.mem.get 36 = s.mem.get 23 := by
    rw [hrun]
    exact (hpresw 36 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.2.2.1)
  have hsD37 : sD.mem.get 37 = s.mem.get 24 := by
    rw [hrun]
    exact (hpresw 37 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (he.2.2.2.2.2.2.2.1)
  have hsDNUL : sD.mem.get 38 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 6 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 6 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 38 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha33 ha34 ha35 ha36 ha37 ha38 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha38 ha18 ha30 ha29 ha0).trans
      (hpresE a ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD33, hsD34, hsD35, hsD36, hsD37, hsDNUL, hsDI, hsDL, hpres⟩

end IntFmt
