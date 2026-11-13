/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

`HAVE_DIG` through `LEN_OK`: RAW from NDIG/SIGN, PAD/LEN versus WIDTH,
and the `CAP==0` halt (or the fall-through that sets `ROOM` and enters
`SP_LOOP`). Block lemmas, not end-to-end correctness.
-/

import IntFmt.Ndig
import IntFmt.DecChunksC

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000


private theorem cell864 (off : Nat) (h : off < 16) :
    intfmtImage[864 + off]! = decChunk054[off]! :=
  extract_chunk 864 decChunk054 image_chunk054 off h (by decide)


private theorem cell880 (off : Nat) (h : off < 16) :
    intfmtImage[880 + off]! = decChunk055[off]! :=
  extract_chunk 880 decChunk055 image_chunk055 off h (by decide)


private theorem cell896 (off : Nat) (h : off < 16) :
    intfmtImage[896 + off]! = decChunk056[off]! :=
  extract_chunk 896 decChunk056 image_chunk056 off h (by decide)


private theorem cell912 (off : Nat) (h : off < 16) :
    intfmtImage[912 + off]! = decChunk057[off]! :=
  extract_chunk 912 decChunk057 image_chunk057 off h (by decide)


private theorem cell928 (off : Nat) (h : off < 16) :
    intfmtImage[928 + off]! = decChunk058[off]! :=
  extract_chunk 928 decChunk058 image_chunk058 off h (by decide)


private theorem cell944 (off : Nat) (h : off < 16) :
    intfmtImage[944 + off]! = decChunk059[off]! :=
  extract_chunk 944 decChunk059 image_chunk059 off h (by decide)


private theorem cell960 (off : Nat) (h : off < 16) :
    intfmtImage[960 + off]! = decChunk060[off]! :=
  extract_chunk 960 decChunk060 image_chunk060 off h (by decide)


private theorem cell976 (off : Nat) (h : off < 16) :
    intfmtImage[976 + off]! = decChunk061[off]! :=
  extract_chunk 976 decChunk061 image_chunk061 off h (by decide)


private theorem cell992 (off : Nat) (h : off < 16) :
    intfmtImage[992 + off]! = decChunk062[off]! :=
  extract_chunk 992 decChunk062 image_chunk062 off h (by decide)


private theorem cell1008 (off : Nat) (h : off < 16) :
    intfmtImage[1008 + off]! = decChunk063[off]! :=
  extract_chunk 1008 decChunk063 image_chunk063 off h (by decide)

private theorem cell1024 (off : Nat) (h : off < 16) :
    intfmtImage[1024 + off]! = decChunk064[off]! :=
  extract_chunk 1024 decChunk064 image_chunk064 off h (by decide)


private theorem cell2304 (off : Nat) (h : off < 16) :
    intfmtImage[2304 + off]! = decChunk144[off]! :=
  extract_chunk 2304 decChunk144 image_chunk144 off h (by decide)

/-- MOV NDIG RAW at HAVE_DIG (pc 867). -/
theorem pad_mov_NDIG_RAW {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 879 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 879 ∧
    s4.halted = false ∧
    s4.mem.get 26 = s.mem.get 25 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 25 = s.mem.get 25 ∧
    (∀ a, a ≠ 26 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 867 :=
    hpc.trans (rfl : (867 : Word) = UInt16.ofNat 867)
  have g (k : Nat) (h1 : 867 ≤ k) (h2 : k < 879) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (867 + off) :=
    word_pc_off 867 off hp (by omega)
  have m0 : s.mem.get s.pc = 26 := by
    rw [hp]
    have hval : decChunk054[3]! = 26 := rfl
    exact (g 867 (by decide) (by decide)).trans ((cell864 3 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 26 := by
    rw [poff 1 (by decide)]
    have hval : decChunk054[4]! = 26 := rfl
    exact (g 868 (by decide) (by decide)).trans ((cell864 4 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk054[5]! = 870 := rfl
    have hv : (870 : Word) = UInt16.ofNat 870 := rfl
    exact (g 869 (by decide) (by decide)).trans ((cell864 5 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 25 := by
    rw [poff 3 (by decide)]
    have hval : decChunk054[6]! = 25 := rfl
    exact (g 870 (by decide) (by decide)).trans ((cell864 6 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk054[7]! = 0 := rfl
    exact (g 871 (by decide) (by decide)).trans ((cell864 7 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk054[8]! = 873 := rfl
    have hv : (873 : Word) = UInt16.ofNat 873 := rfl
    exact (g 872 (by decide) (by decide)).trans ((cell864 8 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk054[9]! = 0 := rfl
    exact (g 873 (by decide) (by decide)).trans ((cell864 9 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 26 := by
    rw [poff 7 (by decide)]
    have hval : decChunk054[10]! = 26 := rfl
    exact (g 874 (by decide) (by decide)).trans ((cell864 10 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk054[11]! = 876 := rfl
    have hv : (876 : Word) = UInt16.ofNat 876 := rfl
    exact (g 875 (by decide) (by decide)).trans ((cell864 11 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk054[12]! = 0 := rfl
    exact (g 876 (by decide) (by decide)).trans ((cell864 12 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk054[13]! = 0 := rfl
    exact (g 877 (by decide) (by decide)).trans ((cell864 13 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk054[14]! = 879 := rfl
    have hv : (879 : Word) = UInt16.ofNat 879 := rfl
    exact (g 878 (by decide) (by decide)).trans ((cell864 14 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (26 : Word) := by
    intro i hi
    have : (26 : Word) = UInt16.ofNat 26 := rfl
    rw [this]
    exact pc_off_ne 867 i 26 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 867 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 25) (dst := 26)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 879 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (879 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 879 = (879 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- MOV SIGN T at pc 879. -/
theorem pad_mov_SIGN_T {s : Machine}
    (hpc : s.pc = 879)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 879 ≤ k → k < 891 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 891 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 19 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 19 = s.mem.get 19 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 879 :=
    hpc.trans (rfl : (879 : Word) = UInt16.ofNat 879)
  have g (k : Nat) (h1 : 879 ≤ k) (h2 : k < 891) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (879 + off) :=
    word_pc_off 879 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk054[15]! = 18 := rfl
    exact (g 879 (by decide) (by decide)).trans ((cell864 15 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk055[0]! = 18 := rfl
    exact (g 880 (by decide) (by decide)).trans ((cell880 0 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk055[1]! = 882 := rfl
    have hv : (882 : Word) = UInt16.ofNat 882 := rfl
    exact (g 881 (by decide) (by decide)).trans ((cell880 1 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 19 := by
    rw [poff 3 (by decide)]
    have hval : decChunk055[2]! = 19 := rfl
    exact (g 882 (by decide) (by decide)).trans ((cell880 2 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk055[3]! = 0 := rfl
    exact (g 883 (by decide) (by decide)).trans ((cell880 3 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk055[4]! = 885 := rfl
    have hv : (885 : Word) = UInt16.ofNat 885 := rfl
    exact (g 884 (by decide) (by decide)).trans ((cell880 4 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk055[5]! = 0 := rfl
    exact (g 885 (by decide) (by decide)).trans ((cell880 5 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk055[6]! = 18 := rfl
    exact (g 886 (by decide) (by decide)).trans ((cell880 6 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk055[7]! = 888 := rfl
    have hv : (888 : Word) = UInt16.ofNat 888 := rfl
    exact (g 887 (by decide) (by decide)).trans ((cell880 7 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk055[8]! = 0 := rfl
    exact (g 888 (by decide) (by decide)).trans ((cell880 8 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk055[9]! = 0 := rfl
    exact (g 889 (by decide) (by decide)).trans ((cell880 9 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk055[10]! = 891 := rfl
    have hv : (891 : Word) = UInt16.ofNat 891 := rfl
    exact (g 890 (by decide) (by decide)).trans ((cell880 10 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 879 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 879 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 19) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 891 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (891 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 891 = (891 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JLEZ T RAW_OK at pc 891. -/
theorem pad_enc_jlez_891 {s : Machine}
    (hpc : s.pc = 891)
    (hcode : ∀ k : Nat, 891 ≤ k → k < 891+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 903 := by
  have hp : s.pc = UInt16.ofNat 891 :=
    hpc.trans (rfl : (891 : Word) = UInt16.ofNat 891)
  have g (k : Nat) (h1 : 891 ≤ k) (h2 : k < 891+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk055[11]! = 0 := rfl
    exact (g 891 (by decide) (by decide)).trans ((cell880 11 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (892 : Word) := by simp [hpc]
    rw [this, (rfl : (892 : Word) = UInt16.ofNat 892)]
    have hval : decChunk055[12]! = 18 := rfl
    exact (g 892 (by decide) (by decide)).trans ((cell880 12 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 903 := by
    have : s.pc + 2 = (893 : Word) := by simp [hpc]
    rw [this, (rfl : (893 : Word) = UInt16.ofNat 893)]
    have hval : decChunk055[13]! = 903 := rfl
    exact (g 893 (by decide) (by decide)).trans ((cell880 13 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- INC RAW at pc 894 (SIGN nonzero). -/
theorem pad_inc_RAW {s : Machine}
    (hpc : s.pc = 894)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 894 ≤ k → k < 903 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 903 ∧
    s3.halted = false ∧
    s3.mem.get 26 = s.mem.get 26 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 26 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 894 :=
    hpc.trans (rfl : (894 : Word) = UInt16.ofNat 894)
  have g (k : Nat) (h1 : 894 ≤ k) (h2 : k < 903) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (894 + off) :=
    word_pc_off 894 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk055[14]! = 3 := rfl
    exact (g 894 (by decide) (by decide)).trans ((cell880 14 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk055[15]! = 0 := rfl
    exact (g 895 (by decide) (by decide)).trans ((cell880 15 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk056[0]! = 897 := rfl
    have hv : (897 : Word) = UInt16.ofNat 897 := rfl
    exact (g 896 (by decide) (by decide)).trans ((cell896 0 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk056[1]! = 0 := rfl
    exact (g 897 (by decide) (by decide)).trans ((cell896 1 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 26 := by
    rw [poff 4 (by decide)]
    have hval : decChunk056[2]! = 26 := rfl
    exact (g 898 (by decide) (by decide)).trans ((cell896 2 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk056[3]! = 900 := rfl
    have hv : (900 : Word) = UInt16.ofNat 900 := rfl
    exact (g 899 (by decide) (by decide)).trans ((cell896 3 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk056[4]! = 0 := rfl
    exact (g 900 (by decide) (by decide)).trans ((cell896 4 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk056[5]! = 0 := rfl
    exact (g 901 (by decide) (by decide)).trans ((cell896 5 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk056[6]! = 903 := rfl
    have hv : (903 : Word) = UInt16.ofNat 903 := rfl
    exact (g 902 (by decide) (by decide)).trans ((cell896 6 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (26 : Word) := by
    intro i hi
    have : (26 : Word) = UInt16.ofNat 26 := rfl
    rw [this]
    exact pc_off_ne 894 i 26 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 894 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 26)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 903 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (903 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 903 = (903 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 26 = s.mem.get 26 + 1 := by
    have : s.mem.get 26 + s.mem.get 3 = s.mem.get 26 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- ZERO PAD at RAW_OK (pc 903). -/
theorem pad_zero_PAD {s : Machine}
    (hpc : s.pc = 903)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 903 ≤ k → k < 906 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s = { s with mem := s.mem.set 27 0, pc := 906 } := by
  have hp : s.pc = UInt16.ofNat 903 :=
    hpc.trans (rfl : (903 : Word) = UInt16.ofNat 903)
  have g (k : Nat) (h1 : 903 ≤ k) (h2 : k < 906) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 27 := by
    rw [hp]
    have hval : decChunk056[7]! = 27 := rfl
    exact (g 903 (by decide) (by decide)).trans ((cell896 7 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 27 := by
    have : s.pc + 1 = (904 : Word) := by simp [hpc]
    rw [this, (rfl : (904 : Word) = UInt16.ofNat 904)]
    have hval : decChunk056[8]! = 27 := rfl
    exact (g 904 (by decide) (by decide)).trans ((cell896 8 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (905 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (906 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (905 : Word) = UInt16.ofNat 905)]
    have hval : decChunk056[9]! = 906 := rfl
    have hv : (906 : Word) = UInt16.ofNat 906 := rfl
    exact (g 905 (by decide) (by decide)).trans ((cell896 9 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hz :=
    step_ZERO (s := s) (x := 27) hh hpc0 ha hb hc (by decide)
  have hpc' : s.pc + 3 = (906 : Word) := by simp [hpc]
  rw [hz, hpc']

/-- MOV WIDTH T at pc 906. -/
theorem pad_mov_WIDTH_T_906 {s : Machine}
    (hpc : s.pc = 906)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 906 ≤ k → k < 918 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 918 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 14 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 14 = s.mem.get 14 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 906 :=
    hpc.trans (rfl : (906 : Word) = UInt16.ofNat 906)
  have g (k : Nat) (h1 : 906 ≤ k) (h2 : k < 918) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (906 + off) :=
    word_pc_off 906 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk056[10]! = 18 := rfl
    exact (g 906 (by decide) (by decide)).trans ((cell896 10 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk056[11]! = 18 := rfl
    exact (g 907 (by decide) (by decide)).trans ((cell896 11 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk056[12]! = 909 := rfl
    have hv : (909 : Word) = UInt16.ofNat 909 := rfl
    exact (g 908 (by decide) (by decide)).trans ((cell896 12 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 14 := by
    rw [poff 3 (by decide)]
    have hval : decChunk056[13]! = 14 := rfl
    exact (g 909 (by decide) (by decide)).trans ((cell896 13 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk056[14]! = 0 := rfl
    exact (g 910 (by decide) (by decide)).trans ((cell896 14 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk056[15]! = 912 := rfl
    have hv : (912 : Word) = UInt16.ofNat 912 := rfl
    exact (g 911 (by decide) (by decide)).trans ((cell896 15 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk057[0]! = 0 := rfl
    exact (g 912 (by decide) (by decide)).trans ((cell912 0 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk057[1]! = 18 := rfl
    exact (g 913 (by decide) (by decide)).trans ((cell912 1 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk057[2]! = 915 := rfl
    have hv : (915 : Word) = UInt16.ofNat 915 := rfl
    exact (g 914 (by decide) (by decide)).trans ((cell912 2 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk057[3]! = 0 := rfl
    exact (g 915 (by decide) (by decide)).trans ((cell912 3 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk057[4]! = 0 := rfl
    exact (g 916 (by decide) (by decide)).trans ((cell912 4 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk057[5]! = 918 := rfl
    have hv : (918 : Word) = UInt16.ofNat 918 := rfl
    exact (g 917 (by decide) (by decide)).trans ((cell912 5 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 906 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 906 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 14) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 918 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (918 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 918 = (918 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JLEZ T NO_PAD at pc 918. -/
theorem pad_enc_jlez_918 {s : Machine}
    (hpc : s.pc = 918)
    (hcode : ∀ k : Nat, 918 ≤ k → k < 918+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 966 := by
  have hp : s.pc = UInt16.ofNat 918 :=
    hpc.trans (rfl : (918 : Word) = UInt16.ofNat 918)
  have g (k : Nat) (h1 : 918 ≤ k) (h2 : k < 918+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk057[6]! = 0 := rfl
    exact (g 918 (by decide) (by decide)).trans ((cell912 6 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (919 : Word) := by simp [hpc]
    rw [this, (rfl : (919 : Word) = UInt16.ofNat 919)]
    have hval : decChunk057[7]! = 18 := rfl
    exact (g 919 (by decide) (by decide)).trans ((cell912 7 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 966 := by
    have : s.pc + 2 = (920 : Word) := by simp [hpc]
    rw [this, (rfl : (920 : Word) = UInt16.ofNat 920)]
    have hval : decChunk057[8]! = 966 := rfl
    exact (g 920 (by decide) (by decide)).trans ((cell912 8 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV WIDTH T at pc 921 (WIDTH nonzero). -/
theorem pad_mov_WIDTH_T_921 {s : Machine}
    (hpc : s.pc = 921)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 921 ≤ k → k < 933 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 933 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 14 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 14 = s.mem.get 14 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 921 :=
    hpc.trans (rfl : (921 : Word) = UInt16.ofNat 921)
  have g (k : Nat) (h1 : 921 ≤ k) (h2 : k < 933) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (921 + off) :=
    word_pc_off 921 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk057[9]! = 18 := rfl
    exact (g 921 (by decide) (by decide)).trans ((cell912 9 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk057[10]! = 18 := rfl
    exact (g 922 (by decide) (by decide)).trans ((cell912 10 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk057[11]! = 924 := rfl
    have hv : (924 : Word) = UInt16.ofNat 924 := rfl
    exact (g 923 (by decide) (by decide)).trans ((cell912 11 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 14 := by
    rw [poff 3 (by decide)]
    have hval : decChunk057[12]! = 14 := rfl
    exact (g 924 (by decide) (by decide)).trans ((cell912 12 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk057[13]! = 0 := rfl
    exact (g 925 (by decide) (by decide)).trans ((cell912 13 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk057[14]! = 927 := rfl
    have hv : (927 : Word) = UInt16.ofNat 927 := rfl
    exact (g 926 (by decide) (by decide)).trans ((cell912 14 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk057[15]! = 0 := rfl
    exact (g 927 (by decide) (by decide)).trans ((cell912 15 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk058[0]! = 18 := rfl
    exact (g 928 (by decide) (by decide)).trans ((cell928 0 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk058[1]! = 930 := rfl
    have hv : (930 : Word) = UInt16.ofNat 930 := rfl
    exact (g 929 (by decide) (by decide)).trans ((cell928 1 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk058[2]! = 0 := rfl
    exact (g 930 (by decide) (by decide)).trans ((cell928 2 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk058[3]! = 0 := rfl
    exact (g 931 (by decide) (by decide)).trans ((cell928 3 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk058[4]! = 933 := rfl
    have hv : (933 : Word) = UInt16.ofNat 933 := rfl
    exact (g 932 (by decide) (by decide)).trans ((cell928 4 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 921 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 921 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 14) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 933 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (933 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 933 = (933 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- SUB RAW T at pc 933 (T = WIDTH - RAW). -/
theorem pad_sub_RAW_T {s : Machine}
    (hpc : s.pc = 933)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 933 ≤ k → k < 936 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 26)
        pc := 936 } := by
  have hp : s.pc = UInt16.ofNat 933 :=
    hpc.trans (rfl : (933 : Word) = UInt16.ofNat 933)
  have g (k : Nat) (h1 : 933 ≤ k) (h2 : k < 936) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 26 := by
    rw [hp]
    have hval : decChunk058[5]! = 26 := rfl
    exact (g 933 (by decide) (by decide)).trans ((cell928 5 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (934 : Word) := by simp [hpc]
    rw [this, (rfl : (934 : Word) = UInt16.ofNat 934)]
    have hval : decChunk058[6]! = 18 := rfl
    exact (g 934 (by decide) (by decide)).trans ((cell928 6 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (935 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (936 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (935 : Word) = UInt16.ofNat 935)]
    have hval : decChunk058[7]! = 936 := rfl
    have hv : (936 : Word) = UInt16.ofNat 936 := rfl
    exact (g 935 (by decide) (by decide)).trans ((cell928 7 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 26) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (936 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T NO_PAD at pc 936 (WIDTH <= RAW). -/
theorem pad_enc_jlez_936 {s : Machine}
    (hpc : s.pc = 936)
    (hcode : ∀ k : Nat, 936 ≤ k → k < 936+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 966 := by
  have hp : s.pc = UInt16.ofNat 936 :=
    hpc.trans (rfl : (936 : Word) = UInt16.ofNat 936)
  have g (k : Nat) (h1 : 936 ≤ k) (h2 : k < 936+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk058[8]! = 0 := rfl
    exact (g 936 (by decide) (by decide)).trans ((cell928 8 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (937 : Word) := by simp [hpc]
    rw [this, (rfl : (937 : Word) = UInt16.ofNat 937)]
    have hval : decChunk058[9]! = 18 := rfl
    exact (g 937 (by decide) (by decide)).trans ((cell928 9 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 966 := by
    have : s.pc + 2 = (938 : Word) := by simp [hpc]
    rw [this, (rfl : (938 : Word) = UInt16.ofNat 938)]
    have hval : decChunk058[10]! = 966 := rfl
    exact (g 938 (by decide) (by decide)).trans ((cell928 10 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV T PAD at pc 939 (PAD = WIDTH - RAW). -/
theorem pad_mov_T_PAD {s : Machine}
    (hpc : s.pc = 939)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 939 ≤ k → k < 951 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 951 ∧
    s4.halted = false ∧
    s4.mem.get 27 = s.mem.get 18 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 18 = s.mem.get 18 ∧
    (∀ a, a ≠ 27 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 939 :=
    hpc.trans (rfl : (939 : Word) = UInt16.ofNat 939)
  have g (k : Nat) (h1 : 939 ≤ k) (h2 : k < 951) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (939 + off) :=
    word_pc_off 939 off hp (by omega)
  have m0 : s.mem.get s.pc = 27 := by
    rw [hp]
    have hval : decChunk058[11]! = 27 := rfl
    exact (g 939 (by decide) (by decide)).trans ((cell928 11 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 27 := by
    rw [poff 1 (by decide)]
    have hval : decChunk058[12]! = 27 := rfl
    exact (g 940 (by decide) (by decide)).trans ((cell928 12 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk058[13]! = 942 := rfl
    have hv : (942 : Word) = UInt16.ofNat 942 := rfl
    exact (g 941 (by decide) (by decide)).trans ((cell928 13 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 18 := by
    rw [poff 3 (by decide)]
    have hval : decChunk058[14]! = 18 := rfl
    exact (g 942 (by decide) (by decide)).trans ((cell928 14 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk058[15]! = 0 := rfl
    exact (g 943 (by decide) (by decide)).trans ((cell928 15 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk059[0]! = 945 := rfl
    have hv : (945 : Word) = UInt16.ofNat 945 := rfl
    exact (g 944 (by decide) (by decide)).trans ((cell944 0 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk059[1]! = 0 := rfl
    exact (g 945 (by decide) (by decide)).trans ((cell944 1 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 27 := by
    rw [poff 7 (by decide)]
    have hval : decChunk059[2]! = 27 := rfl
    exact (g 946 (by decide) (by decide)).trans ((cell944 2 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk059[3]! = 948 := rfl
    have hv : (948 : Word) = UInt16.ofNat 948 := rfl
    exact (g 947 (by decide) (by decide)).trans ((cell944 3 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk059[4]! = 0 := rfl
    exact (g 948 (by decide) (by decide)).trans ((cell944 4 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk059[5]! = 0 := rfl
    exact (g 949 (by decide) (by decide)).trans ((cell944 5 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk059[6]! = 951 := rfl
    have hv : (951 : Word) = UInt16.ofNat 951 := rfl
    exact (g 950 (by decide) (by decide)).trans ((cell944 6 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (27 : Word) := by
    intro i hi
    have : (27 : Word) = UInt16.ofNat 27 := rfl
    rw [this]
    exact pc_off_ne 939 i 27 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 939 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 18) (dst := 27)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 951 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (951 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 951 = (951 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- MOV WIDTH LEN at pc 951. -/
theorem pad_mov_WIDTH_LEN {s : Machine}
    (hpc : s.pc = 951)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 951 ≤ k → k < 963 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 963 ∧
    s4.halted = false ∧
    s4.mem.get 16 = s.mem.get 14 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 14 = s.mem.get 14 ∧
    (∀ a, a ≠ 16 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 951 :=
    hpc.trans (rfl : (951 : Word) = UInt16.ofNat 951)
  have g (k : Nat) (h1 : 951 ≤ k) (h2 : k < 963) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (951 + off) :=
    word_pc_off 951 off hp (by omega)
  have m0 : s.mem.get s.pc = 16 := by
    rw [hp]
    have hval : decChunk059[7]! = 16 := rfl
    exact (g 951 (by decide) (by decide)).trans ((cell944 7 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 16 := by
    rw [poff 1 (by decide)]
    have hval : decChunk059[8]! = 16 := rfl
    exact (g 952 (by decide) (by decide)).trans ((cell944 8 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk059[9]! = 954 := rfl
    have hv : (954 : Word) = UInt16.ofNat 954 := rfl
    exact (g 953 (by decide) (by decide)).trans ((cell944 9 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 14 := by
    rw [poff 3 (by decide)]
    have hval : decChunk059[10]! = 14 := rfl
    exact (g 954 (by decide) (by decide)).trans ((cell944 10 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk059[11]! = 0 := rfl
    exact (g 955 (by decide) (by decide)).trans ((cell944 11 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk059[12]! = 957 := rfl
    have hv : (957 : Word) = UInt16.ofNat 957 := rfl
    exact (g 956 (by decide) (by decide)).trans ((cell944 12 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk059[13]! = 0 := rfl
    exact (g 957 (by decide) (by decide)).trans ((cell944 13 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 16 := by
    rw [poff 7 (by decide)]
    have hval : decChunk059[14]! = 16 := rfl
    exact (g 958 (by decide) (by decide)).trans ((cell944 14 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk059[15]! = 960 := rfl
    have hv : (960 : Word) = UInt16.ofNat 960 := rfl
    exact (g 959 (by decide) (by decide)).trans ((cell944 15 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk060[0]! = 0 := rfl
    exact (g 960 (by decide) (by decide)).trans ((cell960 0 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk060[1]! = 0 := rfl
    exact (g 961 (by decide) (by decide)).trans ((cell960 1 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk060[2]! = 963 := rfl
    have hv : (963 : Word) = UInt16.ofNat 963 := rfl
    exact (g 962 (by decide) (by decide)).trans ((cell960 2 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (16 : Word) := by
    intro i hi
    have : (16 : Word) = UInt16.ofNat 16 := rfl
    rw [this]
    exact pc_off_ne 951 i 16 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 951 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 14) (dst := 16)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 963 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (963 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 963 = (963 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP LEN_OK at pc 963. -/
theorem pad_enc_jmp_963 {s : Machine}
    (hpc : s.pc = 963)
    (hcode : ∀ k : Nat, 963 ≤ k → k < 963+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 978 := by
  have hp : s.pc = UInt16.ofNat 963 :=
    hpc.trans (rfl : (963 : Word) = UInt16.ofNat 963)
  have g (k : Nat) (h1 : 963 ≤ k) (h2 : k < 963+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk060[3]! = 0 := rfl
    exact (g 963 (by decide) (by decide)).trans ((cell960 3 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (964 : Word) := by simp [hpc]
    rw [this, (rfl : (964 : Word) = UInt16.ofNat 964)]
    have hval : decChunk060[4]! = 0 := rfl
    exact (g 964 (by decide) (by decide)).trans ((cell960 4 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 978 := by
    have : s.pc + 2 = (965 : Word) := by simp [hpc]
    rw [this, (rfl : (965 : Word) = UInt16.ofNat 965)]
    have hval : decChunk060[5]! = 978 := rfl
    exact (g 965 (by decide) (by decide)).trans ((cell960 5 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV RAW LEN at NO_PAD (pc 966). -/
theorem pad_mov_RAW_LEN {s : Machine}
    (hpc : s.pc = 966)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 966 ≤ k → k < 978 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 978 ∧
    s4.halted = false ∧
    s4.mem.get 16 = s.mem.get 26 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 26 = s.mem.get 26 ∧
    (∀ a, a ≠ 16 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 966 :=
    hpc.trans (rfl : (966 : Word) = UInt16.ofNat 966)
  have g (k : Nat) (h1 : 966 ≤ k) (h2 : k < 978) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (966 + off) :=
    word_pc_off 966 off hp (by omega)
  have m0 : s.mem.get s.pc = 16 := by
    rw [hp]
    have hval : decChunk060[6]! = 16 := rfl
    exact (g 966 (by decide) (by decide)).trans ((cell960 6 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 16 := by
    rw [poff 1 (by decide)]
    have hval : decChunk060[7]! = 16 := rfl
    exact (g 967 (by decide) (by decide)).trans ((cell960 7 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk060[8]! = 969 := rfl
    have hv : (969 : Word) = UInt16.ofNat 969 := rfl
    exact (g 968 (by decide) (by decide)).trans ((cell960 8 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 26 := by
    rw [poff 3 (by decide)]
    have hval : decChunk060[9]! = 26 := rfl
    exact (g 969 (by decide) (by decide)).trans ((cell960 9 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk060[10]! = 0 := rfl
    exact (g 970 (by decide) (by decide)).trans ((cell960 10 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk060[11]! = 972 := rfl
    have hv : (972 : Word) = UInt16.ofNat 972 := rfl
    exact (g 971 (by decide) (by decide)).trans ((cell960 11 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk060[12]! = 0 := rfl
    exact (g 972 (by decide) (by decide)).trans ((cell960 12 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 16 := by
    rw [poff 7 (by decide)]
    have hval : decChunk060[13]! = 16 := rfl
    exact (g 973 (by decide) (by decide)).trans ((cell960 13 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk060[14]! = 975 := rfl
    have hv : (975 : Word) = UInt16.ofNat 975 := rfl
    exact (g 974 (by decide) (by decide)).trans ((cell960 14 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk060[15]! = 0 := rfl
    exact (g 975 (by decide) (by decide)).trans ((cell960 15 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk061[0]! = 0 := rfl
    exact (g 976 (by decide) (by decide)).trans ((cell976 0 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk061[1]! = 978 := rfl
    have hv : (978 : Word) = UInt16.ofNat 978 := rfl
    exact (g 977 (by decide) (by decide)).trans ((cell976 1 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (16 : Word) := by
    intro i hi
    have : (16 : Word) = UInt16.ofNat 16 := rfl
    rw [this]
    exact pc_off_ne 966 i 16 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 966 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 26) (dst := 16)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 978 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (978 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 978 = (978 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- MOV CAP T at LEN_OK (pc 978). -/
theorem pad_mov_CAP_T {s : Machine}
    (hpc : s.pc = 978)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 978 ≤ k → k < 990 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 990 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 13 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 13 = s.mem.get 13 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 978 :=
    hpc.trans (rfl : (978 : Word) = UInt16.ofNat 978)
  have g (k : Nat) (h1 : 978 ≤ k) (h2 : k < 990) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (978 + off) :=
    word_pc_off 978 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk061[2]! = 18 := rfl
    exact (g 978 (by decide) (by decide)).trans ((cell976 2 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk061[3]! = 18 := rfl
    exact (g 979 (by decide) (by decide)).trans ((cell976 3 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk061[4]! = 981 := rfl
    have hv : (981 : Word) = UInt16.ofNat 981 := rfl
    exact (g 980 (by decide) (by decide)).trans ((cell976 4 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 13 := by
    rw [poff 3 (by decide)]
    have hval : decChunk061[5]! = 13 := rfl
    exact (g 981 (by decide) (by decide)).trans ((cell976 5 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk061[6]! = 0 := rfl
    exact (g 982 (by decide) (by decide)).trans ((cell976 6 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk061[7]! = 984 := rfl
    have hv : (984 : Word) = UInt16.ofNat 984 := rfl
    exact (g 983 (by decide) (by decide)).trans ((cell976 7 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk061[8]! = 0 := rfl
    exact (g 984 (by decide) (by decide)).trans ((cell976 8 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk061[9]! = 18 := rfl
    exact (g 985 (by decide) (by decide)).trans ((cell976 9 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk061[10]! = 987 := rfl
    have hv : (987 : Word) = UInt16.ofNat 987 := rfl
    exact (g 986 (by decide) (by decide)).trans ((cell976 10 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk061[11]! = 0 := rfl
    exact (g 987 (by decide) (by decide)).trans ((cell976 11 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk061[12]! = 0 := rfl
    exact (g 988 (by decide) (by decide)).trans ((cell976 12 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk061[13]! = 990 := rfl
    have hv : (990 : Word) = UInt16.ofNat 990 := rfl
    exact (g 989 (by decide) (by decide)).trans ((cell976 13 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 978 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 978 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 13) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 990 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (990 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 990 = (990 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JLEZ T DONE at pc 990 (CAP==0 halt). -/
theorem pad_enc_jlez_990 {s : Machine}
    (hpc : s.pc = 990)
    (hcode : ∀ k : Nat, 990 ≤ k → k < 990+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 2316 := by
  have hp : s.pc = UInt16.ofNat 990 :=
    hpc.trans (rfl : (990 : Word) = UInt16.ofNat 990)
  have g (k : Nat) (h1 : 990 ≤ k) (h2 : k < 990+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk061[14]! = 0 := rfl
    exact (g 990 (by decide) (by decide)).trans ((cell976 14 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (991 : Word) := by simp [hpc]
    rw [this, (rfl : (991 : Word) = UInt16.ofNat 991)]
    have hval : decChunk061[15]! = 18 := rfl
    exact (g 991 (by decide) (by decide)).trans ((cell976 15 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 2316 := by
    have : s.pc + 2 = (992 : Word) := by simp [hpc]
    rw [this, (rfl : (992 : Word) = UInt16.ofNat 992)]
    have hval : decChunk062[0]! = 2316 := rfl
    exact (g 992 (by decide) (by decide)).trans ((cell992 0 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CAP ROOM at pc 993. -/
theorem pad_mov_CAP_ROOM {s : Machine}
    (hpc : s.pc = 993)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 993 ≤ k → k < 1005 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1005 ∧
    s4.halted = false ∧
    s4.mem.get 28 = s.mem.get 13 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 13 = s.mem.get 13 ∧
    (∀ a, a ≠ 28 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 993 :=
    hpc.trans (rfl : (993 : Word) = UInt16.ofNat 993)
  have g (k : Nat) (h1 : 993 ≤ k) (h2 : k < 1005) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (993 + off) :=
    word_pc_off 993 off hp (by omega)
  have m0 : s.mem.get s.pc = 28 := by
    rw [hp]
    have hval : decChunk062[1]! = 28 := rfl
    exact (g 993 (by decide) (by decide)).trans ((cell992 1 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 28 := by
    rw [poff 1 (by decide)]
    have hval : decChunk062[2]! = 28 := rfl
    exact (g 994 (by decide) (by decide)).trans ((cell992 2 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk062[3]! = 996 := rfl
    have hv : (996 : Word) = UInt16.ofNat 996 := rfl
    exact (g 995 (by decide) (by decide)).trans ((cell992 3 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 13 := by
    rw [poff 3 (by decide)]
    have hval : decChunk062[4]! = 13 := rfl
    exact (g 996 (by decide) (by decide)).trans ((cell992 4 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk062[5]! = 0 := rfl
    exact (g 997 (by decide) (by decide)).trans ((cell992 5 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk062[6]! = 999 := rfl
    have hv : (999 : Word) = UInt16.ofNat 999 := rfl
    exact (g 998 (by decide) (by decide)).trans ((cell992 6 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk062[7]! = 0 := rfl
    exact (g 999 (by decide) (by decide)).trans ((cell992 7 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 28 := by
    rw [poff 7 (by decide)]
    have hval : decChunk062[8]! = 28 := rfl
    exact (g 1000 (by decide) (by decide)).trans ((cell992 8 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk062[9]! = 1002 := rfl
    have hv : (1002 : Word) = UInt16.ofNat 1002 := rfl
    exact (g 1001 (by decide) (by decide)).trans ((cell992 9 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk062[10]! = 0 := rfl
    exact (g 1002 (by decide) (by decide)).trans ((cell992 10 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk062[11]! = 0 := rfl
    exact (g 1003 (by decide) (by decide)).trans ((cell992 11 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk062[12]! = 1005 := rfl
    have hv : (1005 : Word) = UInt16.ofNat 1005 := rfl
    exact (g 1004 (by decide) (by decide)).trans ((cell992 12 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (28 : Word) := by
    intro i hi
    have : (28 : Word) = UInt16.ofNat 28 := rfl
    rw [this]
    exact pc_off_ne 993 i 28 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 993 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 13) (dst := 28)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1005 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1005 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1005 = (1005 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- DEC ROOM at pc 1005 (ROOM = CAP - 1). -/
theorem pad_dec_ROOM {s : Machine}
    (hpc : s.pc = 1005)
    (hh : s.halted = false)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1005 ≤ k → k < 1008 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s = { s with mem := s.mem.set 28 (s.mem.get 28 - 1), pc := 1008 } := by
  have hp : s.pc = UInt16.ofNat 1005 :=
    hpc.trans (rfl : (1005 : Word) = UInt16.ofNat 1005)
  have g (k : Nat) (h1 : 1005 ≤ k) (h2 : k < 1008) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk062[13]! = 3 := rfl
    exact (g 1005 (by decide) (by decide)).trans ((cell992 13 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 28 := by
    have : s.pc + 1 = (1006 : Word) := by simp [hpc]
    rw [this, (rfl : (1006 : Word) = UInt16.ofNat 1006)]
    have hval : decChunk062[14]! = 28 := rfl
    exact (g 1006 (by decide) (by decide)).trans ((cell992 14 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1007 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1008 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1007 : Word) = UInt16.ofNat 1007)]
    have hval : decChunk062[15]! = 1008 := rfl
    have hv : (1008 : Word) = UInt16.ofNat 1008 := rfl
    exact (g 1007 (by decide) (by decide)).trans ((cell992 15 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hd :=
    step_DEC (s := s) (x := 28) hh hpc0 hONE ha hb hc (by decide)
  have hpc' : s.pc + 3 = (1008 : Word) := by simp [hpc]
  rw [hd, hpc']

/-- ZERO IDX at pc 1008, then SP_LOOP. -/
theorem pad_zero_IDX {s : Machine}
    (hpc : s.pc = 1008)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1008 ≤ k → k < 1011 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s = { s with mem := s.mem.set 29 0, pc := 1011 } := by
  have hp : s.pc = UInt16.ofNat 1008 :=
    hpc.trans (rfl : (1008 : Word) = UInt16.ofNat 1008)
  have g (k : Nat) (h1 : 1008 ≤ k) (h2 : k < 1011) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 29 := by
    rw [hp]
    have hval : decChunk063[0]! = 29 := rfl
    exact (g 1008 (by decide) (by decide)).trans ((cell1008 0 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 29 := by
    have : s.pc + 1 = (1009 : Word) := by simp [hpc]
    rw [this, (rfl : (1009 : Word) = UInt16.ofNat 1009)]
    have hval : decChunk063[1]! = 29 := rfl
    exact (g 1009 (by decide) (by decide)).trans ((cell1008 1 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1010 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1011 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1010 : Word) = UInt16.ofNat 1010)]
    have hval : decChunk063[2]! = 1011 := rfl
    have hv : (1011 : Word) = UInt16.ofNat 1011 := rfl
    exact (g 1010 (by decide) (by decide)).trans ((cell1008 2 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hz :=
    step_ZERO (s := s) (x := 29) hh hpc0 ha hb hc (by decide)
  have hpc' : s.pc + 3 = (1011 : Word) := by simp [hpc]
  rw [hz, hpc']

/-- HALT at DONE (pc 2316). -/
theorem pad_enc_halt_2316 {s : Machine}
    (hpc : s.pc = 2316)
    (hcode : ∀ k : Nat, 2316 ≤ k → k < 2316+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 32768 := by
  have hp : s.pc = UInt16.ofNat 2316 :=
    hpc.trans (rfl : (2316 : Word) = UInt16.ofNat 2316)
  have g (k : Nat) (h1 : 2316 ≤ k) (h2 : k < 2316+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk144[12]! = 0 := rfl
    exact (g 2316 (by decide) (by decide)).trans ((cell2304 12 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (2317 : Word) := by simp [hpc]
    rw [this, (rfl : (2317 : Word) = UInt16.ofNat 2317)]
    have hval : decChunk144[13]! = 0 := rfl
    exact (g 2317 (by decide) (by decide)).trans ((cell2304 13 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 32768 := by
    have : s.pc + 2 = (2318 : Word) := by simp [hpc]
    rw [this, (rfl : (2318 : Word) = UInt16.ofNat 2318)]
    have hval : decChunk144[14]! = 32768 := rfl
    exact (g 2318 (by decide) (by decide)).trans ((cell2304 14 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV PAD T at SP_LOOP (pc 1011). -/
theorem pad_mov_PAD_T_1011 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1023 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1023 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 27 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 27 = s.mem.get 27 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1011 :=
    hpc.trans (rfl : (1011 : Word) = UInt16.ofNat 1011)
  have g (k : Nat) (h1 : 1011 ≤ k) (h2 : k < 1023) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1011 + off) :=
    word_pc_off 1011 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk063[3]! = 18 := rfl
    exact (g 1011 (by decide) (by decide)).trans ((cell1008 3 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk063[4]! = 18 := rfl
    exact (g 1012 (by decide) (by decide)).trans ((cell1008 4 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk063[5]! = 1014 := rfl
    have hv : (1014 : Word) = UInt16.ofNat 1014 := rfl
    exact (g 1013 (by decide) (by decide)).trans ((cell1008 5 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 27 := by
    rw [poff 3 (by decide)]
    have hval : decChunk063[6]! = 27 := rfl
    exact (g 1014 (by decide) (by decide)).trans ((cell1008 6 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk063[7]! = 0 := rfl
    exact (g 1015 (by decide) (by decide)).trans ((cell1008 7 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk063[8]! = 1017 := rfl
    have hv : (1017 : Word) = UInt16.ofNat 1017 := rfl
    exact (g 1016 (by decide) (by decide)).trans ((cell1008 8 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk063[9]! = 0 := rfl
    exact (g 1017 (by decide) (by decide)).trans ((cell1008 9 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk063[10]! = 18 := rfl
    exact (g 1018 (by decide) (by decide)).trans ((cell1008 10 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk063[11]! = 1020 := rfl
    have hv : (1020 : Word) = UInt16.ofNat 1020 := rfl
    exact (g 1019 (by decide) (by decide)).trans ((cell1008 11 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk063[12]! = 0 := rfl
    exact (g 1020 (by decide) (by decide)).trans ((cell1008 12 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk063[13]! = 0 := rfl
    exact (g 1021 (by decide) (by decide)).trans ((cell1008 13 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk063[14]! = 1023 := rfl
    have hv : (1023 : Word) = UInt16.ofNat 1023 := rfl
    exact (g 1022 (by decide) (by decide)).trans ((cell1008 14 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1011 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1011 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 27) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1023 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1023 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1023 = (1023 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JLEZ T AFTER_PAD at pc 1023. -/
theorem pad_enc_jlez_1023 {s : Machine}
    (hpc : s.pc = 1023)
    (hcode : ∀ k : Nat, 1023 ≤ k → k < 1023+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1077 := by
  have hp : s.pc = UInt16.ofNat 1023 :=
    hpc.trans (rfl : (1023 : Word) = UInt16.ofNat 1023)
  have g (k : Nat) (h1 : 1023 ≤ k) (h2 : k < 1023+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk063[15]! = 0 := rfl
    exact (g 1023 (by decide) (by decide)).trans ((cell1008 15 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1024 : Word) := by simp [hpc]
    rw [this, (rfl : (1024 : Word) = UInt16.ofNat 1024)]
    have hval : decChunk064[0]! = 18 := rfl
    exact (g 1024 (by decide) (by decide)).trans ((cell1024 0 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1077 := by
    have : s.pc + 2 = (1025 : Word) := by simp [hpc]
    rw [this, (rfl : (1025 : Word) = UInt16.ofNat 1025)]
    have hval : decChunk064[1]! = 1077 := rfl
    exact (g 1025 (by decide) (by decide)).trans ((cell1024 1 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-! ### HAVE_DIG: RAW = NDIG + (1 if SIGN ≠ 0 else 0) -/

/-- `SIGN = 0`: 9 steps from `HAVE_DIG` to `RAW_OK`, `RAW = NDIG`. -/
theorem have_dig_sign0 {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hS : s.mem.get 19 = 0)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 894 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s9 := runN s 9
    s9.pc = 903 ∧
    s9.halted = false ∧
    s9.mem.get 0 = 0 ∧
    s9.mem.get 26 = s.mem.get 25 ∧
    (∀ a, a ≠ 26 → a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a) := by
  intro s9
  have hm0 := pad_mov_NDIG_RAW (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 879 := hm0.1
  have hs4h : s4.halted = false := hm0.2.1
  have hs4R : s4.mem.get 26 = s.mem.get 25 := hm0.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm0.2.2.2.1
  have hpres4 := hm0.2.2.2.2.2
  have hS4 : s4.mem.get 19 = 0 := (hpres4 19 (by decide) (by decide)).trans hS
  have g4 : ∀ k : Nat, 879 ≤ k → k < 891 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n26 n0).trans (hcode k (by omega) (by omega))
  have hm1 := pad_mov_SIGN_T (s := s4) hs4pc hs4h hs4Z g4
  have hrun8 : runN s 8 = runN s4 4 := runN_add_eq s 4 4 8 (by decide)
  let s8 := runN s 8
  have hs8pc : s8.pc = 891 := by
    have : s8 = runN s4 4 := hrun8
    rw [this]; exact hm1.1
  have hs8h : s8.halted = false := by
    have : s8 = runN s4 4 := hrun8
    rw [this]; exact hm1.2.1
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = runN s4 4 := hrun8
    rw [this]; exact hm1.2.2.2.1
  have hs8T : s8.mem.get 18 = 0 := by
    have : s8 = runN s4 4 := hrun8
    rw [this]; exact hm1.2.2.1.trans hS4
  have hs8R : s8.mem.get 26 = s.mem.get 25 := by
    have : s8 = runN s4 4 := hrun8
    rw [this]
    exact (hm1.2.2.2.2.2 26 (by decide) (by decide)).trans hs4R
  have hpres8 : ∀ a, a ≠ 26 → a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha26 ha18 ha0
    have : s8 = runN s4 4 := hrun8
    rw [this]
    exact (hm1.2.2.2.2.2 a ha18 ha0).trans (hpres4 a ha26 ha0)
  have g8 : ∀ k : Nat, 891 ≤ k → k < 894 →
      s8.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres8 (UInt16.ofNat k) (by
        have : (26 : Word) = UInt16.ofNat 26 := rfl
        rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega))
      n18 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_jlez_891 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez :=
    step_JLEZ (s := s8) (x := 18) (dest := 903)
      hs8h hpc8 hs8Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = true := by
    have : le0 (s8.mem.get 18) = true := by
      rw [hs8T]; exact le0_zero
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 903 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (903 : Word) else s8.pc + 3) = (903 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hrun : s9 = step s8 := by
    have h9 : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact h9.trans (runN_one s8 hs8h hpc8)
  have hs9pc : s9.pc = 903 := by rw [hrun, hs9eq]
  have hs9h : s9.halted = false := by rw [hrun, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by rw [hrun, hs9eq]; exact hs8Z
  have hs9R : s9.mem.get 26 = s.mem.get 25 := by rw [hrun, hs9eq]; exact hs8R
  have hpres9 : ∀ a, a ≠ 26 → a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha26 ha18 ha0
    rw [hrun, hs9eq]
    exact hpres8 a ha26 ha18 ha0
  exact ⟨hs9pc, hs9h, hs9Z, hs9R, hpres9⟩

/-- Non-zero, non-negative `SIGN` (the assembled path writes `SIGN = 1`).
12 steps from `HAVE_DIG` to `RAW_OK`, `RAW = NDIG + 1`. -/
theorem have_dig_sign_nz {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hlo : 0 < (s.mem.get 19).toNat)
    (hhi : (s.mem.get 19).toNat < 32768)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 903 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s12 := runN s 12
    s12.pc = 903 ∧
    s12.halted = false ∧
    s12.mem.get 0 = 0 ∧
    s12.mem.get 26 = s.mem.get 25 + 1 ∧
    (∀ a, a ≠ 26 → a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a) := by
  intro s12
  have hm0 := pad_mov_NDIG_RAW (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 879 := hm0.1
  have hs4h : s4.halted = false := hm0.2.1
  have hs4R : s4.mem.get 26 = s.mem.get 25 := hm0.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm0.2.2.2.1
  have hpres4 := hm0.2.2.2.2.2
  have hS4 : s4.mem.get 19 = s.mem.get 19 := hpres4 19 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 : ∀ k : Nat, 879 ≤ k → k < 891 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n26 n0).trans (hcode k (by omega) (by omega))
  have hm1 := pad_mov_SIGN_T (s := s4) hs4pc hs4h hs4Z g4
  have hrun8 : runN s 8 = runN s4 4 := runN_add_eq s 4 4 8 (by decide)
  let s8 := runN s 8
  have hs8pc : s8.pc = 891 := by
    have : s8 = runN s4 4 := hrun8
    rw [this]; exact hm1.1
  have hs8h : s8.halted = false := by
    have : s8 = runN s4 4 := hrun8
    rw [this]; exact hm1.2.1
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = runN s4 4 := hrun8
    rw [this]; exact hm1.2.2.2.1
  have hs8T : s8.mem.get 18 = s.mem.get 19 := by
    have : s8 = runN s4 4 := hrun8
    rw [this]; exact hm1.2.2.1.trans hS4
  have hs8R : s8.mem.get 26 = s.mem.get 25 := by
    have : s8 = runN s4 4 := hrun8
    rw [this]
    exact (hm1.2.2.2.2.2 26 (by decide) (by decide)).trans hs4R
  have hpres8 : ∀ a, a ≠ 26 → a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha26 ha18 ha0
    have : s8 = runN s4 4 := hrun8
    rw [this]
    exact (hm1.2.2.2.2.2 a ha18 ha0).trans (hpres4 a ha26 ha0)
  have hONE8 : s8.mem.get 3 = 1 := (hpres8 3 (by decide) (by decide) (by decide)).trans hONE
  have g8 : ∀ k : Nat, 891 ≤ k → k < 894 →
      s8.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres8 (UInt16.ofNat k) n26 n18 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_jlez_891 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez :=
    step_JLEZ (s := s8) (x := 18) (dest := 903)
      hs8h hpc8 hs8Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos hlo hhi
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 894 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (903 : Word) else s8.pc + 3) = (894 : Word) := by
      have hfall : s8.pc + 3 = (894 : Word) := by simp [hs8pc]
      simp [hle, hfall]
    rw [hjlez, hif]
  have hrun9 : runN s 9 = step s8 := by
    have h9 : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact h9.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 894 := by
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]
  have hs9h : s9.halted = false := by
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hs8Z
  have hs9R : s9.mem.get 26 = s.mem.get 25 := by
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hs8R
  have hpres9 : ∀ a, a ≠ 26 → a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha26 ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]
    exact hpres8 a ha26 ha18 ha0
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide) (by decide)).trans hONE
  have g9 : ∀ k : Nat, 894 ≤ k → k < 903 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n26 n18 n0).trans (hcode k (by omega) (by omega))
  have hi := pad_inc_RAW (s := s9) hs9pc hs9h hs9Z hONE9 g9
  have hrun : s12 = runN s9 3 := runN_add_eq s 9 3 12 (by decide)
  have hs12pc : s12.pc = 903 := by rw [hrun]; exact hi.1
  have hs12h : s12.halted = false := by rw [hrun]; exact hi.2.1
  have hs12Z : s12.mem.get 0 = 0 := by rw [hrun]; exact hi.2.2.2.1
  have hs12R : s12.mem.get 26 = s.mem.get 25 + 1 := by
    rw [hrun]
    exact hi.2.2.1.trans (by rw [hs9R])
  have hpres : ∀ a, a ≠ 26 → a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha26 ha18 ha0
    rw [hrun]
    exact (hi.2.2.2.2 a ha26 ha0).trans (hpres9 a ha26 ha18 ha0)
  exact ⟨hs12pc, hs12h, hs12Z, hs12R, hpres⟩

/-! ### RAW_OK: PAD / LEN versus WIDTH -/

/-- `WIDTH = 0`: 10 steps from `RAW_OK` to `LEN_OK`, `PAD = 0`, `LEN = RAW`. -/
theorem pad_len_width0 {s : Machine}
    (hpc : s.pc = 903)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hW : s.mem.get 14 = 0)
    (hcode : ∀ k : Nat, 903 ≤ k → k < 978 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s10 := runN s 10
    s10.pc = 978 ∧
    s10.halted = false ∧
    s10.mem.get 0 = 0 ∧
    s10.mem.get 27 = 0 ∧
    s10.mem.get 16 = s.mem.get 26 ∧
    (∀ a, a ≠ 27 → a ≠ 18 → a ≠ 16 → a ≠ 0 → s10.mem.get a = s.mem.get a) := by
  intro s10
  have hz := pad_zero_PAD (s := s) hpc hh
    (fun k h1 h2 => hcode k h1 (by omega))
  have hs1eq : step s = { s with mem := s.mem.set 27 0, pc := 906 } := hz
  have hs1pc : (step s).pc = 906 := by rw [hs1eq]
  have hs1h : (step s).halted = false := by rw [hs1eq]; exact hh
  have hs1Z : (step s).mem.get 0 = 0 := by
    rw [hs1eq]
    exact (Mem.get_set_ne s.mem 27 0 0 (by decide)).trans hZ
  have hs1P : (step s).mem.get 27 = 0 := by rw [hs1eq, Mem.get_set_eq]
  have hW1 : (step s).mem.get 14 = 0 := by
    rw [hs1eq]
    exact (Mem.get_set_ne s.mem 27 14 0 (by decide)).trans hW
  have hR1 : (step s).mem.get 26 = s.mem.get 26 := by
    rw [hs1eq]
    exact Mem.get_set_ne s.mem 27 26 0 (by decide)
  have hpres1 : ∀ a, a ≠ 27 → a ≠ 0 → (step s).mem.get a = s.mem.get a := by
    intro a ha27 ha0
    rw [hs1eq]
    exact Mem.get_set_ne s.mem 27 a 0 ha27
  have g1 : ∀ k : Nat, 906 ≤ k → k < 918 →
      (step s).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres1 (UInt16.ofNat k) n27 n0).trans (hcode k (by omega) (by omega))
  have hm := pad_mov_WIDTH_T_906 (s := step s) hs1pc hs1h hs1Z g1
  have hrun5 : runN s 5 = runN (step s) 4 := by
    have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
    exact (runN_succ_go s 4 hh hpc0)
  let s5 := runN s 5
  have hs5pc : s5.pc = 918 := by
    have : s5 = runN (step s) 4 := hrun5
    rw [this]; exact hm.1
  have hs5h : s5.halted = false := by
    have : s5 = runN (step s) 4 := hrun5
    rw [this]; exact hm.2.1
  have hs5Z : s5.mem.get 0 = 0 := by
    have : s5 = runN (step s) 4 := hrun5
    rw [this]; exact hm.2.2.2.1
  have hs5T : s5.mem.get 18 = 0 := by
    have : s5 = runN (step s) 4 := hrun5
    rw [this]; exact hm.2.2.1.trans hW1
  have hs5P : s5.mem.get 27 = 0 := by
    have : s5 = runN (step s) 4 := hrun5
    rw [this]
    exact (hm.2.2.2.2.2 27 (by decide) (by decide)).trans hs1P
  have hs5R : s5.mem.get 26 = s.mem.get 26 := by
    have : s5 = runN (step s) 4 := hrun5
    rw [this]
    exact (hm.2.2.2.2.2 26 (by decide) (by decide)).trans hR1
  have hpres5 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha0
    have : s5 = runN (step s) 4 := hrun5
    rw [this]
    exact (hm.2.2.2.2.2 a ha18 ha0).trans (hpres1 a ha27 ha0)
  have g5 : ∀ k : Nat, 918 ≤ k → k < 921 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n27 n18 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_jlez_918 (s := s5) hs5pc g5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hjlez :=
    step_JLEZ (s := s5) (x := 18) (dest := 966)
      hs5h hpc5 hs5Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = true := by
    have : le0 (s5.mem.get 18) = true := by
      rw [hs5T]; exact le0_zero
    simpa [le0] using this
  have hs6eq : step s5 = { s5 with pc := 966 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (966 : Word) else s5.pc + 3) = (966 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hs6pc : s6.pc = 966 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
  have hs6h : s6.halted = false := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]; exact hs5Z
  have hs6P : s6.mem.get 27 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]; exact hs5P
  have hs6R : s6.mem.get 26 = s.mem.get 26 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]; exact hs5R
  have hpres6 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact hpres5 a ha27 ha18 ha0
  have g6 : ∀ k : Nat, 966 ≤ k → k < 978 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n27 n18 n0).trans (hcode k (by omega) (by omega))
  have hmL := pad_mov_RAW_LEN (s := s6) hs6pc hs6h hs6Z g6
  have hrun : s10 = runN s6 4 := runN_add_eq s 6 4 10 (by decide)
  have hs10pc : s10.pc = 978 := by rw [hrun]; exact hmL.1
  have hs10h : s10.halted = false := by rw [hrun]; exact hmL.2.1
  have hs10Z : s10.mem.get 0 = 0 := by rw [hrun]; exact hmL.2.2.2.1
  have hs10L : s10.mem.get 16 = s.mem.get 26 := by
    rw [hrun]
    exact hmL.2.2.1.trans hs6R
  have hs10P : s10.mem.get 27 = 0 := by
    rw [hrun]
    exact (hmL.2.2.2.2.2 27 (by decide) (by decide)).trans hs6P
  have hpres : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 16 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha16 ha0
    rw [hrun]
    exact (hmL.2.2.2.2.2 a ha16 ha0).trans (hpres6 a ha27 ha18 ha0)
  exact ⟨hs10pc, hs10h, hs10Z, hs10P, hs10L, hpres⟩

/-- `0 < WIDTH ≤ RAW` (both below the sign bit): 16 steps to `LEN_OK`,
`PAD = 0`, `LEN = RAW`. -/
theorem pad_len_le_raw {s : Machine}
    (hpc : s.pc = 903)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hWlo : 0 < (s.mem.get 14).toNat)
    (hWhi : (s.mem.get 14).toNat < 32768)
    (hle : (s.mem.get 14).toNat ≤ (s.mem.get 26).toNat)
    (hRhi : (s.mem.get 26).toNat < 32768)
    (hcode : ∀ k : Nat, 903 ≤ k → k < 978 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s16 := runN s 16
    s16.pc = 978 ∧
    s16.halted = false ∧
    s16.mem.get 0 = 0 ∧
    s16.mem.get 27 = 0 ∧
    s16.mem.get 16 = s.mem.get 26 ∧
    (∀ a, a ≠ 27 → a ≠ 18 → a ≠ 16 → a ≠ 0 → s16.mem.get a = s.mem.get a) := by
  intro s16
  have hz := pad_zero_PAD (s := s) hpc hh
    (fun k h1 h2 => hcode k h1 (by omega))
  have hs1eq : step s = { s with mem := s.mem.set 27 0, pc := 906 } := hz
  have hs1pc : (step s).pc = 906 := by rw [hs1eq]
  have hs1h : (step s).halted = false := by rw [hs1eq]; exact hh
  have hs1Z : (step s).mem.get 0 = 0 := by
    rw [hs1eq]
    exact (Mem.get_set_ne s.mem 27 0 0 (by decide)).trans hZ
  have hs1P : (step s).mem.get 27 = 0 := by rw [hs1eq, Mem.get_set_eq]
  have hW1 : (step s).mem.get 14 = s.mem.get 14 := by
    rw [hs1eq]; exact Mem.get_set_ne s.mem 27 14 0 (by decide)
  have hR1 : (step s).mem.get 26 = s.mem.get 26 := by
    rw [hs1eq]; exact Mem.get_set_ne s.mem 27 26 0 (by decide)
  have hpres1 : ∀ a, a ≠ 27 → a ≠ 0 → (step s).mem.get a = s.mem.get a := by
    intro a ha27 ha0
    rw [hs1eq]; exact Mem.get_set_ne s.mem 27 a 0 ha27
  have g1 : ∀ k : Nat, 906 ≤ k → k < 918 →
      (step s).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres1 (UInt16.ofNat k) n27 n0).trans (hcode k (by omega) (by omega))
  have hm := pad_mov_WIDTH_T_906 (s := step s) hs1pc hs1h hs1Z g1
  have hrun5 : runN s 5 = runN (step s) 4 := by
    have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
    exact runN_succ_go s 4 hh hpc0
  let s5 := runN s 5
  have hs5pc : s5.pc = 918 := by
    have : s5 = runN (step s) 4 := hrun5; rw [this]; exact hm.1
  have hs5h : s5.halted = false := by
    have : s5 = runN (step s) 4 := hrun5; rw [this]; exact hm.2.1
  have hs5Z : s5.mem.get 0 = 0 := by
    have : s5 = runN (step s) 4 := hrun5; rw [this]; exact hm.2.2.2.1
  have hs5T : s5.mem.get 18 = s.mem.get 14 := by
    have : s5 = runN (step s) 4 := hrun5
    rw [this]; exact hm.2.2.1.trans hW1
  have hs5P : s5.mem.get 27 = 0 := by
    have : s5 = runN (step s) 4 := hrun5
    rw [this]; exact (hm.2.2.2.2.2 27 (by decide) (by decide)).trans hs1P
  have hs5R : s5.mem.get 26 = s.mem.get 26 := by
    have : s5 = runN (step s) 4 := hrun5
    rw [this]; exact (hm.2.2.2.2.2 26 (by decide) (by decide)).trans hR1
  have hW5 : s5.mem.get 14 = s.mem.get 14 := by
    have : s5 = runN (step s) 4 := hrun5
    rw [this]; exact (hm.2.2.2.2.2 14 (by decide) (by decide)).trans hW1
  have hpres5 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha0
    have : s5 = runN (step s) 4 := hrun5
    rw [this]; exact (hm.2.2.2.2.2 a ha18 ha0).trans (hpres1 a ha27 ha0)
  have g5 : ∀ k : Nat, 918 ≤ k → k < 921 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n27 n18 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_jlez_918 (s := s5) hs5pc g5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hjlez :=
    step_JLEZ (s := s5) (x := 18) (dest := 966)
      hs5h hpc5 hs5Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle5 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = false := by
    have : le0 (s5.mem.get 18) = false := by
      rw [hs5T]; exact le0_pos hWlo hWhi
    simpa [le0] using this
  have hs6eq : step s5 = { s5 with pc := 921 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (966 : Word) else s5.pc + 3) = (921 : Word) := by
      have hfall : s5.pc + 3 = (921 : Word) := by simp [hs5pc]
      simp [hle5, hfall]
    rw [hjlez, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hs6pc : s6.pc = 921 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5Z
  have hs6P : s6.mem.get 27 = 0 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5P
  have hs6R : s6.mem.get 26 = s.mem.get 26 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5R
  have hW6 : s6.mem.get 14 = s.mem.get 14 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]; exact hW5
  have hpres6 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]; exact hpres5 a ha27 ha18 ha0
  have g6 : ∀ k : Nat, 921 ≤ k → k < 933 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n27 n18 n0).trans (hcode k (by omega) (by omega))
  have hm2 := pad_mov_WIDTH_T_921 (s := s6) hs6pc hs6h hs6Z g6
  have hrun10 : runN s 10 = runN s6 4 := runN_add_eq s 6 4 10 (by decide)
  let s10 := runN s 10
  have hs10pc : s10.pc = 933 := by have : s10 = runN s6 4 := hrun10; rw [this]; exact hm2.1
  have hs10h : s10.halted = false := by have : s10 = runN s6 4 := hrun10; rw [this]; exact hm2.2.1
  have hs10Z : s10.mem.get 0 = 0 := by have : s10 = runN s6 4 := hrun10; rw [this]; exact hm2.2.2.2.1
  have hs10T : s10.mem.get 18 = s.mem.get 14 := by
    have : s10 = runN s6 4 := hrun10
    rw [this]; exact hm2.2.2.1.trans hW6
  have hs10P : s10.mem.get 27 = 0 := by
    have : s10 = runN s6 4 := hrun10
    rw [this]; exact (hm2.2.2.2.2.2 27 (by decide) (by decide)).trans hs6P
  have hs10R : s10.mem.get 26 = s.mem.get 26 := by
    have : s10 = runN s6 4 := hrun10
    rw [this]; exact (hm2.2.2.2.2.2 26 (by decide) (by decide)).trans hs6R
  have hpres10 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha0
    have : s10 = runN s6 4 := hrun10
    rw [this]; exact (hm2.2.2.2.2.2 a ha18 ha0).trans (hpres6 a ha27 ha18 ha0)
  have g10 : ∀ k : Nat, 933 ≤ k → k < 936 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n27 n18 n0).trans (hcode k (by omega) (by omega))
  have hsub := pad_sub_RAW_T (s := s10) hs10pc hs10h g10
  have hs11eq : step s10 =
      { s10 with mem := s10.mem.set 18 (s10.mem.get 18 - s10.mem.get 26), pc := 936 } := hsub
  have hs11pc : (step s10).pc = 936 := by rw [hs11eq]
  have hs11h : (step s10).halted = false := by rw [hs11eq]; exact hs10h
  have hs11Z : (step s10).mem.get 0 = 0 := by
    rw [hs11eq]
    exact (Mem.get_set_ne s10.mem 18 0 (s10.mem.get 18 - s10.mem.get 26) (by decide)).trans hs10Z
  have hs11T : (step s10).mem.get 18 = s.mem.get 14 - s.mem.get 26 := by
    rw [hs11eq, Mem.get_set_eq, hs10T, hs10R]
  have hs11P : (step s10).mem.get 27 = 0 := by
    rw [hs11eq]
    exact (Mem.get_set_ne s10.mem 18 27 (s10.mem.get 18 - s10.mem.get 26) (by decide)).trans hs10P
  have hs11R : (step s10).mem.get 26 = s.mem.get 26 := by
    rw [hs11eq]
    exact (Mem.get_set_ne s10.mem 18 26 (s10.mem.get 18 - s10.mem.get 26) (by decide)).trans hs10R
  have hpres11 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 0 → (step s10).mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha0
    rw [hs11eq]
    exact (Mem.get_set_ne s10.mem 18 a (s10.mem.get 18 - s10.mem.get 26) ha18).trans
      (hpres10 a ha27 ha18 ha0)
  have g11 : ∀ k : Nat, 936 ≤ k → k < 939 →
      (step s10).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres11 (UInt16.ofNat k) n27 n18 n0).trans (hcode k (by omega) (by omega))
  have henc2 := pad_enc_jlez_936 (s := step s10) hs11pc g11
  have hpc11 : (step s10).pc.toNat < 32768 := by simp [hs11pc]
  have hjlez2 :=
    step_JLEZ (s := step s10) (x := 18) (dest := 966)
      hs11h hpc11 hs11Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle11 : ((step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18) = true := by
    have : le0 ((step s10).mem.get 18) = true := by
      rw [hs11T]
      cases Nat.eq_or_lt_of_le hle with
      | inl hEq =>
        have hW : (s.mem.get 14).toNat = (s.mem.get 26).toNat := hEq
        have : s.mem.get 14 = s.mem.get 26 :=
          UInt16.toNat.inj hW
        rw [this]
        have : s.mem.get 26 - s.mem.get 26 = 0 := by simp
        rw [this]; exact le0_zero
      | inr hLt =>
        have htn := word_sub_lt (s.mem.get 14) (s.mem.get 26) hLt
        have hhi : 32768 ≤ (s.mem.get 14 - s.mem.get 26).toNat := by omega
        exact le0_hi hhi
    simpa [le0] using this
  have hs12eq : step (step s10) = { step s10 with pc := 966 } := by
    have hif :
        (if (step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18
          then (966 : Word) else (step s10).pc + 3) = (966 : Word) := by
      simp [hle11]
    rw [hjlez2, hif]
  have hrun12 : runN s 12 = step (step s10) := by
    have h12 : runN s 12 = runN s10 2 := runN_add_eq s 10 2 12 (by decide)
    exact h12.trans (runN_2_steps s10 hs10h (by simp [hs10pc]) hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 966 := by have : s12 = step (step s10) := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step (step s10) := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by have : s12 = step (step s10) := hrun12; rw [this, hs12eq]; exact hs11Z
  have hs12P : s12.mem.get 27 = 0 := by have : s12 = step (step s10) := hrun12; rw [this, hs12eq]; exact hs11P
  have hs12R : s12.mem.get 26 = s.mem.get 26 := by have : s12 = step (step s10) := hrun12; rw [this, hs12eq]; exact hs11R
  have hpres12 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha0
    have : s12 = step (step s10) := hrun12
    rw [this, hs12eq]; exact hpres11 a ha27 ha18 ha0
  have g12 : ∀ k : Nat, 966 ≤ k → k < 978 →
      s12.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres12 (UInt16.ofNat k) n27 n18 n0).trans (hcode k (by omega) (by omega))
  have hmL := pad_mov_RAW_LEN (s := s12) hs12pc hs12h hs12Z g12
  have hrun : s16 = runN s12 4 := runN_add_eq s 12 4 16 (by decide)
  have hs16pc : s16.pc = 978 := by rw [hrun]; exact hmL.1
  have hs16h : s16.halted = false := by rw [hrun]; exact hmL.2.1
  have hs16Z : s16.mem.get 0 = 0 := by rw [hrun]; exact hmL.2.2.2.1
  have hs16L : s16.mem.get 16 = s.mem.get 26 := by rw [hrun]; exact hmL.2.2.1.trans hs12R
  have hs16P : s16.mem.get 27 = 0 := by
    rw [hrun]; exact (hmL.2.2.2.2.2 27 (by decide) (by decide)).trans hs12P
  have hpres : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 16 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha16 ha0
    rw [hrun]; exact (hmL.2.2.2.2.2 a ha16 ha0).trans (hpres12 a ha27 ha18 ha0)
  exact ⟨hs16pc, hs16h, hs16Z, hs16P, hs16L, hpres⟩

/-- `RAW < WIDTH` (both below the sign bit): 21 steps to `LEN_OK`,
`PAD = WIDTH - RAW`, `LEN = WIDTH`. -/
theorem pad_len_gt_raw {s : Machine}
    (hpc : s.pc = 903)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hLt : (s.mem.get 26).toNat < (s.mem.get 14).toNat)
    (hWhi : (s.mem.get 14).toNat < 32768)
    (hcode : ∀ k : Nat, 903 ≤ k → k < 978 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s21 := runN s 21
    s21.pc = 978 ∧
    s21.halted = false ∧
    s21.mem.get 0 = 0 ∧
    s21.mem.get 27 = s.mem.get 14 - s.mem.get 26 ∧
    s21.mem.get 16 = s.mem.get 14 ∧
    (∀ a, a ≠ 27 → a ≠ 18 → a ≠ 16 → a ≠ 0 → s21.mem.get a = s.mem.get a) := by
  intro s21
  have hWlo : 0 < (s.mem.get 14).toNat := by omega
  have hz := pad_zero_PAD (s := s) hpc hh
    (fun k h1 h2 => hcode k h1 (by omega))
  have hs1eq : step s = { s with mem := s.mem.set 27 0, pc := 906 } := hz
  have hs1pc : (step s).pc = 906 := by rw [hs1eq]
  have hs1h : (step s).halted = false := by rw [hs1eq]; exact hh
  have hs1Z : (step s).mem.get 0 = 0 := by
    rw [hs1eq]; exact (Mem.get_set_ne s.mem 27 0 0 (by decide)).trans hZ
  have hW1 : (step s).mem.get 14 = s.mem.get 14 := by
    rw [hs1eq]; exact Mem.get_set_ne s.mem 27 14 0 (by decide)
  have hR1 : (step s).mem.get 26 = s.mem.get 26 := by
    rw [hs1eq]; exact Mem.get_set_ne s.mem 27 26 0 (by decide)
  have hpres1 : ∀ a, a ≠ 27 → a ≠ 0 → (step s).mem.get a = s.mem.get a := by
    intro a ha27 ha0
    rw [hs1eq]; exact Mem.get_set_ne s.mem 27 a 0 ha27
  have g1 : ∀ k : Nat, 906 ≤ k → k < 918 →
      (step s).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres1 (UInt16.ofNat k) n27 n0).trans (hcode k (by omega) (by omega))
  have hm := pad_mov_WIDTH_T_906 (s := step s) hs1pc hs1h hs1Z g1
  have hrun5 : runN s 5 = runN (step s) 4 := by
    have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
    exact runN_succ_go s 4 hh hpc0
  let s5 := runN s 5
  have hs5pc : s5.pc = 918 := by have : s5 = runN (step s) 4 := hrun5; rw [this]; exact hm.1
  have hs5h : s5.halted = false := by have : s5 = runN (step s) 4 := hrun5; rw [this]; exact hm.2.1
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = runN (step s) 4 := hrun5; rw [this]; exact hm.2.2.2.1
  have hs5T : s5.mem.get 18 = s.mem.get 14 := by
    have : s5 = runN (step s) 4 := hrun5; rw [this]; exact hm.2.2.1.trans hW1
  have hs5R : s5.mem.get 26 = s.mem.get 26 := by
    have : s5 = runN (step s) 4 := hrun5
    rw [this]; exact (hm.2.2.2.2.2 26 (by decide) (by decide)).trans hR1
  have hW5 : s5.mem.get 14 = s.mem.get 14 := by
    have : s5 = runN (step s) 4 := hrun5
    rw [this]; exact (hm.2.2.2.2.2 14 (by decide) (by decide)).trans hW1
  have hpres5 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha0
    have : s5 = runN (step s) 4 := hrun5
    rw [this]; exact (hm.2.2.2.2.2 a ha18 ha0).trans (hpres1 a ha27 ha0)
  have g5 : ∀ k : Nat, 918 ≤ k → k < 921 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n27 n18 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_jlez_918 (s := s5) hs5pc g5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hjlez :=
    step_JLEZ (s := s5) (x := 18) (dest := 966)
      hs5h hpc5 hs5Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle5 : (s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18) = false := by
    have : le0 (s5.mem.get 18) = false := by
      rw [hs5T]; exact le0_pos hWlo hWhi
    simpa [le0] using this
  have hs6eq : step s5 = { s5 with pc := 921 } := by
    have hif :
        (if s5.mem.get 18 = 0 || 0x8000 ≤ s5.mem.get 18
          then (966 : Word) else s5.pc + 3) = (921 : Word) := by
      have hfall : s5.pc + 3 = (921 : Word) := by simp [hs5pc]
      simp [hle5, hfall]
    rw [hjlez, hif]
  have hrun6 : runN s 6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  let s6 := runN s 6
  have hs6pc : s6.pc = 921 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5Z
  have hs6R : s6.mem.get 26 = s.mem.get 26 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5R
  have hW6 : s6.mem.get 14 = s.mem.get 14 := by
    have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hW5
  have hpres6 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]; exact hpres5 a ha27 ha18 ha0
  have g6 : ∀ k : Nat, 921 ≤ k → k < 933 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n27 n18 n0).trans (hcode k (by omega) (by omega))
  have hm2 := pad_mov_WIDTH_T_921 (s := s6) hs6pc hs6h hs6Z g6
  have hrun10 : runN s 10 = runN s6 4 := runN_add_eq s 6 4 10 (by decide)
  let s10 := runN s 10
  have hs10pc : s10.pc = 933 := by have : s10 = runN s6 4 := hrun10; rw [this]; exact hm2.1
  have hs10h : s10.halted = false := by have : s10 = runN s6 4 := hrun10; rw [this]; exact hm2.2.1
  have hs10Z : s10.mem.get 0 = 0 := by have : s10 = runN s6 4 := hrun10; rw [this]; exact hm2.2.2.2.1
  have hs10T : s10.mem.get 18 = s.mem.get 14 := by
    have : s10 = runN s6 4 := hrun10; rw [this]; exact hm2.2.2.1.trans hW6
  have hs10R : s10.mem.get 26 = s.mem.get 26 := by
    have : s10 = runN s6 4 := hrun10
    rw [this]; exact (hm2.2.2.2.2.2 26 (by decide) (by decide)).trans hs6R
  have hW10 : s10.mem.get 14 = s.mem.get 14 := by
    have : s10 = runN s6 4 := hrun10
    rw [this]; exact (hm2.2.2.2.2.2 14 (by decide) (by decide)).trans hW6
  have hpres10 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha0
    have : s10 = runN s6 4 := hrun10
    rw [this]; exact (hm2.2.2.2.2.2 a ha18 ha0).trans (hpres6 a ha27 ha18 ha0)
  have g10 : ∀ k : Nat, 933 ≤ k → k < 936 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n27 n18 n0).trans (hcode k (by omega) (by omega))
  have hsub := pad_sub_RAW_T (s := s10) hs10pc hs10h g10
  have hs11eq : step s10 =
      { s10 with mem := s10.mem.set 18 (s10.mem.get 18 - s10.mem.get 26), pc := 936 } := hsub
  have hs11pc : (step s10).pc = 936 := by rw [hs11eq]
  have hs11h : (step s10).halted = false := by rw [hs11eq]; exact hs10h
  have hs11Z : (step s10).mem.get 0 = 0 := by
    rw [hs11eq]
    exact (Mem.get_set_ne s10.mem 18 0 (s10.mem.get 18 - s10.mem.get 26) (by decide)).trans hs10Z
  have hs11T : (step s10).mem.get 18 = s.mem.get 14 - s.mem.get 26 := by
    rw [hs11eq, Mem.get_set_eq, hs10T, hs10R]
  have hW11 : (step s10).mem.get 14 = s.mem.get 14 := by
    rw [hs11eq]
    exact (Mem.get_set_ne s10.mem 18 14 (s10.mem.get 18 - s10.mem.get 26) (by decide)).trans hW10
  have hpres11 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 0 → (step s10).mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha0
    rw [hs11eq]
    exact (Mem.get_set_ne s10.mem 18 a (s10.mem.get 18 - s10.mem.get 26) ha18).trans
      (hpres10 a ha27 ha18 ha0)
  have g11 : ∀ k : Nat, 936 ≤ k → k < 939 →
      (step s10).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres11 (UInt16.ofNat k) n27 n18 n0).trans (hcode k (by omega) (by omega))
  have henc2 := pad_enc_jlez_936 (s := step s10) hs11pc g11
  have hpc11 : (step s10).pc.toNat < 32768 := by simp [hs11pc]
  have hjlez2 :=
    step_JLEZ (s := step s10) (x := 18) (dest := 966)
      hs11h hpc11 hs11Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle11 : ((step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18) = false := by
    have : le0 ((step s10).mem.get 18) = false := by
      rw [hs11T]
      have htn := word_sub_ge (s.mem.get 14) (s.mem.get 26) (by omega)
      have hpos : 0 < (s.mem.get 14 - s.mem.get 26).toNat := by omega
      have hlt : (s.mem.get 14 - s.mem.get 26).toNat < 32768 := by omega
      exact le0_pos hpos hlt
    simpa [le0] using this
  have hs12eq : step (step s10) = { step s10 with pc := 939 } := by
    have hif :
        (if (step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18
          then (966 : Word) else (step s10).pc + 3) = (939 : Word) := by
      have hfall : (step s10).pc + 3 = (939 : Word) := by simp [hs11pc]
      simp [hle11, hfall]
    rw [hjlez2, hif]
  have hrun12 : runN s 12 = step (step s10) := by
    have h12 : runN s 12 = runN s10 2 := runN_add_eq s 10 2 12 (by decide)
    exact h12.trans (runN_2_steps s10 hs10h (by simp [hs10pc]) hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 939 := by have : s12 = step (step s10) := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step (step s10) := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by have : s12 = step (step s10) := hrun12; rw [this, hs12eq]; exact hs11Z
  have hs12T : s12.mem.get 18 = s.mem.get 14 - s.mem.get 26 := by
    have : s12 = step (step s10) := hrun12; rw [this, hs12eq]; exact hs11T
  have hW12 : s12.mem.get 14 = s.mem.get 14 := by
    have : s12 = step (step s10) := hrun12; rw [this, hs12eq]; exact hW11
  have hpres12 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha0
    have : s12 = step (step s10) := hrun12
    rw [this, hs12eq]; exact hpres11 a ha27 ha18 ha0
  have g12 : ∀ k : Nat, 939 ≤ k → k < 951 →
      s12.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres12 (UInt16.ofNat k) n27 n18 n0).trans (hcode k (by omega) (by omega))
  have hmP := pad_mov_T_PAD (s := s12) hs12pc hs12h hs12Z g12
  have hrun16 : runN s 16 = runN s12 4 := runN_add_eq s 12 4 16 (by decide)
  let s16 := runN s 16
  have hs16pc : s16.pc = 951 := by have : s16 = runN s12 4 := hrun16; rw [this]; exact hmP.1
  have hs16h : s16.halted = false := by have : s16 = runN s12 4 := hrun16; rw [this]; exact hmP.2.1
  have hs16Z : s16.mem.get 0 = 0 := by have : s16 = runN s12 4 := hrun16; rw [this]; exact hmP.2.2.2.1
  have hs16P : s16.mem.get 27 = s.mem.get 14 - s.mem.get 26 := by
    have : s16 = runN s12 4 := hrun16
    rw [this]; exact hmP.2.2.1.trans hs12T
  have hW16 : s16.mem.get 14 = s.mem.get 14 := by
    have : s16 = runN s12 4 := hrun16
    rw [this]; exact (hmP.2.2.2.2.2 14 (by decide) (by decide)).trans hW12
  have hpres16 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha0
    have : s16 = runN s12 4 := hrun16
    rw [this]; exact (hmP.2.2.2.2.2 a ha27 ha0).trans (hpres12 a ha27 ha18 ha0)
  have g16 : ∀ k : Nat, 951 ≤ k → k < 963 →
      s16.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n16 : UInt16.ofNat k ≠ (16 : Word) := by
      have : (16 : Word) = UInt16.ofNat 16 := rfl
      rw [this]; exact ofNat_ne k 16 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres16 (UInt16.ofNat k) n27 n18 n0).trans (hcode k (by omega) (by omega))
  have hmL := pad_mov_WIDTH_LEN (s := s16) hs16pc hs16h hs16Z g16
  have hrun20 : runN s 20 = runN s16 4 := runN_add_eq s 16 4 20 (by decide)
  let s20 := runN s 20
  have hs20pc : s20.pc = 963 := by have : s20 = runN s16 4 := hrun20; rw [this]; exact hmL.1
  have hs20h : s20.halted = false := by have : s20 = runN s16 4 := hrun20; rw [this]; exact hmL.2.1
  have hs20Z : s20.mem.get 0 = 0 := by have : s20 = runN s16 4 := hrun20; rw [this]; exact hmL.2.2.2.1
  have hs20L : s20.mem.get 16 = s.mem.get 14 := by
    have : s20 = runN s16 4 := hrun20; rw [this]; exact hmL.2.2.1.trans hW16
  have hs20P : s20.mem.get 27 = s.mem.get 14 - s.mem.get 26 := by
    have : s20 = runN s16 4 := hrun20
    rw [this]; exact (hmL.2.2.2.2.2 27 (by decide) (by decide)).trans hs16P
  have hpres20 : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 16 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha16 ha0
    have : s20 = runN s16 4 := hrun20
    rw [this]; exact (hmL.2.2.2.2.2 a ha16 ha0).trans (hpres16 a ha27 ha18 ha0)
  have g20 : ∀ k : Nat, 963 ≤ k → k < 966 →
      s20.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n16 : UInt16.ofNat k ≠ (16 : Word) := by
      have : (16 : Word) = UInt16.ofNat 16 := rfl
      rw [this]; exact ofNat_ne k 16 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres20 (UInt16.ofNat k) n27 n18 n16 n0).trans (hcode k (by omega) (by omega))
  have hencj := pad_enc_jmp_963 (s := s20) hs20pc g20
  have hpc20 : s20.pc.toNat < 32768 := by simp [hs20pc]
  have hjmp := step_JMP (s := s20) (dest := 978)
    hs20h hpc20 hs20Z hencj.1 hencj.2.1 hencj.2.2
  have hrun : s21 = step s20 := by
    have h21 : runN s 21 = runN s20 1 := runN_add_eq s 20 1 21 (by decide)
    exact h21.trans (runN_one s20 hs20h hpc20)
  have hs21pc : s21.pc = 978 := by rw [hrun, hjmp]
  have hs21h : s21.halted = false := by rw [hrun, hjmp]; exact hs20h
  have hs21Z : s21.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs20Z
  have hs21P : s21.mem.get 27 = s.mem.get 14 - s.mem.get 26 := by rw [hrun, hjmp]; exact hs20P
  have hs21L : s21.mem.get 16 = s.mem.get 14 := by rw [hrun, hjmp]; exact hs20L
  have hpres : ∀ a, a ≠ 27 → a ≠ 18 → a ≠ 16 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha27 ha18 ha16 ha0
    rw [hrun, hjmp]; exact hpres20 a ha27 ha18 ha16 ha0
  exact ⟨hs21pc, hs21h, hs21Z, hs21P, hs21L, hpres⟩

/-! ### LEN_OK: CAP==0 halt, or ROOM = CAP-1 and enter SP_LOOP -/

/-- `CAP = 0`: 6 steps from `LEN_OK` through `DONE`/`HALT` to `pc = 32768`. -/
theorem cap0_halt {s : Machine}
    (hpc : s.pc = 978)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hC : s.mem.get 13 = 0)
    (hcode : ∀ k : Nat, 978 ≤ k → k < 993 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hhalt : ∀ k : Nat, 2316 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s6 := runN s 6
    s6.pc = 32768 ∧
    s6.halted = false ∧
    s6.mem.get 0 = 0 ∧
    s6.mem.get 18 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a) := by
  intro s6
  have hm := pad_mov_CAP_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 990 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 0 := hm.2.2.1.trans hC
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 990 ≤ k → k < 993 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_jlez_990 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez :=
    step_JLEZ (s := s4) (x := 18) (dest := 2316)
      hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = true := by
    have : le0 (s4.mem.get 18) = true := by
      rw [hs4T]; exact le0_zero
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 2316 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (2316 : Word) else s4.pc + 3) = (2316 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 2316 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 : ∀ k : Nat, 2316 ≤ k → k < 2319 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hhalt k h1 h2)
  have hencH := pad_enc_halt_2316 (s := s5) hs5pc g5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hH := step_HALT (s := s5) hs5h hpc5 hs5Z hencH.1 hencH.2.1 hencH.2.2
  have hrun : s6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  have hs6pc : s6.pc = 32768 := by rw [hrun, hH]
  have hs6h : s6.halted = false := by rw [hrun, hH]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by rw [hrun, hH]; exact hs5Z
  have hs6T : s6.mem.get 18 = 0 := by rw [hrun, hH]; exact hs5T
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hH]; exact hpres5 a ha18 ha0
  exact ⟨hs6pc, hs6h, hs6Z, hs6T, hpres⟩

/-- `0 < CAP < 32768`: 11 steps from `LEN_OK` to `SP_LOOP`,
`ROOM = CAP - 1`, `IDX = 0`. -/
theorem cap_nz_to_sploop {s : Machine}
    (hpc : s.pc = 978)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 978 ≤ k → k < 1011 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s11 := runN s 11
    s11.pc = 1011 ∧
    s11.halted = false ∧
    s11.mem.get 0 = 0 ∧
    s11.mem.get 28 = s.mem.get 13 - 1 ∧
    s11.mem.get 29 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 28 → a ≠ 29 → a ≠ 0 → s11.mem.get a = s.mem.get a) := by
  intro s11
  have hm := pad_mov_CAP_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 990 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 13 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hC4 : s4.mem.get 13 = s.mem.get 13 := hpres4 13 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 : ∀ k : Nat, 990 ≤ k → k < 993 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_jlez_990 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez :=
    step_JLEZ (s := s4) (x := 18) (dest := 2316)
      hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos hClo hChi
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 993 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (2316 : Word) else s4.pc + 3) = (993 : Word) := by
      have hfall : s4.pc + 3 = (993 : Word) := by simp [hs4pc]
      simp [hle, hfall]
    rw [hjlez, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 993 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hC5 : s5.mem.get 13 = s.mem.get 13 := by
    have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hC4
  have hONE5 : s5.mem.get 3 = 1 := by
    have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 : ∀ k : Nat, 993 ≤ k → k < 1005 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hmR := pad_mov_CAP_ROOM (s := s5) hs5pc hs5h hs5Z g5
  have hrun9 : runN s 9 = runN s5 4 := runN_add_eq s 5 4 9 (by decide)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1005 := by have : s9 = runN s5 4 := hrun9; rw [this]; exact hmR.1
  have hs9h : s9.halted = false := by have : s9 = runN s5 4 := hrun9; rw [this]; exact hmR.2.1
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = runN s5 4 := hrun9; rw [this]; exact hmR.2.2.2.1
  have hs9R : s9.mem.get 28 = s.mem.get 13 := by
    have : s9 = runN s5 4 := hrun9; rw [this]; exact hmR.2.2.1.trans hC5
  have hONE9 : s9.mem.get 3 = 1 := by
    have : s9 = runN s5 4 := hrun9
    rw [this]; exact (hmR.2.2.2.2.2 3 (by decide) (by decide)).trans hONE5
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 28 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha28 ha0
    have : s9 = runN s5 4 := hrun9
    rw [this]; exact (hmR.2.2.2.2.2 a ha28 ha0).trans (hpres5 a ha18 ha0)
  have g9 : ∀ k : Nat, 1005 ≤ k → k < 1008 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n28 : UInt16.ofNat k ≠ (28 : Word) := by
      have : (28 : Word) = UInt16.ofNat 28 := rfl
      rw [this]; exact ofNat_ne k 28 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n18 n28 n0).trans (hcode k (by omega) (by omega))
  have hd := pad_dec_ROOM (s := s9) hs9pc hs9h hONE9 g9
  have hs10eq : step s9 = { s9 with mem := s9.mem.set 28 (s9.mem.get 28 - 1), pc := 1008 } := hd
  have hrun10 : runN s 10 = step s9 := by
    have h10 : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
    exact h10.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hs10pc : s10.pc = 1008 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 28 0 (s9.mem.get 28 - 1) (by decide)).trans hs9Z
  have hs10R : s10.mem.get 28 = s.mem.get 13 - 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq, hs9R]
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 28 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha28 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 28 a (s9.mem.get 28 - 1) ha28).trans (hpres9 a ha18 ha28 ha0)
  have g10 : ∀ k : Nat, 1008 ≤ k → k < 1011 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n28 : UInt16.ofNat k ≠ (28 : Word) := by
      have : (28 : Word) = UInt16.ofNat 28 := rfl
      rw [this]; exact ofNat_ne k 28 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n28 n0).trans (hcode k (by omega) (by omega))
  have hz := pad_zero_IDX (s := s10) hs10pc hs10h g10
  have hs11eq : step s10 = { s10 with mem := s10.mem.set 29 0, pc := 1011 } := hz
  have hrun : s11 = step s10 := by
    have h11 : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
    exact h11.trans (runN_one s10 hs10h hpc10)
  have hs11pc : s11.pc = 1011 := by rw [hrun, hs11eq]
  have hs11h : s11.halted = false := by rw [hrun, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by
    rw [hrun, hs11eq]
    exact (Mem.get_set_ne s10.mem 29 0 0 (by decide)).trans hs10Z
  have hs11R : s11.mem.get 28 = s.mem.get 13 - 1 := by
    rw [hrun, hs11eq]
    exact (Mem.get_set_ne s10.mem 29 28 0 (by decide)).trans hs10R
  have hs11I : s11.mem.get 29 = 0 := by rw [hrun, hs11eq, Mem.get_set_eq]
  have hpres : ∀ a, a ≠ 18 → a ≠ 28 → a ≠ 29 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha28 ha29 ha0
    rw [hrun, hs11eq]
    exact (Mem.get_set_ne s10.mem 29 a 0 ha29).trans (hpres10 a ha18 ha28 ha0)
  exact ⟨hs11pc, hs11h, hs11Z, hs11R, hs11I, hpres⟩

/-- `PAD = 0`: 5 steps from `SP_LOOP` to `AFTER_PAD`. -/
theorem sp_loop_pad0 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hP : s.mem.get 27 = 0)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1026 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1077 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 18 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := pad_mov_PAD_T_1011 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1023 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 0 := hm.2.2.1.trans hP
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1023 ≤ k → k < 1026 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := pad_enc_jlez_1023 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez :=
    step_JLEZ (s := s4) (x := 18) (dest := 1077)
      hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = true := by
    have : le0 (s4.mem.get 18) = true := by
      rw [hs4T]; exact le0_zero
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1077 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1077 : Word) else s4.pc + 3) = (1077 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1077 := by rw [hrun, hs5eq]
  have hs5h : s5.halted = false := by rw [hrun, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 0 := by rw [hrun, hs5eq]; exact hs4T
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hs5eq]; exact hpres4 a ha18 ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5T, hpres⟩

/-! ### Default-path compositions (WIDTH = 0, CAP ≠ 0) from HAVE_DIG to AFTER_PAD -/

/-- `SIGN = 0`, `WIDTH = 0`, `0 < CAP < 32768`: 35 steps, 867 → 1077,
`LEN = NDIG`, `PAD = 0`, `ROOM = CAP - 1`, `IDX = 0`. -/
theorem have_dig_to_after_pad_unsigned {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hS : s.mem.get 19 = 0)
    (hW : s.mem.get 14 = 0)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 1026 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s35 := runN s 35
    s35.pc = 1077 ∧
    s35.halted = false ∧
    s35.mem.get 0 = 0 ∧
    s35.mem.get 26 = s.mem.get 25 ∧
    s35.mem.get 16 = s.mem.get 25 ∧
    s35.mem.get 27 = 0 ∧
    s35.mem.get 28 = s.mem.get 13 - 1 ∧
    s35.mem.get 29 = 0 ∧
    (∀ a, a ≠ 26 → a ≠ 18 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 0 →
      s35.mem.get a = s.mem.get a) := by
  intro s35
  have hd := have_dig_sign0 (s := s) hpc hh hZ hS
    (fun k h1 h2 => hcode k h1 (by omega))
  let s9 := runN s 9
  have hs9pc : s9.pc = 903 := hd.1
  have hs9h : s9.halted = false := hd.2.1
  have hs9Z : s9.mem.get 0 = 0 := hd.2.2.1
  have hs9R : s9.mem.get 26 = s.mem.get 25 := hd.2.2.2.1
  have hpres9 := hd.2.2.2.2
  have hW9 : s9.mem.get 14 = 0 := (hpres9 14 (by decide) (by decide) (by decide)).trans hW
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide) (by decide)).trans hONE
  have hC9 : s9.mem.get 13 = s.mem.get 13 := hpres9 13 (by decide) (by decide) (by decide)
  have g9 : ∀ k : Nat, 903 ≤ k → k < 978 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n26 n18 n0).trans (hcode k (by omega) (by omega))
  have hp := pad_len_width0 (s := s9) hs9pc hs9h hs9Z hW9 g9
  have hrun19 : runN s 19 = runN s9 10 := runN_add_eq s 9 10 19 (by decide)
  let s19 := runN s 19
  have hs19pc : s19.pc = 978 := by have : s19 = runN s9 10 := hrun19; rw [this]; exact hp.1
  have hs19h : s19.halted = false := by have : s19 = runN s9 10 := hrun19; rw [this]; exact hp.2.1
  have hs19Z : s19.mem.get 0 = 0 := by have : s19 = runN s9 10 := hrun19; rw [this]; exact hp.2.2.1
  have hs19P : s19.mem.get 27 = 0 := by have : s19 = runN s9 10 := hrun19; rw [this]; exact hp.2.2.2.1
  have hs19L : s19.mem.get 16 = s.mem.get 25 := by
    have : s19 = runN s9 10 := hrun19
    rw [this]; exact hp.2.2.2.2.1.trans hs9R
  have hs19R : s19.mem.get 26 = s.mem.get 25 := by
    have : s19 = runN s9 10 := hrun19
    rw [this]; exact (hp.2.2.2.2.2 26 (by decide) (by decide) (by decide) (by decide)).trans hs9R
  have hONE19 : s19.mem.get 3 = 1 := by
    have : s19 = runN s9 10 := hrun19
    rw [this]
    exact (hp.2.2.2.2.2 3 (by decide) (by decide) (by decide) (by decide)).trans hONE9
  have hC19 : s19.mem.get 13 = s.mem.get 13 := by
    have : s19 = runN s9 10 := hrun19
    rw [this]
    exact (hp.2.2.2.2.2 13 (by decide) (by decide) (by decide) (by decide)).trans hC9
  have hClo19 : 0 < (s19.mem.get 13).toNat := by rw [hC19]; exact hClo
  have hChi19 : (s19.mem.get 13).toNat < 32768 := by rw [hC19]; exact hChi
  have hpres19 : ∀ a, a ≠ 26 → a ≠ 18 → a ≠ 16 → a ≠ 27 → a ≠ 0 →
      s19.mem.get a = s.mem.get a := by
    intro a ha26 ha18 ha16 ha27 ha0
    have : s19 = runN s9 10 := hrun19
    rw [this]
    exact (hp.2.2.2.2.2 a ha27 ha18 ha16 ha0).trans (hpres9 a ha26 ha18 ha0)
  have g19 : ∀ k : Nat, 978 ≤ k → k < 1011 →
      s19.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n16 : UInt16.ofNat k ≠ (16 : Word) := by
      have : (16 : Word) = UInt16.ofNat 16 := rfl
      rw [this]; exact ofNat_ne k 16 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres19 (UInt16.ofNat k) n26 n18 n16 n27 n0).trans (hcode k (by omega) (by omega))
  have hc := cap_nz_to_sploop (s := s19) hs19pc hs19h hs19Z hONE19 hClo19 hChi19 g19
  have hrun30 : runN s 30 = runN s19 11 := runN_add_eq s 19 11 30 (by decide)
  let s30 := runN s 30
  have hs30pc : s30.pc = 1011 := by have : s30 = runN s19 11 := hrun30; rw [this]; exact hc.1
  have hs30h : s30.halted = false := by have : s30 = runN s19 11 := hrun30; rw [this]; exact hc.2.1
  have hs30Z : s30.mem.get 0 = 0 := by have : s30 = runN s19 11 := hrun30; rw [this]; exact hc.2.2.1
  have hs30Room : s30.mem.get 28 = s.mem.get 13 - 1 := by
    have : s30 = runN s19 11 := hrun30
    rw [this]; exact hc.2.2.2.1.trans (by rw [hC19])
  have hs30I : s30.mem.get 29 = 0 := by have : s30 = runN s19 11 := hrun30; rw [this]; exact hc.2.2.2.2.1
  have hs30P : s30.mem.get 27 = 0 := by
    have : s30 = runN s19 11 := hrun30
    rw [this]; exact (hc.2.2.2.2.2 27 (by decide) (by decide) (by decide) (by decide)).trans hs19P
  have hs30L : s30.mem.get 16 = s.mem.get 25 := by
    have : s30 = runN s19 11 := hrun30
    rw [this]; exact (hc.2.2.2.2.2 16 (by decide) (by decide) (by decide) (by decide)).trans hs19L
  have hs30Raw : s30.mem.get 26 = s.mem.get 25 := by
    have : s30 = runN s19 11 := hrun30
    rw [this]; exact (hc.2.2.2.2.2 26 (by decide) (by decide) (by decide) (by decide)).trans hs19R
  have hpres30 : ∀ a, a ≠ 26 → a ≠ 18 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 0 →
      s30.mem.get a = s.mem.get a := by
    intro a ha26 ha18 ha16 ha27 ha28 ha29 ha0
    have : s30 = runN s19 11 := hrun30
    rw [this]
    exact (hc.2.2.2.2.2 a ha18 ha28 ha29 ha0).trans (hpres19 a ha26 ha18 ha16 ha27 ha0)
  have g30 : ∀ k : Nat, 1011 ≤ k → k < 1026 →
      s30.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n16 : UInt16.ofNat k ≠ (16 : Word) := by
      have : (16 : Word) = UInt16.ofNat 16 := rfl
      rw [this]; exact ofNat_ne k 16 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n28 : UInt16.ofNat k ≠ (28 : Word) := by
      have : (28 : Word) = UInt16.ofNat 28 := rfl
      rw [this]; exact ofNat_ne k 28 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres30 (UInt16.ofNat k) n26 n18 n16 n27 n28 n29 n0).trans
      (hcode k (by omega) (by omega))
  have hs := sp_loop_pad0 (s := s30) hs30pc hs30h hs30Z hs30P g30
  have hrun : s35 = runN s30 5 := runN_add_eq s 30 5 35 (by decide)
  have hs35pc : s35.pc = 1077 := by rw [hrun]; exact hs.1
  have hs35h : s35.halted = false := by rw [hrun]; exact hs.2.1
  have hs35Z : s35.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hs35Raw : s35.mem.get 26 = s.mem.get 25 := by
    rw [hrun]; exact (hs.2.2.2.2 26 (by decide) (by decide)).trans hs30Raw
  have hs35L : s35.mem.get 16 = s.mem.get 25 := by
    rw [hrun]; exact (hs.2.2.2.2 16 (by decide) (by decide)).trans hs30L
  have hs35P : s35.mem.get 27 = 0 := by
    rw [hrun]; exact (hs.2.2.2.2 27 (by decide) (by decide)).trans hs30P
  have hs35Room : s35.mem.get 28 = s.mem.get 13 - 1 := by
    rw [hrun]; exact (hs.2.2.2.2 28 (by decide) (by decide)).trans hs30Room
  have hs35I : s35.mem.get 29 = 0 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hs30I
  have hpres : ∀ a, a ≠ 26 → a ≠ 18 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 0 →
      s35.mem.get a = s.mem.get a := by
    intro a ha26 ha18 ha16 ha27 ha28 ha29 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a ha18 ha0).trans
      (hpres30 a ha26 ha18 ha16 ha27 ha28 ha29 ha0)
  exact ⟨hs35pc, hs35h, hs35Z, hs35Raw, hs35L, hs35P, hs35Room, hs35I, hpres⟩

end IntFmt
