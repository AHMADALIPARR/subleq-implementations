/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

`SP_LOOP` padding (`PAD > 0`, `WRITE_SPACE`) and the `AFTER_PAD`
sign-write path (`SIGN ≠ 0`, `WRITE_MINUS`). Block lemmas, not
end-to-end correctness.
-/

import IntFmt.StoreCh

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000


private theorem cell1024 (off : Nat) (h : off < 16) :
    intfmtImage[1024 + off]! = decChunk064[off]! :=
  extract_chunk 1024 decChunk064 image_chunk064 off h (by decide)


private theorem cell1040 (off : Nat) (h : off < 16) :
    intfmtImage[1040 + off]! = decChunk065[off]! :=
  extract_chunk 1040 decChunk065 image_chunk065 off h (by decide)


private theorem cell1056 (off : Nat) (h : off < 16) :
    intfmtImage[1056 + off]! = decChunk066[off]! :=
  extract_chunk 1056 decChunk066 image_chunk066 off h (by decide)


private theorem cell1072 (off : Nat) (h : off < 16) :
    intfmtImage[1072 + off]! = decChunk067[off]! :=
  extract_chunk 1072 decChunk067 image_chunk067 off h (by decide)


private theorem cell1088 (off : Nat) (h : off < 16) :
    intfmtImage[1088 + off]! = decChunk068[off]! :=
  extract_chunk 1088 decChunk068 image_chunk068 off h (by decide)


private theorem cell1104 (off : Nat) (h : off < 16) :
    intfmtImage[1104 + off]! = decChunk069[off]! :=
  extract_chunk 1104 decChunk069 image_chunk069 off h (by decide)


private theorem cell1120 (off : Nat) (h : off < 16) :
    intfmtImage[1120 + off]! = decChunk070[off]! :=
  extract_chunk 1120 decChunk070 image_chunk070 off h (by decide)


private theorem cell1136 (off : Nat) (h : off < 16) :
    intfmtImage[1136 + off]! = decChunk071[off]! :=
  extract_chunk 1136 decChunk071 image_chunk071 off h (by decide)


private theorem cell1152 (off : Nat) (h : off < 16) :
    intfmtImage[1152 + off]! = decChunk072[off]! :=
  extract_chunk 1152 decChunk072 image_chunk072 off h (by decide)


private theorem cell1168 (off : Nat) (h : off < 16) :
    intfmtImage[1168 + off]! = decChunk073[off]! :=
  extract_chunk 1168 decChunk073 image_chunk073 off h (by decide)

/-- MOV IDX T at pc 1026 (SP_LOOP, PAD nonzero). -/
theorem pl_mov_IDX_T_1026 {s : Machine}
    (hpc : s.pc = 1026)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1026 ≤ k → k < 1038 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1038 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 29 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 29 = s.mem.get 29 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1026 :=
    hpc.trans (rfl : (1026 : Word) = UInt16.ofNat 1026)
  have g (k : Nat) (h1 : 1026 ≤ k) (h2 : k < 1038) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1026 + off) :=
    word_pc_off 1026 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk064[2]! = 18 := rfl
    exact (g 1026 (by decide) (by decide)).trans ((cell1024 2 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk064[3]! = 18 := rfl
    exact (g 1027 (by decide) (by decide)).trans ((cell1024 3 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk064[4]! = 1029 := rfl
    have hv : (1029 : Word) = UInt16.ofNat 1029 := rfl
    exact (g 1028 (by decide) (by decide)).trans ((cell1024 4 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 29 := by
    rw [poff 3 (by decide)]
    have hval : decChunk064[5]! = 29 := rfl
    exact (g 1029 (by decide) (by decide)).trans ((cell1024 5 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk064[6]! = 0 := rfl
    exact (g 1030 (by decide) (by decide)).trans ((cell1024 6 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk064[7]! = 1032 := rfl
    have hv : (1032 : Word) = UInt16.ofNat 1032 := rfl
    exact (g 1031 (by decide) (by decide)).trans ((cell1024 7 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk064[8]! = 0 := rfl
    exact (g 1032 (by decide) (by decide)).trans ((cell1024 8 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk064[9]! = 18 := rfl
    exact (g 1033 (by decide) (by decide)).trans ((cell1024 9 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk064[10]! = 1035 := rfl
    have hv : (1035 : Word) = UInt16.ofNat 1035 := rfl
    exact (g 1034 (by decide) (by decide)).trans ((cell1024 10 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk064[11]! = 0 := rfl
    exact (g 1035 (by decide) (by decide)).trans ((cell1024 11 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk064[12]! = 0 := rfl
    exact (g 1036 (by decide) (by decide)).trans ((cell1024 12 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk064[13]! = 1038 := rfl
    have hv : (1038 : Word) = UInt16.ofNat 1038 := rfl
    exact (g 1037 (by decide) (by decide)).trans ((cell1024 13 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1026 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1026 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 29) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1038 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1038 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1038 = (1038 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- SUB ROOM T at pc 1038 (T = IDX - ROOM). -/
theorem pl_sub_ROOM_T_1038 {s : Machine}
    (hpc : s.pc = 1038)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1038 ≤ k → k < 1041 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 28)
        pc := 1041 } := by
  have hp : s.pc = UInt16.ofNat 1038 :=
    hpc.trans (rfl : (1038 : Word) = UInt16.ofNat 1038)
  have g (k : Nat) (h1 : 1038 ≤ k) (h2 : k < 1041) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 28 := by
    rw [hp]
    have hval : decChunk064[14]! = 28 := rfl
    exact (g 1038 (by decide) (by decide)).trans ((cell1024 14 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1039 : Word) := by simp [hpc]
    rw [this, (rfl : (1039 : Word) = UInt16.ofNat 1039)]
    have hval : decChunk064[15]! = 18 := rfl
    exact (g 1039 (by decide) (by decide)).trans ((cell1024 15 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1040 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1041 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1040 : Word) = UInt16.ofNat 1040)]
    have hval : decChunk065[0]! = 1041 := rfl
    have hv : (1041 : Word) = UInt16.ofNat 1041 := rfl
    exact (g 1040 (by decide) (by decide)).trans ((cell1040 0 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 28) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1041 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T SP_EQCHK at pc 1041. -/
theorem pl_enc_jlez_1041 {s : Machine}
    (hpc : s.pc = 1041)
    (hcode : ∀ k : Nat, 1041 ≤ k → k < 1041+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1047 := by
  have hp : s.pc = UInt16.ofNat 1041 :=
    hpc.trans (rfl : (1041 : Word) = UInt16.ofNat 1041)
  have g (k : Nat) (h1 : 1041 ≤ k) (h2 : k < 1041+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk065[1]! = 0 := rfl
    exact (g 1041 (by decide) (by decide)).trans ((cell1040 1 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1042 : Word) := by simp [hpc]
    rw [this, (rfl : (1042 : Word) = UInt16.ofNat 1042)]
    have hval : decChunk065[2]! = 18 := rfl
    exact (g 1042 (by decide) (by decide)).trans ((cell1040 2 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1047 := by
    have : s.pc + 2 = (1043 : Word) := by simp [hpc]
    rw [this, (rfl : (1043 : Word) = UInt16.ofNat 1043)]
    have hval : decChunk065[3]! = 1047 := rfl
    exact (g 1043 (by decide) (by decide)).trans ((cell1040 3 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP AFTER_PAD at pc 1044 (IDX > ROOM). -/
theorem pl_enc_jmp_1044 {s : Machine}
    (hpc : s.pc = 1044)
    (hcode : ∀ k : Nat, 1044 ≤ k → k < 1044+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1077 := by
  have hp : s.pc = UInt16.ofNat 1044 :=
    hpc.trans (rfl : (1044 : Word) = UInt16.ofNat 1044)
  have g (k : Nat) (h1 : 1044 ≤ k) (h2 : k < 1044+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk065[4]! = 0 := rfl
    exact (g 1044 (by decide) (by decide)).trans ((cell1040 4 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1045 : Word) := by simp [hpc]
    rw [this, (rfl : (1045 : Word) = UInt16.ofNat 1045)]
    have hval : decChunk065[5]! = 0 := rfl
    exact (g 1045 (by decide) (by decide)).trans ((cell1040 5 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1077 := by
    have : s.pc + 2 = (1046 : Word) := by simp [hpc]
    rw [this, (rfl : (1046 : Word) = UInt16.ofNat 1046)]
    have hval : decChunk065[6]! = 1077 := rfl
    exact (g 1046 (by decide) (by decide)).trans ((cell1040 6 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- INC T at SP_EQCHK (pc 1047). -/
theorem pl_inc_T_1047 {s : Machine}
    (hpc : s.pc = 1047)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1047 ≤ k → k < 1056 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1056 ∧
    s3.halted = false ∧
    s3.mem.get 18 = s.mem.get 18 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1047 :=
    hpc.trans (rfl : (1047 : Word) = UInt16.ofNat 1047)
  have g (k : Nat) (h1 : 1047 ≤ k) (h2 : k < 1056) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1047 + off) :=
    word_pc_off 1047 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk065[7]! = 3 := rfl
    exact (g 1047 (by decide) (by decide)).trans ((cell1040 7 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk065[8]! = 0 := rfl
    exact (g 1048 (by decide) (by decide)).trans ((cell1040 8 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk065[9]! = 1050 := rfl
    have hv : (1050 : Word) = UInt16.ofNat 1050 := rfl
    exact (g 1049 (by decide) (by decide)).trans ((cell1040 9 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk065[10]! = 0 := rfl
    exact (g 1050 (by decide) (by decide)).trans ((cell1040 10 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 18 := by
    rw [poff 4 (by decide)]
    have hval : decChunk065[11]! = 18 := rfl
    exact (g 1051 (by decide) (by decide)).trans ((cell1040 11 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk065[12]! = 1053 := rfl
    have hv : (1053 : Word) = UInt16.ofNat 1053 := rfl
    exact (g 1052 (by decide) (by decide)).trans ((cell1040 12 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk065[13]! = 0 := rfl
    exact (g 1053 (by decide) (by decide)).trans ((cell1040 13 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk065[14]! = 0 := rfl
    exact (g 1054 (by decide) (by decide)).trans ((cell1040 14 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk065[15]! = 1056 := rfl
    have hv : (1056 : Word) = UInt16.ofNat 1056 := rfl
    exact (g 1055 (by decide) (by decide)).trans ((cell1040 15 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1047 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1047 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1056 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1056 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1056 = (1056 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 18 = s.mem.get 18 + 1 := by
    have : s.mem.get 18 + s.mem.get 3 = s.mem.get 18 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- JLEZ T SP_WRITE at pc 1056. -/
theorem pl_enc_jlez_1056 {s : Machine}
    (hpc : s.pc = 1056)
    (hcode : ∀ k : Nat, 1056 ≤ k → k < 1056+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1062 := by
  have hp : s.pc = UInt16.ofNat 1056 :=
    hpc.trans (rfl : (1056 : Word) = UInt16.ofNat 1056)
  have g (k : Nat) (h1 : 1056 ≤ k) (h2 : k < 1056+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk066[0]! = 0 := rfl
    exact (g 1056 (by decide) (by decide)).trans ((cell1056 0 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1057 : Word) := by simp [hpc]
    rw [this, (rfl : (1057 : Word) = UInt16.ofNat 1057)]
    have hval : decChunk066[1]! = 18 := rfl
    exact (g 1057 (by decide) (by decide)).trans ((cell1056 1 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1062 := by
    have : s.pc + 2 = (1058 : Word) := by simp [hpc]
    rw [this, (rfl : (1058 : Word) = UInt16.ofNat 1058)]
    have hval : decChunk066[2]! = 1062 := rfl
    exact (g 1058 (by decide) (by decide)).trans ((cell1056 2 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP AFTER_PAD at pc 1059 (IDX = ROOM). -/
theorem pl_enc_jmp_1059 {s : Machine}
    (hpc : s.pc = 1059)
    (hcode : ∀ k : Nat, 1059 ≤ k → k < 1059+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1077 := by
  have hp : s.pc = UInt16.ofNat 1059 :=
    hpc.trans (rfl : (1059 : Word) = UInt16.ofNat 1059)
  have g (k : Nat) (h1 : 1059 ≤ k) (h2 : k < 1059+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk066[3]! = 0 := rfl
    exact (g 1059 (by decide) (by decide)).trans ((cell1056 3 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1060 : Word) := by simp [hpc]
    rw [this, (rfl : (1060 : Word) = UInt16.ofNat 1060)]
    have hval : decChunk066[4]! = 0 := rfl
    exact (g 1060 (by decide) (by decide)).trans ((cell1056 4 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1077 := by
    have : s.pc + 2 = (1061 : Word) := by simp [hpc]
    rw [this, (rfl : (1061 : Word) = UInt16.ofNat 1061)]
    have hval : decChunk066[5]! = 1077 := rfl
    exact (g 1061 (by decide) (by decide)).trans ((cell1056 5 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV ONE RETID at SP_WRITE (pc 1062). -/
theorem pl_mov_ONE_RETID_1062 {s : Machine}
    (hpc : s.pc = 1062)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1062 ≤ k → k < 1074 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1074 ∧
    s4.halted = false ∧
    s4.mem.get 2319 = s.mem.get 3 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 3 = s.mem.get 3 ∧
    (∀ a, a ≠ 2319 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1062 :=
    hpc.trans (rfl : (1062 : Word) = UInt16.ofNat 1062)
  have g (k : Nat) (h1 : 1062 ≤ k) (h2 : k < 1074) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1062 + off) :=
    word_pc_off 1062 off hp (by omega)
  have m0 : s.mem.get s.pc = 2319 := by
    rw [hp]
    have hval : decChunk066[6]! = 2319 := rfl
    exact (g 1062 (by decide) (by decide)).trans ((cell1056 6 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 2319 := by
    rw [poff 1 (by decide)]
    have hval : decChunk066[7]! = 2319 := rfl
    exact (g 1063 (by decide) (by decide)).trans ((cell1056 7 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk066[8]! = 1065 := rfl
    have hv : (1065 : Word) = UInt16.ofNat 1065 := rfl
    exact (g 1064 (by decide) (by decide)).trans ((cell1056 8 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 3 := by
    rw [poff 3 (by decide)]
    have hval : decChunk066[9]! = 3 := rfl
    exact (g 1065 (by decide) (by decide)).trans ((cell1056 9 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk066[10]! = 0 := rfl
    exact (g 1066 (by decide) (by decide)).trans ((cell1056 10 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk066[11]! = 1068 := rfl
    have hv : (1068 : Word) = UInt16.ofNat 1068 := rfl
    exact (g 1067 (by decide) (by decide)).trans ((cell1056 11 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk066[12]! = 0 := rfl
    exact (g 1068 (by decide) (by decide)).trans ((cell1056 12 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 2319 := by
    rw [poff 7 (by decide)]
    have hval : decChunk066[13]! = 2319 := rfl
    exact (g 1069 (by decide) (by decide)).trans ((cell1056 13 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk066[14]! = 1071 := rfl
    have hv : (1071 : Word) = UInt16.ofNat 1071 := rfl
    exact (g 1070 (by decide) (by decide)).trans ((cell1056 14 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk066[15]! = 0 := rfl
    exact (g 1071 (by decide) (by decide)).trans ((cell1056 15 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk067[0]! = 0 := rfl
    exact (g 1072 (by decide) (by decide)).trans ((cell1072 0 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk067[1]! = 1074 := rfl
    have hv : (1074 : Word) = UInt16.ofNat 1074 := rfl
    exact (g 1073 (by decide) (by decide)).trans ((cell1072 1 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (2319 : Word) := by
    intro i hi
    have : (2319 : Word) = UInt16.ofNat 2319 := rfl
    rw [this]
    exact pc_off_ne 1062 i 2319 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1062 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 3) (dst := 2319)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1074 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1074 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1074 = (1074 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP WRITE_SPACE at pc 1074. -/
theorem pl_enc_jmp_1074 {s : Machine}
    (hpc : s.pc = 1074)
    (hcode : ∀ k : Nat, 1074 ≤ k → k < 1074+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1155 := by
  have hp : s.pc = UInt16.ofNat 1074 :=
    hpc.trans (rfl : (1074 : Word) = UInt16.ofNat 1074)
  have g (k : Nat) (h1 : 1074 ≤ k) (h2 : k < 1074+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk067[2]! = 0 := rfl
    exact (g 1074 (by decide) (by decide)).trans ((cell1072 2 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1075 : Word) := by simp [hpc]
    rw [this, (rfl : (1075 : Word) = UInt16.ofNat 1075)]
    have hval : decChunk067[3]! = 0 := rfl
    exact (g 1075 (by decide) (by decide)).trans ((cell1072 3 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1155 := by
    have : s.pc + 2 = (1076 : Word) := by simp [hpc]
    rw [this, (rfl : (1076 : Word) = UInt16.ofNat 1076)]
    have hval : decChunk067[4]! = 1155 := rfl
    exact (g 1076 (by decide) (by decide)).trans ((cell1072 4 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV IDX T at pc 1092 (AFTER_PAD, SIGN nonzero). -/
theorem pl_mov_IDX_T_1092 {s : Machine}
    (hpc : s.pc = 1092)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1092 ≤ k → k < 1104 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1104 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 29 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 29 = s.mem.get 29 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1092 :=
    hpc.trans (rfl : (1092 : Word) = UInt16.ofNat 1092)
  have g (k : Nat) (h1 : 1092 ≤ k) (h2 : k < 1104) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1092 + off) :=
    word_pc_off 1092 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk068[4]! = 18 := rfl
    exact (g 1092 (by decide) (by decide)).trans ((cell1088 4 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk068[5]! = 18 := rfl
    exact (g 1093 (by decide) (by decide)).trans ((cell1088 5 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk068[6]! = 1095 := rfl
    have hv : (1095 : Word) = UInt16.ofNat 1095 := rfl
    exact (g 1094 (by decide) (by decide)).trans ((cell1088 6 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 29 := by
    rw [poff 3 (by decide)]
    have hval : decChunk068[7]! = 29 := rfl
    exact (g 1095 (by decide) (by decide)).trans ((cell1088 7 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk068[8]! = 0 := rfl
    exact (g 1096 (by decide) (by decide)).trans ((cell1088 8 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk068[9]! = 1098 := rfl
    have hv : (1098 : Word) = UInt16.ofNat 1098 := rfl
    exact (g 1097 (by decide) (by decide)).trans ((cell1088 9 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk068[10]! = 0 := rfl
    exact (g 1098 (by decide) (by decide)).trans ((cell1088 10 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk068[11]! = 18 := rfl
    exact (g 1099 (by decide) (by decide)).trans ((cell1088 11 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk068[12]! = 1101 := rfl
    have hv : (1101 : Word) = UInt16.ofNat 1101 := rfl
    exact (g 1100 (by decide) (by decide)).trans ((cell1088 12 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk068[13]! = 0 := rfl
    exact (g 1101 (by decide) (by decide)).trans ((cell1088 13 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk068[14]! = 0 := rfl
    exact (g 1102 (by decide) (by decide)).trans ((cell1088 14 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk068[15]! = 1104 := rfl
    have hv : (1104 : Word) = UInt16.ofNat 1104 := rfl
    exact (g 1103 (by decide) (by decide)).trans ((cell1088 15 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1092 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1092 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 29) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1104 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1104 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1104 = (1104 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- SUB ROOM T at pc 1104 (sign room check). -/
theorem pl_sub_ROOM_T_1104 {s : Machine}
    (hpc : s.pc = 1104)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1104 ≤ k → k < 1107 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 28)
        pc := 1107 } := by
  have hp : s.pc = UInt16.ofNat 1104 :=
    hpc.trans (rfl : (1104 : Word) = UInt16.ofNat 1104)
  have g (k : Nat) (h1 : 1104 ≤ k) (h2 : k < 1107) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 28 := by
    rw [hp]
    have hval : decChunk069[0]! = 28 := rfl
    exact (g 1104 (by decide) (by decide)).trans ((cell1104 0 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1105 : Word) := by simp [hpc]
    rw [this, (rfl : (1105 : Word) = UInt16.ofNat 1105)]
    have hval : decChunk069[1]! = 18 := rfl
    exact (g 1105 (by decide) (by decide)).trans ((cell1104 1 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1106 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1107 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1106 : Word) = UInt16.ofNat 1106)]
    have hval : decChunk069[2]! = 1107 := rfl
    have hv : (1107 : Word) = UInt16.ofNat 1107 := rfl
    exact (g 1106 (by decide) (by decide)).trans ((cell1104 2 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 28) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1107 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T SG_EQ at pc 1107. -/
theorem pl_enc_jlez_1107 {s : Machine}
    (hpc : s.pc = 1107)
    (hcode : ∀ k : Nat, 1107 ≤ k → k < 1107+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1113 := by
  have hp : s.pc = UInt16.ofNat 1107 :=
    hpc.trans (rfl : (1107 : Word) = UInt16.ofNat 1107)
  have g (k : Nat) (h1 : 1107 ≤ k) (h2 : k < 1107+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk069[3]! = 0 := rfl
    exact (g 1107 (by decide) (by decide)).trans ((cell1104 3 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1108 : Word) := by simp [hpc]
    rw [this, (rfl : (1108 : Word) = UInt16.ofNat 1108)]
    have hval : decChunk069[4]! = 18 := rfl
    exact (g 1108 (by decide) (by decide)).trans ((cell1104 4 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1113 := by
    have : s.pc + 2 = (1109 : Word) := by simp [hpc]
    rw [this, (rfl : (1109 : Word) = UInt16.ofNat 1109)]
    have hval : decChunk069[5]! = 1113 := rfl
    exact (g 1109 (by decide) (by decide)).trans ((cell1104 5 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP AFTER_SIGN at pc 1110 (no room for sign). -/
theorem pl_enc_jmp_1110 {s : Machine}
    (hpc : s.pc = 1110)
    (hcode : ∀ k : Nat, 1110 ≤ k → k < 1110+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1152 := by
  have hp : s.pc = UInt16.ofNat 1110 :=
    hpc.trans (rfl : (1110 : Word) = UInt16.ofNat 1110)
  have g (k : Nat) (h1 : 1110 ≤ k) (h2 : k < 1110+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk069[6]! = 0 := rfl
    exact (g 1110 (by decide) (by decide)).trans ((cell1104 6 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1111 : Word) := by simp [hpc]
    rw [this, (rfl : (1111 : Word) = UInt16.ofNat 1111)]
    have hval : decChunk069[7]! = 0 := rfl
    exact (g 1111 (by decide) (by decide)).trans ((cell1104 7 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1152 := by
    have : s.pc + 2 = (1112 : Word) := by simp [hpc]
    rw [this, (rfl : (1112 : Word) = UInt16.ofNat 1112)]
    have hval : decChunk069[8]! = 1152 := rfl
    exact (g 1112 (by decide) (by decide)).trans ((cell1104 8 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- INC T at SG_EQ (pc 1113). -/
theorem pl_inc_T_1113 {s : Machine}
    (hpc : s.pc = 1113)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1113 ≤ k → k < 1122 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1122 ∧
    s3.halted = false ∧
    s3.mem.get 18 = s.mem.get 18 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1113 :=
    hpc.trans (rfl : (1113 : Word) = UInt16.ofNat 1113)
  have g (k : Nat) (h1 : 1113 ≤ k) (h2 : k < 1122) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1113 + off) :=
    word_pc_off 1113 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk069[9]! = 3 := rfl
    exact (g 1113 (by decide) (by decide)).trans ((cell1104 9 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk069[10]! = 0 := rfl
    exact (g 1114 (by decide) (by decide)).trans ((cell1104 10 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk069[11]! = 1116 := rfl
    have hv : (1116 : Word) = UInt16.ofNat 1116 := rfl
    exact (g 1115 (by decide) (by decide)).trans ((cell1104 11 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk069[12]! = 0 := rfl
    exact (g 1116 (by decide) (by decide)).trans ((cell1104 12 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 18 := by
    rw [poff 4 (by decide)]
    have hval : decChunk069[13]! = 18 := rfl
    exact (g 1117 (by decide) (by decide)).trans ((cell1104 13 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk069[14]! = 1119 := rfl
    have hv : (1119 : Word) = UInt16.ofNat 1119 := rfl
    exact (g 1118 (by decide) (by decide)).trans ((cell1104 14 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk069[15]! = 0 := rfl
    exact (g 1119 (by decide) (by decide)).trans ((cell1104 15 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk070[0]! = 0 := rfl
    exact (g 1120 (by decide) (by decide)).trans ((cell1120 0 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk070[1]! = 1122 := rfl
    have hv : (1122 : Word) = UInt16.ofNat 1122 := rfl
    exact (g 1121 (by decide) (by decide)).trans ((cell1120 1 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1113 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1113 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1122 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1122 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1122 = (1122 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 18 = s.mem.get 18 + 1 := by
    have : s.mem.get 18 + s.mem.get 3 = s.mem.get 18 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- JLEZ T SG_WRITE at pc 1122. -/
theorem pl_enc_jlez_1122 {s : Machine}
    (hpc : s.pc = 1122)
    (hcode : ∀ k : Nat, 1122 ≤ k → k < 1122+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1128 := by
  have hp : s.pc = UInt16.ofNat 1122 :=
    hpc.trans (rfl : (1122 : Word) = UInt16.ofNat 1122)
  have g (k : Nat) (h1 : 1122 ≤ k) (h2 : k < 1122+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk070[2]! = 0 := rfl
    exact (g 1122 (by decide) (by decide)).trans ((cell1120 2 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1123 : Word) := by simp [hpc]
    rw [this, (rfl : (1123 : Word) = UInt16.ofNat 1123)]
    have hval : decChunk070[3]! = 18 := rfl
    exact (g 1123 (by decide) (by decide)).trans ((cell1120 3 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1128 := by
    have : s.pc + 2 = (1124 : Word) := by simp [hpc]
    rw [this, (rfl : (1124 : Word) = UInt16.ofNat 1124)]
    have hval : decChunk070[4]! = 1128 := rfl
    exact (g 1124 (by decide) (by decide)).trans ((cell1120 4 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP AFTER_SIGN at pc 1125 (IDX = ROOM). -/
theorem pl_enc_jmp_1125 {s : Machine}
    (hpc : s.pc = 1125)
    (hcode : ∀ k : Nat, 1125 ≤ k → k < 1125+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1152 := by
  have hp : s.pc = UInt16.ofNat 1125 :=
    hpc.trans (rfl : (1125 : Word) = UInt16.ofNat 1125)
  have g (k : Nat) (h1 : 1125 ≤ k) (h2 : k < 1125+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk070[5]! = 0 := rfl
    exact (g 1125 (by decide) (by decide)).trans ((cell1120 5 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1126 : Word) := by simp [hpc]
    rw [this, (rfl : (1126 : Word) = UInt16.ofNat 1126)]
    have hval : decChunk070[6]! = 0 := rfl
    exact (g 1126 (by decide) (by decide)).trans ((cell1120 6 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1152 := by
    have : s.pc + 2 = (1127 : Word) := by simp [hpc]
    rw [this, (rfl : (1127 : Word) = UInt16.ofNat 1127)]
    have hval : decChunk070[7]! = 1152 := rfl
    exact (g 1127 (by decide) (by decide)).trans ((cell1120 7 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV ONE RETID at SG_WRITE (pc 1128). -/
theorem pl_mov_ONE_RETID_1128 {s : Machine}
    (hpc : s.pc = 1128)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1128 ≤ k → k < 1140 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1140 ∧
    s4.halted = false ∧
    s4.mem.get 2319 = s.mem.get 3 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 3 = s.mem.get 3 ∧
    (∀ a, a ≠ 2319 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1128 :=
    hpc.trans (rfl : (1128 : Word) = UInt16.ofNat 1128)
  have g (k : Nat) (h1 : 1128 ≤ k) (h2 : k < 1140) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1128 + off) :=
    word_pc_off 1128 off hp (by omega)
  have m0 : s.mem.get s.pc = 2319 := by
    rw [hp]
    have hval : decChunk070[8]! = 2319 := rfl
    exact (g 1128 (by decide) (by decide)).trans ((cell1120 8 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 2319 := by
    rw [poff 1 (by decide)]
    have hval : decChunk070[9]! = 2319 := rfl
    exact (g 1129 (by decide) (by decide)).trans ((cell1120 9 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk070[10]! = 1131 := rfl
    have hv : (1131 : Word) = UInt16.ofNat 1131 := rfl
    exact (g 1130 (by decide) (by decide)).trans ((cell1120 10 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 3 := by
    rw [poff 3 (by decide)]
    have hval : decChunk070[11]! = 3 := rfl
    exact (g 1131 (by decide) (by decide)).trans ((cell1120 11 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk070[12]! = 0 := rfl
    exact (g 1132 (by decide) (by decide)).trans ((cell1120 12 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk070[13]! = 1134 := rfl
    have hv : (1134 : Word) = UInt16.ofNat 1134 := rfl
    exact (g 1133 (by decide) (by decide)).trans ((cell1120 13 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk070[14]! = 0 := rfl
    exact (g 1134 (by decide) (by decide)).trans ((cell1120 14 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 2319 := by
    rw [poff 7 (by decide)]
    have hval : decChunk070[15]! = 2319 := rfl
    exact (g 1135 (by decide) (by decide)).trans ((cell1120 15 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk071[0]! = 1137 := rfl
    have hv : (1137 : Word) = UInt16.ofNat 1137 := rfl
    exact (g 1136 (by decide) (by decide)).trans ((cell1136 0 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk071[1]! = 0 := rfl
    exact (g 1137 (by decide) (by decide)).trans ((cell1136 1 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk071[2]! = 0 := rfl
    exact (g 1138 (by decide) (by decide)).trans ((cell1136 2 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk071[3]! = 1140 := rfl
    have hv : (1140 : Word) = UInt16.ofNat 1140 := rfl
    exact (g 1139 (by decide) (by decide)).trans ((cell1136 3 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (2319 : Word) := by
    intro i hi
    have : (2319 : Word) = UInt16.ofNat 2319 := rfl
    rw [this]
    exact pc_off_ne 1128 i 2319 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1128 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 3) (dst := 2319)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1140 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1140 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1140 = (1140 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- INC RETID at pc 1140 (RETID = 2). -/
theorem pl_inc_RETID_1140 {s : Machine}
    (hpc : s.pc = 1140)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1140 ≤ k → k < 1149 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1149 ∧
    s3.halted = false ∧
    s3.mem.get 2319 = s.mem.get 2319 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 2319 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1140 :=
    hpc.trans (rfl : (1140 : Word) = UInt16.ofNat 1140)
  have g (k : Nat) (h1 : 1140 ≤ k) (h2 : k < 1149) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1140 + off) :=
    word_pc_off 1140 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk071[4]! = 3 := rfl
    exact (g 1140 (by decide) (by decide)).trans ((cell1136 4 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk071[5]! = 0 := rfl
    exact (g 1141 (by decide) (by decide)).trans ((cell1136 5 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk071[6]! = 1143 := rfl
    have hv : (1143 : Word) = UInt16.ofNat 1143 := rfl
    exact (g 1142 (by decide) (by decide)).trans ((cell1136 6 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk071[7]! = 0 := rfl
    exact (g 1143 (by decide) (by decide)).trans ((cell1136 7 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 2319 := by
    rw [poff 4 (by decide)]
    have hval : decChunk071[8]! = 2319 := rfl
    exact (g 1144 (by decide) (by decide)).trans ((cell1136 8 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk071[9]! = 1146 := rfl
    have hv : (1146 : Word) = UInt16.ofNat 1146 := rfl
    exact (g 1145 (by decide) (by decide)).trans ((cell1136 9 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk071[10]! = 0 := rfl
    exact (g 1146 (by decide) (by decide)).trans ((cell1136 10 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk071[11]! = 0 := rfl
    exact (g 1147 (by decide) (by decide)).trans ((cell1136 11 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk071[12]! = 1149 := rfl
    have hv : (1149 : Word) = UInt16.ofNat 1149 := rfl
    exact (g 1148 (by decide) (by decide)).trans ((cell1136 12 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (2319 : Word) := by
    intro i hi
    have : (2319 : Word) = UInt16.ofNat 2319 := rfl
    rw [this]
    exact pc_off_ne 1140 i 2319 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1140 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 2319)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1149 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1149 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1149 = (1149 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 2319 = s.mem.get 2319 + 1 := by
    have : s.mem.get 2319 + s.mem.get 3 = s.mem.get 2319 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- JMP WRITE_MINUS at pc 1149. -/
theorem pl_enc_jmp_1149 {s : Machine}
    (hpc : s.pc = 1149)
    (hcode : ∀ k : Nat, 1149 ≤ k → k < 1149+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1170 := by
  have hp : s.pc = UInt16.ofNat 1149 :=
    hpc.trans (rfl : (1149 : Word) = UInt16.ofNat 1149)
  have g (k : Nat) (h1 : 1149 ≤ k) (h2 : k < 1149+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk071[13]! = 0 := rfl
    exact (g 1149 (by decide) (by decide)).trans ((cell1136 13 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1150 : Word) := by simp [hpc]
    rw [this, (rfl : (1150 : Word) = UInt16.ofNat 1150)]
    have hval : decChunk071[14]! = 0 := rfl
    exact (g 1150 (by decide) (by decide)).trans ((cell1136 14 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1170 := by
    have : s.pc + 2 = (1151 : Word) := by simp [hpc]
    rw [this, (rfl : (1151 : Word) = UInt16.ofNat 1151)]
    have hval : decChunk071[15]! = 1170 := rfl
    exact (g 1151 (by decide) (by decide)).trans ((cell1136 15 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩


/-- `IDX < ROOM` (both below the sign bit) makes `IDX - ROOM` a high-bit word. -/
theorem idx_lt_room_le0 (idx room : Word)
    (hR : room.toNat < 32768) (h : idx.toNat < room.toNat) :
    le0 (idx - room) = true := by
  have htn := word_sub_lt idx room h
  have hhi : 32768 ≤ (idx - room).toNat := by omega
  exact le0_hi hhi

/-- After `INC T` on that difference, the result is still `le0`. -/
theorem idx_lt_room_inc_le0 (idx room : Word)
    (hR : room.toNat < 32768) (h : idx.toNat < room.toNat) :
    le0 ((idx - room) + 1) = true := by
  have htn := word_sub_lt idx room h
  have hd : (room.toNat - idx.toNat) ≥ 1 := by omega
  have hT : 32769 ≤ (idx - room).toNat := by omega
  have hT2 : (idx - room).toNat ≤ 65535 := by
    have : (idx - room).toNat < 65536 := by
      simpa [show UInt16.size = 65536 from rfl] using UInt16.toNat_lt_size (idx - room)
    omega
  by_cases h65535 : (idx - room).toNat = 65535
  · have hwrap := word_add_one_wrap (idx - room) h65535
    have : (idx - room) + 1 = 0 := hwrap
    rw [this]
    exact le0_zero
  · have hsum : (idx - room).toNat + 1 < 65536 := by omega
    have hadd := word_add_one_toNat (idx - room) hsum
    have hhi : 32768 ≤ ((idx - room) + 1).toNat := by omega
    exact le0_hi hhi

/-- `WRITE_SPACE`: 5 steps, `CH = ' '`, pc = `STORE_CH`. -/
theorem write_space {s : Machine}
    (hpc : s.pc = 1155)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK32 : s.mem.get 10 = 32)
    (hcode : ∀ k : Nat, 1155 ≤ k → k < 1170 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1185 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 30 = 32 ∧
    (∀ a, a ≠ 30 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := ap_mov_K32_CH (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1167 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4CH : s4.mem.get 30 = 32 := hm.2.2.1.trans hK32
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1167 ≤ k → k < 1170 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have henc := ap_enc_jmp_1167 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1185)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1185 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5CH : s5.mem.get 30 = 32 := by rw [hrun, hjmp]; exact hs4CH
  have hpres : ∀ a, a ≠ 30 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha30 ha0
    rw [hrun, hjmp]; exact hpres4 a ha30 ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5CH, hpres⟩

/-- `WRITE_MINUS`: 5 steps, `CH = '-'`, pc = `STORE_CH`. -/
theorem write_minus {s : Machine}
    (hpc : s.pc = 1170)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hK45 : s.mem.get 9 = 45)
    (hcode : ∀ k : Nat, 1170 ≤ k → k < 1185 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1185 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 30 = 45 ∧
    (∀ a, a ≠ 30 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := ap_mov_K45_CH (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1182 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4CH : s4.mem.get 30 = 45 := hm.2.2.1.trans hK45
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1182 ≤ k → k < 1185 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have henc := ap_enc_jmp_1182 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1185)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1185 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5CH : s5.mem.get 30 = 45 := by rw [hrun, hjmp]; exact hs4CH
  have hpres : ∀ a, a ≠ 30 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha30 ha0
    rw [hrun, hjmp]; exact hpres4 a ha30 ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5CH, hpres⟩

/-- From `WRITE_SPACE` with `IDX = 0` and `RETID = 1`: write `' '` at `BUF+0`,
return to `SP_LOOP` with `IDX = 1` and `PAD -= 1`. 26 steps. -/
theorem write_space_pad_idx0 {s : Machine}
    (hpc : s.pc = 1155)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hR : s.mem.get 2319 = 1)
    (hcode : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s26 := runN s 26
    s26.pc = 1011 ∧
    s26.halted = false ∧
    s26.mem.get 0 = 0 ∧
    s26.mem.get 32 = 32 ∧
    s26.mem.get 29 = 1 ∧
    s26.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      s26.mem.get a = s.mem.get a) := by
  intro s26
  have hw := write_space (s := s) hpc hh hZ hK32
    (fun k h1 h2 => hcode k h1 (by omega))
  let s5 := runN s 5
  have hs5pc : s5.pc = 1185 := hw.1
  have hs5h : s5.halted = false := hw.2.1
  have hs5Z : s5.mem.get 0 = 0 := hw.2.2.1
  have hs5CH : s5.mem.get 30 = 32 := hw.2.2.2.1
  have hpres5 := hw.2.2.2.2
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 0 := (hpres5 29 (by decide) (by decide)).trans hI
  have hR5 : s5.mem.get 2319 = 1 := (hpres5 2319 (by decide) (by decide)).trans hR
  have hP5 : s5.mem.get 27 = s.mem.get 27 := hpres5 27 (by decide) (by decide)
  have g5 : ∀ k : Nat, 1185 ≤ k → k < 1200 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have gst : ∀ k : Nat, 1287 ≤ k → k < 1302 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hs := store_ch_idx0 (s := s5) hs5pc hs5h hs5Z hI5 g5 gst
  have hrun15 : runN s 15 = runN s5 10 := runN_add_eq s 5 10 15 (by decide)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1527 := by have : s15 = runN s5 10 := hrun15; rw [this]; exact hs.1
  have hs15h : s15.halted = false := by have : s15 = runN s5 10 := hrun15; rw [this]; exact hs.2.1
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = runN s5 10 := hrun15; rw [this]; exact hs.2.2.1
  have hs15B : s15.mem.get 32 = 32 := by
    have : s15 = runN s5 10 := hrun15
    rw [this]; exact hs.2.2.2.1.trans hs5CH
  have hs15I : s15.mem.get 29 = 0 := by have : s15 = runN s5 10 := hrun15; rw [this]; exact hs.2.2.2.2.1
  have hONE15 : s15.mem.get 3 = 1 := by
    have : s15 = runN s5 10 := hrun15
    rw [this]; exact (hs.2.2.2.2.2 3 (by decide) (by decide) (by decide)).trans hONE5
  have hR15 : s15.mem.get 2319 = 1 := by
    have : s15 = runN s5 10 := hrun15
    rw [this]; exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hR5
  have hP15 : s15.mem.get 27 = s.mem.get 27 := by
    have : s15 = runN s5 10 := hrun15
    rw [this]; exact (hs.2.2.2.2.2 27 (by decide) (by decide) (by decide)).trans hP5
  have hpres15 : ∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha32 ha18 ha30 ha0
    have : s15 = runN s5 10 := hrun15
    rw [this]
    exact (hs.2.2.2.2.2 a ha32 ha18 ha0).trans (hpres5 a ha30 ha0)
  have g15 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres15 (UInt16.ofNat k) n32 n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hr := stored_ret_pad (s := s15) hs15pc hs15h hs15Z hONE15 hR15 g15
  have hrun : s26 = runN s15 11 := runN_add_eq s 15 11 26 (by decide)
  have hs26pc : s26.pc = 1011 := by rw [hrun]; exact hr.1
  have hs26h : s26.halted = false := by rw [hrun]; exact hr.2.1
  have hs26Z : s26.mem.get 0 = 0 := by rw [hrun]; exact hr.2.2.1
  have hs26I : s26.mem.get 29 = 1 := by
    rw [hrun]
    have : s15.mem.get 29 + 1 = (0 : Word) + 1 := by rw [hs15I]
    exact hr.2.2.2.1.trans (this.trans (rfl : (0 : Word) + 1 = 1))
  have hs26P : s26.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun]
    exact hr.2.2.2.2.1.trans (by rw [hP15])
  have hs26B : s26.mem.get 32 = 32 := by
    rw [hrun]
    exact (hr.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide)).trans hs15B
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      s26.mem.get a = s.mem.get a := by
    intro a ha32 ha29 ha27 ha18 ha30 ha0
    rw [hrun]
    exact (hr.2.2.2.2.2 a ha29 ha27 ha18 ha0).trans (hpres15 a ha32 ha18 ha30 ha0)
  exact ⟨hs26pc, hs26h, hs26Z, hs26B, hs26I, hs26P, hpres⟩

/-- From `WRITE_MINUS` with `IDX = 0` and `RETID = 2`: write `'-'` at `BUF+0`,
return to `AFTER_SIGN` with `IDX = 1`. 27 steps. -/
theorem write_minus_sign_idx0 {s : Machine}
    (hpc : s.pc = 1170)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK45 : s.mem.get 9 = 45)
    (hI : s.mem.get 29 = 0)
    (hR : s.mem.get 2319 = 2)
    (hcode : ∀ k : Nat, 1170 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s27 := runN s 27
    s27.pc = 1152 ∧
    s27.halted = false ∧
    s27.mem.get 0 = 0 ∧
    s27.mem.get 32 = 45 ∧
    s27.mem.get 29 = 1 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      s27.mem.get a = s.mem.get a) := by
  intro s27
  have hw := write_minus (s := s) hpc hh hZ hK45
    (fun k h1 h2 => hcode k h1 (by omega))
  let s5 := runN s 5
  have hs5pc : s5.pc = 1185 := hw.1
  have hs5h : s5.halted = false := hw.2.1
  have hs5Z : s5.mem.get 0 = 0 := hw.2.2.1
  have hs5CH : s5.mem.get 30 = 45 := hw.2.2.2.1
  have hpres5 := hw.2.2.2.2
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 0 := (hpres5 29 (by decide) (by decide)).trans hI
  have hR5 : s5.mem.get 2319 = 2 := (hpres5 2319 (by decide) (by decide)).trans hR
  have g5 : ∀ k : Nat, 1185 ≤ k → k < 1200 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have gst : ∀ k : Nat, 1287 ≤ k → k < 1302 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hs := store_ch_idx0 (s := s5) hs5pc hs5h hs5Z hI5 g5 gst
  have hrun15 : runN s 15 = runN s5 10 := runN_add_eq s 5 10 15 (by decide)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1527 := by have : s15 = runN s5 10 := hrun15; rw [this]; exact hs.1
  have hs15h : s15.halted = false := by have : s15 = runN s5 10 := hrun15; rw [this]; exact hs.2.1
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = runN s5 10 := hrun15; rw [this]; exact hs.2.2.1
  have hs15B : s15.mem.get 32 = 45 := by
    have : s15 = runN s5 10 := hrun15
    rw [this]; exact hs.2.2.2.1.trans hs5CH
  have hs15I : s15.mem.get 29 = 0 := by have : s15 = runN s5 10 := hrun15; rw [this]; exact hs.2.2.2.2.1
  have hONE15 : s15.mem.get 3 = 1 := by
    have : s15 = runN s5 10 := hrun15
    rw [this]; exact (hs.2.2.2.2.2 3 (by decide) (by decide) (by decide)).trans hONE5
  have hR15 : s15.mem.get 2319 = 2 := by
    have : s15 = runN s5 10 := hrun15
    rw [this]; exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hR5
  have hpres15 : ∀ a, a ≠ 32 → a ≠ 18 → a ≠ 30 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha32 ha18 ha30 ha0
    have : s15 = runN s5 10 := hrun15
    rw [this]
    exact (hs.2.2.2.2.2 a ha32 ha18 ha0).trans (hpres5 a ha30 ha0)
  have g15 : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres15 (UInt16.ofNat k) n32 n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hr := stored_ret_sign (s := s15) hs15pc hs15h hs15Z hONE15 hR15 g15
  have hrun : s27 = runN s15 12 := runN_add_eq s 15 12 27 (by decide)
  have hs27pc : s27.pc = 1152 := by rw [hrun]; exact hr.1
  have hs27h : s27.halted = false := by rw [hrun]; exact hr.2.1
  have hs27Z : s27.mem.get 0 = 0 := by rw [hrun]; exact hr.2.2.1
  have hs27I : s27.mem.get 29 = 1 := by
    rw [hrun]
    have : s15.mem.get 29 + 1 = (0 : Word) + 1 := by rw [hs15I]
    exact hr.2.2.2.1.trans (this.trans (rfl : (0 : Word) + 1 = 1))
  have hs27B : s27.mem.get 32 = 45 := by
    rw [hrun]
    exact (hr.2.2.2.2 32 (by decide) (by decide) (by decide)).trans hs15B
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      s27.mem.get a = s.mem.get a := by
    intro a ha32 ha29 ha18 ha30 ha0
    rw [hrun]
    exact (hr.2.2.2.2 a ha29 ha18 ha0).trans (hpres15 a ha32 ha18 ha30 ha0)
  exact ⟨hs27pc, hs27h, hs27Z, hs27B, hs27I, hpres⟩

/-- `SP_LOOP` with `PAD > 0` and `IDX < ROOM`: 20 steps to `WRITE_SPACE`,
`RETID = 1`. Leaves `PAD`, `IDX`, `ROOM` unchanged. -/
theorem sp_loop_to_write_space {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hPlo : 0 < (s.mem.get 27).toNat)
    (hPhi : (s.mem.get 27).toNat < 32768)
    (hIlt : (s.mem.get 29).toNat < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1077 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s20 := runN s 20
    s20.pc = 1155 ∧
    s20.halted = false ∧
    s20.mem.get 0 = 0 ∧
    s20.mem.get 2319 = 1 ∧
    s20.mem.get 27 = s.mem.get 27 ∧
    s20.mem.get 29 = s.mem.get 29 ∧
    s20.mem.get 28 = s.mem.get 28 ∧
    (∀ a, a ≠ 18 → a ≠ 2319 → a ≠ 0 → s20.mem.get a = s.mem.get a) := by
  intro s20
  -- 4: MOV PAD T
  have hm1 := pad_mov_PAD_T_1011 (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1023 := hm1.1
  have hs4h : s4.halted = false := hm1.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 27 := hm1.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm1.2.2.2.1
  have hpres4 := hm1.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hP4 : s4.mem.get 27 = s.mem.get 27 := hpres4 27 (by decide) (by decide)
  have hI4 : s4.mem.get 29 = s.mem.get 29 := hpres4 29 (by decide) (by decide)
  have hR4 : s4.mem.get 28 = s.mem.get 28 := hpres4 28 (by decide) (by decide)
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
  have henc1 := pad_enc_jlez_1023 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hj1 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1077)
      hs4h hpc4 hs4Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos hPlo hPhi
    simpa [le0] using this
  have hs5eq' : step s4 = { s4 with pc := 1026 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1077 : Word) else s4.pc + 3) = (1026 : Word) := by
      have hfall : s4.pc + 3 = (1026 : Word) := by simp [hs4pc]
      simp [hle1, hfall]
    rw [hj1, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1026 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4Z
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq']; exact hpres4 a ha18 ha0
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hP5 : s5.mem.get 27 = s.mem.get 27 := hpres5 27 (by decide) (by decide)
  have hI5 : s5.mem.get 29 = s.mem.get 29 := hpres5 29 (by decide) (by decide)
  have hR5 : s5.mem.get 28 = s.mem.get 28 := hpres5 28 (by decide) (by decide)
  have g5 : ∀ k : Nat, 1026 ≤ k → k < 1038 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  -- 4: MOV IDX T
  have hm2 := pl_mov_IDX_T_1026 (s := s5) hs5pc hs5h hs5Z g5
  have hrun9 : runN s 9 = runN s5 4 := runN_add_eq s 5 4 9 (by decide)
  let s9 := runN s 9
  have hs9eq : s9 = runN s5 4 := hrun9
  have hs9pc : s9.pc = 1038 := by rw [hs9eq]; exact hm2.1
  have hs9h : s9.halted = false := by rw [hs9eq]; exact hm2.2.1
  have hs9T : s9.mem.get 18 = s.mem.get 29 := by
    rw [hs9eq]; exact hm2.2.2.1.trans hI5
  have hs9Z : s9.mem.get 0 = 0 := by rw [hs9eq]; exact hm2.2.2.2.1
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs9eq]; exact (hm2.2.2.2.2.2 a ha18 ha0).trans (hpres5 a ha18 ha0)
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide)).trans hONE
  have hP9 : s9.mem.get 27 = s.mem.get 27 := hpres9 27 (by decide) (by decide)
  have hI9 : s9.mem.get 29 = s.mem.get 29 := hpres9 29 (by decide) (by decide)
  have hR9 : s9.mem.get 28 = s.mem.get 28 := hpres9 28 (by decide) (by decide)
  have g9 : ∀ k : Nat, 1038 ≤ k → k < 1044 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  -- 1: SUB ROOM T
  have hsub := pl_sub_ROOM_T_1038 (s := s9) hs9pc hs9h
    (fun k h1 h2 => g9 k h1 (by omega))
  have hrun10 : runN s 10 = step s9 := by
    have h10 : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
    exact h10.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hs10eq' : s10 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 28), pc := 1041 } := by
    have : s10 = step s9 := hrun10
    rw [this, hsub]
  have hs10pc : s10.pc = 1041 := by rw [hs10eq']
  have hs10h : s10.halted = false := by rw [hs10eq']; exact hs9h
  have hs10T : s10.mem.get 18 = s.mem.get 29 - s.mem.get 28 := by
    rw [hs10eq', Mem.get_set_eq, hs9T, hR9]
  have hs10Z : s10.mem.get 0 = 0 := by
    rw [hs10eq']
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 28) (by decide)).trans hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs10eq']
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 28) ha18).trans
      (hpres9 a ha18 ha0)
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hP10 : s10.mem.get 27 = s.mem.get 27 := hpres10 27 (by decide) (by decide)
  have hI10 : s10.mem.get 29 = s.mem.get 29 := hpres10 29 (by decide) (by decide)
  have hR10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1041 ≤ k → k < 1044 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc2 := pl_enc_jlez_1041 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hj2 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1047)
      hs10h hpc10 hs10Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = true := by
    have : le0 (s10.mem.get 18) = true := by
      rw [hs10T]; exact idx_lt_room_le0 (s.mem.get 29) (s.mem.get 28) hRhi hIlt
    simpa [le0] using this
  have hs11eq' : step s10 = { s10 with pc := 1047 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1047 : Word) else s10.pc + 3) = (1047 : Word) := by
      simp [hle2]
    rw [hj2, hif]
  have hrun11 : runN s 11 = step s10 := by
    have h11 : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact h11.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1047 := by have : s11 = step s10 := hrun11; rw [this, hs11eq']
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq']; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq']; exact hs10Z
  have hs11T : s11.mem.get 18 = s.mem.get 29 - s.mem.get 28 := by
    have : s11 = step s10 := hrun11; rw [this, hs11eq']; exact hs10T
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq']; exact hpres10 a ha18 ha0
  have hONE11 : s11.mem.get 3 = 1 := (hpres11 3 (by decide) (by decide)).trans hONE
  have hP11 : s11.mem.get 27 = s.mem.get 27 := hpres11 27 (by decide) (by decide)
  have hI11 : s11.mem.get 29 = s.mem.get 29 := hpres11 29 (by decide) (by decide)
  have hR11 : s11.mem.get 28 = s.mem.get 28 := hpres11 28 (by decide) (by decide)
  have g11 : ∀ k : Nat, 1047 ≤ k → k < 1056 →
      s11.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres11 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  -- 3: INC T
  have hinc := pl_inc_T_1047 (s := s11) hs11pc hs11h hs11Z hONE11 g11
  have hrun14 : runN s 14 = runN s11 3 := runN_add_eq s 11 3 14 (by decide)
  let s14 := runN s 14
  have hs14eq : s14 = runN s11 3 := hrun14
  have hs14pc : s14.pc = 1056 := by rw [hs14eq]; exact hinc.1
  have hs14h : s14.halted = false := by rw [hs14eq]; exact hinc.2.1
  have hs14T : s14.mem.get 18 = (s.mem.get 29 - s.mem.get 28) + 1 := by
    rw [hs14eq, hinc.2.2.1, hs11T]
  have hs14Z : s14.mem.get 0 = 0 := by rw [hs14eq]; exact hinc.2.2.2.1
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs14eq]; exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres11 a ha18 ha0)
  have hONE14 : s14.mem.get 3 = 1 := (hpres14 3 (by decide) (by decide)).trans hONE
  have hP14 : s14.mem.get 27 = s.mem.get 27 := hpres14 27 (by decide) (by decide)
  have hI14 : s14.mem.get 29 = s.mem.get 29 := hpres14 29 (by decide) (by decide)
  have hR14 : s14.mem.get 28 = s.mem.get 28 := hpres14 28 (by decide) (by decide)
  have g14 : ∀ k : Nat, 1056 ≤ k → k < 1059 →
      s14.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres14 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc3 := pl_enc_jlez_1056 (s := s14) hs14pc g14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hj3 :=
    step_JLEZ (s := s14) (x := 18) (dest := 1062)
      hs14h hpc14 hs14Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18) = true := by
    have : le0 (s14.mem.get 18) = true := by
      rw [hs14T]; exact idx_lt_room_inc_le0 (s.mem.get 29) (s.mem.get 28) hRhi hIlt
    simpa [le0] using this
  have hs15eq' : step s14 = { s14 with pc := 1062 } := by
    have hif :
        (if s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18
          then (1062 : Word) else s14.pc + 3) = (1062 : Word) := by
      simp [hle3]
    rw [hj3, hif]
  have hrun15 : runN s 15 = step s14 := by
    have h15 : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    exact h15.trans (runN_one s14 hs14h hpc14)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1062 := by have : s15 = step s14 := hrun15; rw [this, hs15eq']
  have hs15h : s15.halted = false := by have : s15 = step s14 := hrun15; rw [this, hs15eq']; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq']; exact hs14Z
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s15 = step s14 := hrun15
    rw [this, hs15eq']; exact hpres14 a ha18 ha0
  have hONE15 : s15.mem.get 3 = 1 := (hpres15 3 (by decide) (by decide)).trans hONE
  have hP15 : s15.mem.get 27 = s.mem.get 27 := hpres15 27 (by decide) (by decide)
  have hI15 : s15.mem.get 29 = s.mem.get 29 := hpres15 29 (by decide) (by decide)
  have hR15 : s15.mem.get 28 = s.mem.get 28 := hpres15 28 (by decide) (by decide)
  have g15 : ∀ k : Nat, 1062 ≤ k → k < 1074 →
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres15 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  -- 4: MOV ONE RETID
  have hm3 := pl_mov_ONE_RETID_1062 (s := s15) hs15pc hs15h hs15Z g15
  have hrun19 : runN s 19 = runN s15 4 := runN_add_eq s 15 4 19 (by decide)
  let s19 := runN s 19
  have hs19eq : s19 = runN s15 4 := hrun19
  have hs19pc : s19.pc = 1074 := by rw [hs19eq]; exact hm3.1
  have hs19h : s19.halted = false := by rw [hs19eq]; exact hm3.2.1
  have hs19R : s19.mem.get 2319 = 1 := by
    rw [hs19eq, hm3.2.2.1]
    exact (hpres15 3 (by decide) (by decide)).trans hONE
  have hs19Z : s19.mem.get 0 = 0 := by rw [hs19eq]; exact hm3.2.2.2.1
  have hpres19 : ∀ a, a ≠ 18 → a ≠ 2319 → a ≠ 0 → s19.mem.get a = s.mem.get a := by
    intro a ha18 haR ha0
    rw [hs19eq]
    exact (hm3.2.2.2.2.2 a haR ha0).trans (hpres15 a ha18 ha0)
  have hP19 : s19.mem.get 27 = s.mem.get 27 := hpres19 27 (by decide) (by decide) (by decide)
  have hI19 : s19.mem.get 29 = s.mem.get 29 := hpres19 29 (by decide) (by decide) (by decide)
  have hR19 : s19.mem.get 28 = s.mem.get 28 := hpres19 28 (by decide) (by decide) (by decide)
  have g19 : ∀ k : Nat, 1074 ≤ k → k < 1077 →
      s19.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres19 (UInt16.ofNat k) n18 nR n0).trans (hcode k (by omega) (by omega))
  have henc4 := pl_enc_jmp_1074 (s := s19) hs19pc g19
  have hpc19 : s19.pc.toNat < 32768 := by simp [hs19pc]
  have hj4 := step_JMP (s := s19) (dest := 1155)
    hs19h hpc19 hs19Z henc4.1 henc4.2.1 henc4.2.2
  have hrun : s20 = runN s19 1 := runN_add_eq s 19 1 20 (by decide)
  have hs20eq : s20 = step s19 := hrun.trans (runN_one s19 hs19h hpc19)
  have hs20pc : s20.pc = 1155 := by rw [hs20eq, hj4]
  have hs20h : s20.halted = false := by rw [hs20eq, hj4]; exact hs19h
  have hs20Z : s20.mem.get 0 = 0 := by rw [hs20eq, hj4]; exact hs19Z
  have hs20R : s20.mem.get 2319 = 1 := by rw [hs20eq, hj4]; exact hs19R
  have hs20P : s20.mem.get 27 = s.mem.get 27 := by rw [hs20eq, hj4]; exact hP19
  have hs20I : s20.mem.get 29 = s.mem.get 29 := by rw [hs20eq, hj4]; exact hI19
  have hs20Rm : s20.mem.get 28 = s.mem.get 28 := by rw [hs20eq, hj4]; exact hR19
  have hpres : ∀ a, a ≠ 18 → a ≠ 2319 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a ha18 haR ha0
    rw [hs20eq, hj4]; exact hpres19 a ha18 haR ha0
  exact ⟨hs20pc, hs20h, hs20Z, hs20R, hs20P, hs20I, hs20Rm, hpres⟩

/-- `AFTER_PAD` with `SIGN ≠ 0` and `IDX < ROOM`: 23 steps to `WRITE_MINUS`,
`RETID = 2`. Leaves `SIGN`, `IDX`, `ROOM` unchanged. -/
theorem after_pad_to_write_minus {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hIlt : (s.mem.get 29).toNat < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 1155 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s23 := runN s 23
    s23.pc = 1170 ∧
    s23.halted = false ∧
    s23.mem.get 0 = 0 ∧
    s23.mem.get 2319 = 2 ∧
    s23.mem.get 19 = s.mem.get 19 ∧
    s23.mem.get 29 = s.mem.get 29 ∧
    s23.mem.get 28 = s.mem.get 28 ∧
    (∀ a, a ≠ 18 → a ≠ 2319 → a ≠ 0 → s23.mem.get a = s.mem.get a) := by
  intro s23
  have hm1 := ap_mov_SIGN_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1089 := hm1.1
  have hs4h : s4.halted = false := hm1.2.1
  have hs4T : s4.mem.get 18 = s.mem.get 19 := hm1.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm1.2.2.2.1
  have hpres4 := hm1.2.2.2.2.2
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have hS4 : s4.mem.get 19 = s.mem.get 19 := hpres4 19 (by decide) (by decide)
  have hI4 : s4.mem.get 29 = s.mem.get 29 := hpres4 29 (by decide) (by decide)
  have hR4 : s4.mem.get 28 = s.mem.get 28 := hpres4 28 (by decide) (by decide)
  have g4 : ∀ k : Nat, 1089 ≤ k → k < 1092 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc1 := ap_enc_jlez_1089 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hj1 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1152)
      hs4h hpc4 hs4Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos hSlo hShi
    simpa [le0] using this
  have hs5eq' : step s4 = { s4 with pc := 1092 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1152 : Word) else s4.pc + 3) = (1092 : Word) := by
      have hfall : s4.pc + 3 = (1092 : Word) := by simp [hs4pc]
      simp [hle1, hfall]
    rw [hj1, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1092 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq']; exact hs4Z
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq']; exact hpres4 a ha18 ha0
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hS5 : s5.mem.get 19 = s.mem.get 19 := hpres5 19 (by decide) (by decide)
  have hI5 : s5.mem.get 29 = s.mem.get 29 := hpres5 29 (by decide) (by decide)
  have hR5 : s5.mem.get 28 = s.mem.get 28 := hpres5 28 (by decide) (by decide)
  have g5 : ∀ k : Nat, 1092 ≤ k → k < 1104 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hm2 := pl_mov_IDX_T_1092 (s := s5) hs5pc hs5h hs5Z g5
  have hrun9 : runN s 9 = runN s5 4 := runN_add_eq s 5 4 9 (by decide)
  let s9 := runN s 9
  have hs9eq : s9 = runN s5 4 := hrun9
  have hs9pc : s9.pc = 1104 := by rw [hs9eq]; exact hm2.1
  have hs9h : s9.halted = false := by rw [hs9eq]; exact hm2.2.1
  have hs9T : s9.mem.get 18 = s.mem.get 29 := by
    rw [hs9eq]; exact hm2.2.2.1.trans hI5
  have hs9Z : s9.mem.get 0 = 0 := by rw [hs9eq]; exact hm2.2.2.2.1
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs9eq]; exact (hm2.2.2.2.2.2 a ha18 ha0).trans (hpres5 a ha18 ha0)
  have hONE9 : s9.mem.get 3 = 1 := (hpres9 3 (by decide) (by decide)).trans hONE
  have hS9 : s9.mem.get 19 = s.mem.get 19 := hpres9 19 (by decide) (by decide)
  have hI9 : s9.mem.get 29 = s.mem.get 29 := hpres9 29 (by decide) (by decide)
  have hR9 : s9.mem.get 28 = s.mem.get 28 := hpres9 28 (by decide) (by decide)
  have g9 : ∀ k : Nat, 1104 ≤ k → k < 1110 →
      s9.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres9 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hsub := pl_sub_ROOM_T_1104 (s := s9) hs9pc hs9h
    (fun k h1 h2 => g9 k h1 (by omega))
  have hrun10 : runN s 10 = step s9 := by
    have h10 : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
    exact h10.trans (runN_one s9 hs9h hpc9)
  let s10 := runN s 10
  have hs10eq' : s10 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 28), pc := 1107 } := by
    have : s10 = step s9 := hrun10
    rw [this, hsub]
  have hs10pc : s10.pc = 1107 := by rw [hs10eq']
  have hs10h : s10.halted = false := by rw [hs10eq']; exact hs9h
  have hs10T : s10.mem.get 18 = s.mem.get 29 - s.mem.get 28 := by
    rw [hs10eq', Mem.get_set_eq, hs9T, hR9]
  have hs10Z : s10.mem.get 0 = 0 := by
    rw [hs10eq']
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 28) (by decide)).trans hs9Z
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs10eq']
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 28) ha18).trans
      (hpres9 a ha18 ha0)
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have g10 : ∀ k : Nat, 1107 ≤ k → k < 1110 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc2 := pl_enc_jlez_1107 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hj2 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1113)
      hs10h hpc10 hs10Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = true := by
    have : le0 (s10.mem.get 18) = true := by
      rw [hs10T]; exact idx_lt_room_le0 (s.mem.get 29) (s.mem.get 28) hRhi hIlt
    simpa [le0] using this
  have hs11eq' : step s10 = { s10 with pc := 1113 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1113 : Word) else s10.pc + 3) = (1113 : Word) := by
      simp [hle2]
    rw [hj2, hif]
  have hrun11 : runN s 11 = step s10 := by
    have h11 : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact h11.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1113 := by have : s11 = step s10 := hrun11; rw [this, hs11eq']
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq']; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq']; exact hs10Z
  have hs11T : s11.mem.get 18 = s.mem.get 29 - s.mem.get 28 := by
    have : s11 = step s10 := hrun11; rw [this, hs11eq']; exact hs10T
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq']; exact hpres10 a ha18 ha0
  have hONE11 : s11.mem.get 3 = 1 := (hpres11 3 (by decide) (by decide)).trans hONE
  have g11 : ∀ k : Nat, 1113 ≤ k → k < 1122 →
      s11.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres11 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hinc := pl_inc_T_1113 (s := s11) hs11pc hs11h hs11Z hONE11 g11
  have hrun14 : runN s 14 = runN s11 3 := runN_add_eq s 11 3 14 (by decide)
  let s14 := runN s 14
  have hs14eq : s14 = runN s11 3 := hrun14
  have hs14pc : s14.pc = 1122 := by rw [hs14eq]; exact hinc.1
  have hs14h : s14.halted = false := by rw [hs14eq]; exact hinc.2.1
  have hs14T : s14.mem.get 18 = (s.mem.get 29 - s.mem.get 28) + 1 := by
    rw [hs14eq, hinc.2.2.1, hs11T]
  have hs14Z : s14.mem.get 0 = 0 := by rw [hs14eq]; exact hinc.2.2.2.1
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs14eq]; exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres11 a ha18 ha0)
  have hONE14 : s14.mem.get 3 = 1 := (hpres14 3 (by decide) (by decide)).trans hONE
  have g14 : ∀ k : Nat, 1122 ≤ k → k < 1125 →
      s14.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres14 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc3 := pl_enc_jlez_1122 (s := s14) hs14pc g14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hj3 :=
    step_JLEZ (s := s14) (x := 18) (dest := 1128)
      hs14h hpc14 hs14Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18) = true := by
    have : le0 (s14.mem.get 18) = true := by
      rw [hs14T]; exact idx_lt_room_inc_le0 (s.mem.get 29) (s.mem.get 28) hRhi hIlt
    simpa [le0] using this
  have hs15eq' : step s14 = { s14 with pc := 1128 } := by
    have hif :
        (if s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18
          then (1128 : Word) else s14.pc + 3) = (1128 : Word) := by
      simp [hle3]
    rw [hj3, hif]
  have hrun15 : runN s 15 = step s14 := by
    have h15 : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    exact h15.trans (runN_one s14 hs14h hpc14)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1128 := by have : s15 = step s14 := hrun15; rw [this, hs15eq']
  have hs15h : s15.halted = false := by have : s15 = step s14 := hrun15; rw [this, hs15eq']; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq']; exact hs14Z
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s15 = step s14 := hrun15
    rw [this, hs15eq']; exact hpres14 a ha18 ha0
  have hONE15 : s15.mem.get 3 = 1 := (hpres15 3 (by decide) (by decide)).trans hONE
  have g15 : ∀ k : Nat, 1128 ≤ k → k < 1140 →
      s15.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres15 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hm3 := pl_mov_ONE_RETID_1128 (s := s15) hs15pc hs15h hs15Z g15
  have hrun19 : runN s 19 = runN s15 4 := runN_add_eq s 15 4 19 (by decide)
  let s19 := runN s 19
  have hs19eq : s19 = runN s15 4 := hrun19
  have hs19pc : s19.pc = 1140 := by rw [hs19eq]; exact hm3.1
  have hs19h : s19.halted = false := by rw [hs19eq]; exact hm3.2.1
  have hs19R : s19.mem.get 2319 = 1 := by
    rw [hs19eq, hm3.2.2.1]
    exact (hpres15 3 (by decide) (by decide)).trans hONE
  have hs19Z : s19.mem.get 0 = 0 := by rw [hs19eq]; exact hm3.2.2.2.1
  have hpres19 : ∀ a, a ≠ 18 → a ≠ 2319 → a ≠ 0 → s19.mem.get a = s.mem.get a := by
    intro a ha18 haR ha0
    rw [hs19eq]
    exact (hm3.2.2.2.2.2 a haR ha0).trans (hpres15 a ha18 ha0)
  have hONE19 : s19.mem.get 3 = 1 := (hpres19 3 (by decide) (by decide) (by decide)).trans hONE
  have g19 : ∀ k : Nat, 1140 ≤ k → k < 1149 →
      s19.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres19 (UInt16.ofNat k) n18 nR n0).trans (hcode k (by omega) (by omega))
  have hincR := pl_inc_RETID_1140 (s := s19) hs19pc hs19h hs19Z hONE19 g19
  have hrun22 : runN s 22 = runN s19 3 := runN_add_eq s 19 3 22 (by decide)
  let s22 := runN s 22
  have hs22eq : s22 = runN s19 3 := hrun22
  have hs22pc : s22.pc = 1149 := by rw [hs22eq]; exact hincR.1
  have hs22h : s22.halted = false := by rw [hs22eq]; exact hincR.2.1
  have hs22R : s22.mem.get 2319 = 2 := by
    rw [hs22eq, hincR.2.2.1, hs19R]
    exact (rfl : (1 : Word) + 1 = 2)
  have hs22Z : s22.mem.get 0 = 0 := by rw [hs22eq]; exact hincR.2.2.2.1
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 2319 → a ≠ 0 → s22.mem.get a = s.mem.get a := by
    intro a ha18 haR ha0
    rw [hs22eq]; exact (hincR.2.2.2.2 a haR ha0).trans (hpres19 a ha18 haR ha0)
  have hS22 : s22.mem.get 19 = s.mem.get 19 := hpres22 19 (by decide) (by decide) (by decide)
  have hI22 : s22.mem.get 29 = s.mem.get 29 := hpres22 29 (by decide) (by decide) (by decide)
  have hR22 : s22.mem.get 28 = s.mem.get 28 := hpres22 28 (by decide) (by decide) (by decide)
  have g22 : ∀ k : Nat, 1149 ≤ k → k < 1152 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres22 (UInt16.ofNat k) n18 nR n0).trans (hcode k (by omega) (by omega))
  have henc4 := pl_enc_jmp_1149 (s := s22) hs22pc g22
  have hpc22 : s22.pc.toNat < 32768 := by simp [hs22pc]
  have hj4 := step_JMP (s := s22) (dest := 1170)
    hs22h hpc22 hs22Z henc4.1 henc4.2.1 henc4.2.2
  have hrun : s23 = runN s22 1 := runN_add_eq s 22 1 23 (by decide)
  have hs23eq : s23 = step s22 := hrun.trans (runN_one s22 hs22h hpc22)
  have hs23pc : s23.pc = 1170 := by rw [hs23eq, hj4]
  have hs23h : s23.halted = false := by rw [hs23eq, hj4]; exact hs22h
  have hs23Z : s23.mem.get 0 = 0 := by rw [hs23eq, hj4]; exact hs22Z
  have hs23R : s23.mem.get 2319 = 2 := by rw [hs23eq, hj4]; exact hs22R
  have hs23S : s23.mem.get 19 = s.mem.get 19 := by rw [hs23eq, hj4]; exact hS22
  have hs23I : s23.mem.get 29 = s.mem.get 29 := by rw [hs23eq, hj4]; exact hI22
  have hs23Rm : s23.mem.get 28 = s.mem.get 28 := by rw [hs23eq, hj4]; exact hR22
  have hpres : ∀ a, a ≠ 18 → a ≠ 2319 → a ≠ 0 → s23.mem.get a = s.mem.get a := by
    intro a ha18 haR ha0
    rw [hs23eq, hj4]; exact hpres22 a ha18 haR ha0
  exact ⟨hs23pc, hs23h, hs23Z, hs23R, hs23S, hs23I, hs23Rm, hpres⟩

/-- `AFTER_SIGN`: 1 step `JMP EMIT_DIGS`. -/
theorem after_sign_to_emit {s : Machine}
    (hpc : s.pc = 1152)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1152 ≤ k → k < 1155 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s1 := runN s 1
    s1.pc = 1575 ∧
    s1.halted = false ∧
    s1.mem.get 0 = 0 ∧
    (∀ a, a ≠ 0 → s1.mem.get a = s.mem.get a) := by
  intro s1
  have henc := ap_enc_jmp_1152 (s := s) hpc hcode
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hjmp := step_JMP (s := s) (dest := 1575)
    hh hpc0 hZ henc.1 henc.2.1 henc.2.2
  have hs1eq : s1 = step s := runN_one s hh hpc0
  have hs1pc : s1.pc = 1575 := by rw [hs1eq, hjmp]
  have hs1h : s1.halted = false := by rw [hs1eq, hjmp]; exact hh
  have hs1Z : s1.mem.get 0 = 0 := by rw [hs1eq, hjmp]; exact hZ
  have hpres : ∀ a, a ≠ 0 → s1.mem.get a = s.mem.get a := by
    intro a ha0
    rw [hs1eq, hjmp]
  exact ⟨hs1pc, hs1h, hs1Z, hpres⟩

/-- One padding write at `IDX = 0`: from `SP_LOOP` with `PAD > 0` and
`0 < ROOM`, write `' '` at `BUF+0` and return to `SP_LOOP` with
`IDX = 1` and `PAD -= 1`. 46 steps. -/
theorem pad_one_iter_idx0 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hPlo : 0 < (s.mem.get 27).toNat)
    (hPhi : (s.mem.get 27).toNat < 32768)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s46 := runN s 46
    s46.pc = 1011 ∧
    s46.halted = false ∧
    s46.mem.get 0 = 0 ∧
    s46.mem.get 32 = 32 ∧
    s46.mem.get 29 = 1 ∧
    s46.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s46.mem.get a = s.mem.get a) := by
  intro s46
  have hIlt : (s.mem.get 29).toNat < (s.mem.get 28).toNat := by
    rw [hI]; simp; exact hRlo
  have hw := sp_loop_to_write_space (s := s) hpc hh hZ hONE hPlo hPhi hIlt hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1155 := hw.1
  have hs20h : s20.halted = false := hw.2.1
  have hs20Z : s20.mem.get 0 = 0 := hw.2.2.1
  have hs20R : s20.mem.get 2319 = 1 := hw.2.2.2.1
  have hs20P : s20.mem.get 27 = s.mem.get 27 := hw.2.2.2.2.1
  have hs20I : s20.mem.get 29 = 0 := hw.2.2.2.2.2.1.trans hI
  have hpres20 := hw.2.2.2.2.2.2.2
  have hONE20 : s20.mem.get 3 = 1 := (hpres20 3 (by decide) (by decide) (by decide)).trans hONE
  have hK20 : s20.mem.get 10 = 32 := (hpres20 10 (by decide) (by decide) (by decide)).trans hK32
  have g20 : ∀ k : Nat, 1155 ≤ k → k < 1575 →
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
  have hw2 := write_space_pad_idx0 (s := s20) hs20pc hs20h hs20Z hONE20 hK20 hs20I hs20R g20
  have hrun : s46 = runN s20 26 := runN_add_eq s 20 26 46 (by decide)
  have hs46pc : s46.pc = 1011 := by rw [hrun]; exact hw2.1
  have hs46h : s46.halted = false := by rw [hrun]; exact hw2.2.1
  have hs46Z : s46.mem.get 0 = 0 := by rw [hrun]; exact hw2.2.2.1
  have hs46B : s46.mem.get 32 = 32 := by rw [hrun]; exact hw2.2.2.2.1
  have hs46I : s46.mem.get 29 = 1 := by rw [hrun]; exact hw2.2.2.2.2.1
  have hs46P : s46.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun, hw2.2.2.2.2.2.1, hs20P]
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s46.mem.get a = s.mem.get a := by
    intro a ha32 ha29 ha27 ha18 ha30 haR ha0
    rw [hrun]
    exact (hw2.2.2.2.2.2.2 a ha32 ha29 ha27 ha18 ha30 ha0).trans
      (hpres20 a ha18 haR ha0)
  exact ⟨hs46pc, hs46h, hs46Z, hs46B, hs46I, hs46P, hpres⟩

/-- From `AFTER_PAD` with `SIGN ≠ 0` and `IDX = 0 < ROOM`: write `'-'` at
`BUF+0` and reach `EMIT_DIGS` with `IDX = 1`. 51 steps. -/
theorem after_pad_minus_to_emit_idx0 {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK45 : s.mem.get 9 = 45)
    (hI : s.mem.get 29 = 0)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s51 := runN s 51
    s51.pc = 1575 ∧
    s51.halted = false ∧
    s51.mem.get 0 = 0 ∧
    s51.mem.get 32 = 45 ∧
    s51.mem.get 29 = 1 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s51.mem.get a = s.mem.get a) := by
  intro s51
  have hIlt : (s.mem.get 29).toNat < (s.mem.get 28).toNat := by
    rw [hI]; simp; exact hRlo
  have hw := after_pad_to_write_minus (s := s) hpc hh hZ hONE hSlo hShi hIlt hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s23 := runN s 23
  have hs23pc : s23.pc = 1170 := hw.1
  have hs23h : s23.halted = false := hw.2.1
  have hs23Z : s23.mem.get 0 = 0 := hw.2.2.1
  have hs23R : s23.mem.get 2319 = 2 := hw.2.2.2.1
  have hs23I : s23.mem.get 29 = 0 := hw.2.2.2.2.2.1.trans hI
  have hpres23 := hw.2.2.2.2.2.2.2
  have hONE23 : s23.mem.get 3 = 1 := (hpres23 3 (by decide) (by decide) (by decide)).trans hONE
  have hK23 : s23.mem.get 9 = 45 := (hpres23 9 (by decide) (by decide) (by decide)).trans hK45
  have g23 : ∀ k : Nat, 1170 ≤ k → k < 1575 →
      s23.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres23 (UInt16.ofNat k) n18 nR n0).trans (hcode k (by omega) (by omega))
  have hw2 := write_minus_sign_idx0 (s := s23) hs23pc hs23h hs23Z hONE23 hK23 hs23I hs23R g23
  have hrun50 : runN s 50 = runN s23 27 := runN_add_eq s 23 27 50 (by decide)
  let s50 := runN s 50
  have hs50pc : s50.pc = 1152 := by have : s50 = runN s23 27 := hrun50; rw [this]; exact hw2.1
  have hs50h : s50.halted = false := by have : s50 = runN s23 27 := hrun50; rw [this]; exact hw2.2.1
  have hs50Z : s50.mem.get 0 = 0 := by have : s50 = runN s23 27 := hrun50; rw [this]; exact hw2.2.2.1
  have hs50B : s50.mem.get 32 = 45 := by have : s50 = runN s23 27 := hrun50; rw [this]; exact hw2.2.2.2.1
  have hs50I : s50.mem.get 29 = 1 := by have : s50 = runN s23 27 := hrun50; rw [this]; exact hw2.2.2.2.2.1
  have hpres50 : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s50.mem.get a = s.mem.get a := by
    intro a ha32 ha29 ha18 ha30 haR ha0
    have : s50 = runN s23 27 := hrun50
    rw [this]
    exact (hw2.2.2.2.2.2 a ha32 ha29 ha18 ha30 ha0).trans (hpres23 a ha18 haR ha0)
  have g50 : ∀ k : Nat, 1152 ≤ k → k < 1155 →
      s50.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    have nR : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres50 (UInt16.ofNat k) n32 n29 n18 n30 nR n0).trans
      (hcode k (by omega) (by omega))
  have hj := after_sign_to_emit (s := s50) hs50pc hs50h hs50Z g50
  have hrun : s51 = runN s50 1 := runN_add_eq s 50 1 51 (by decide)
  have hs51pc : s51.pc = 1575 := by rw [hrun]; exact hj.1
  have hs51h : s51.halted = false := by rw [hrun]; exact hj.2.1
  have hs51Z : s51.mem.get 0 = 0 := by rw [hrun]; exact hj.2.2.1
  have hs51B : s51.mem.get 32 = 45 := by
    rw [hrun]; exact (hj.2.2.2 32 (by decide)).trans hs50B
  have hs51I : s51.mem.get 29 = 1 := by
    rw [hrun]; exact (hj.2.2.2 29 (by decide)).trans hs50I
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s51.mem.get a = s.mem.get a := by
    intro a ha32 ha29 ha18 ha30 haR ha0
    rw [hrun]; exact (hj.2.2.2 a ha0).trans (hpres50 a ha32 ha29 ha18 ha30 haR ha0)
  exact ⟨hs51pc, hs51h, hs51Z, hs51B, hs51I, hpres⟩

end IntFmt
