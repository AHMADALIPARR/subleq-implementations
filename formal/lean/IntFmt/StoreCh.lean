/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

`AFTER_PAD` sign dispatch and the unrolled `STORE_CH` / `STi` / `STORED`
buffer-write table. Block lemmas, not end-to-end correctness.
-/

import IntFmt.PadLen
import IntFmt.DecChunksC

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000


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


private theorem cell1184 (off : Nat) (h : off < 16) :
    intfmtImage[1184 + off]! = decChunk074[off]! :=
  extract_chunk 1184 decChunk074 image_chunk074 off h (by decide)


private theorem cell1200 (off : Nat) (h : off < 16) :
    intfmtImage[1200 + off]! = decChunk075[off]! :=
  extract_chunk 1200 decChunk075 image_chunk075 off h (by decide)


private theorem cell1216 (off : Nat) (h : off < 16) :
    intfmtImage[1216 + off]! = decChunk076[off]! :=
  extract_chunk 1216 decChunk076 image_chunk076 off h (by decide)


private theorem cell1232 (off : Nat) (h : off < 16) :
    intfmtImage[1232 + off]! = decChunk077[off]! :=
  extract_chunk 1232 decChunk077 image_chunk077 off h (by decide)


private theorem cell1248 (off : Nat) (h : off < 16) :
    intfmtImage[1248 + off]! = decChunk078[off]! :=
  extract_chunk 1248 decChunk078 image_chunk078 off h (by decide)


private theorem cell1264 (off : Nat) (h : off < 16) :
    intfmtImage[1264 + off]! = decChunk079[off]! :=
  extract_chunk 1264 decChunk079 image_chunk079 off h (by decide)


private theorem cell1280 (off : Nat) (h : off < 16) :
    intfmtImage[1280 + off]! = decChunk080[off]! :=
  extract_chunk 1280 decChunk080 image_chunk080 off h (by decide)


private theorem cell1296 (off : Nat) (h : off < 16) :
    intfmtImage[1296 + off]! = decChunk081[off]! :=
  extract_chunk 1296 decChunk081 image_chunk081 off h (by decide)


private theorem cell1312 (off : Nat) (h : off < 16) :
    intfmtImage[1312 + off]! = decChunk082[off]! :=
  extract_chunk 1312 decChunk082 image_chunk082 off h (by decide)


private theorem cell1328 (off : Nat) (h : off < 16) :
    intfmtImage[1328 + off]! = decChunk083[off]! :=
  extract_chunk 1328 decChunk083 image_chunk083 off h (by decide)


private theorem cell1344 (off : Nat) (h : off < 16) :
    intfmtImage[1344 + off]! = decChunk084[off]! :=
  extract_chunk 1344 decChunk084 image_chunk084 off h (by decide)


private theorem cell1360 (off : Nat) (h : off < 16) :
    intfmtImage[1360 + off]! = decChunk085[off]! :=
  extract_chunk 1360 decChunk085 image_chunk085 off h (by decide)


private theorem cell1376 (off : Nat) (h : off < 16) :
    intfmtImage[1376 + off]! = decChunk086[off]! :=
  extract_chunk 1376 decChunk086 image_chunk086 off h (by decide)


private theorem cell1392 (off : Nat) (h : off < 16) :
    intfmtImage[1392 + off]! = decChunk087[off]! :=
  extract_chunk 1392 decChunk087 image_chunk087 off h (by decide)


private theorem cell1408 (off : Nat) (h : off < 16) :
    intfmtImage[1408 + off]! = decChunk088[off]! :=
  extract_chunk 1408 decChunk088 image_chunk088 off h (by decide)


private theorem cell1424 (off : Nat) (h : off < 16) :
    intfmtImage[1424 + off]! = decChunk089[off]! :=
  extract_chunk 1424 decChunk089 image_chunk089 off h (by decide)


private theorem cell1440 (off : Nat) (h : off < 16) :
    intfmtImage[1440 + off]! = decChunk090[off]! :=
  extract_chunk 1440 decChunk090 image_chunk090 off h (by decide)


private theorem cell1456 (off : Nat) (h : off < 16) :
    intfmtImage[1456 + off]! = decChunk091[off]! :=
  extract_chunk 1456 decChunk091 image_chunk091 off h (by decide)


private theorem cell1472 (off : Nat) (h : off < 16) :
    intfmtImage[1472 + off]! = decChunk092[off]! :=
  extract_chunk 1472 decChunk092 image_chunk092 off h (by decide)


private theorem cell1488 (off : Nat) (h : off < 16) :
    intfmtImage[1488 + off]! = decChunk093[off]! :=
  extract_chunk 1488 decChunk093 image_chunk093 off h (by decide)


private theorem cell1504 (off : Nat) (h : off < 16) :
    intfmtImage[1504 + off]! = decChunk094[off]! :=
  extract_chunk 1504 decChunk094 image_chunk094 off h (by decide)


private theorem cell1520 (off : Nat) (h : off < 16) :
    intfmtImage[1520 + off]! = decChunk095[off]! :=
  extract_chunk 1520 decChunk095 image_chunk095 off h (by decide)


private theorem cell1536 (off : Nat) (h : off < 16) :
    intfmtImage[1536 + off]! = decChunk096[off]! :=
  extract_chunk 1536 decChunk096 image_chunk096 off h (by decide)


private theorem cell1552 (off : Nat) (h : off < 16) :
    intfmtImage[1552 + off]! = decChunk097[off]! :=
  extract_chunk 1552 decChunk097 image_chunk097 off h (by decide)


private theorem cell1568 (off : Nat) (h : off < 16) :
    intfmtImage[1568 + off]! = decChunk098[off]! :=
  extract_chunk 1568 decChunk098 image_chunk098 off h (by decide)

/-- MOV SIGN T at AFTER_PAD (pc 1077). -/
theorem ap_mov_SIGN_T {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 1089 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1089 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 19 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 19 = s.mem.get 19 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1077 :=
    hpc.trans (rfl : (1077 : Word) = UInt16.ofNat 1077)
  have g (k : Nat) (h1 : 1077 ≤ k) (h2 : k < 1089) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1077 + off) :=
    word_pc_off 1077 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk067[5]! = 18 := rfl
    exact (g 1077 (by decide) (by decide)).trans ((cell1072 5 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk067[6]! = 18 := rfl
    exact (g 1078 (by decide) (by decide)).trans ((cell1072 6 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk067[7]! = 1080 := rfl
    have hv : (1080 : Word) = UInt16.ofNat 1080 := rfl
    exact (g 1079 (by decide) (by decide)).trans ((cell1072 7 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 19 := by
    rw [poff 3 (by decide)]
    have hval : decChunk067[8]! = 19 := rfl
    exact (g 1080 (by decide) (by decide)).trans ((cell1072 8 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk067[9]! = 0 := rfl
    exact (g 1081 (by decide) (by decide)).trans ((cell1072 9 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk067[10]! = 1083 := rfl
    have hv : (1083 : Word) = UInt16.ofNat 1083 := rfl
    exact (g 1082 (by decide) (by decide)).trans ((cell1072 10 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk067[11]! = 0 := rfl
    exact (g 1083 (by decide) (by decide)).trans ((cell1072 11 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk067[12]! = 18 := rfl
    exact (g 1084 (by decide) (by decide)).trans ((cell1072 12 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk067[13]! = 1086 := rfl
    have hv : (1086 : Word) = UInt16.ofNat 1086 := rfl
    exact (g 1085 (by decide) (by decide)).trans ((cell1072 13 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk067[14]! = 0 := rfl
    exact (g 1086 (by decide) (by decide)).trans ((cell1072 14 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk067[15]! = 0 := rfl
    exact (g 1087 (by decide) (by decide)).trans ((cell1072 15 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk068[0]! = 1089 := rfl
    have hv : (1089 : Word) = UInt16.ofNat 1089 := rfl
    exact (g 1088 (by decide) (by decide)).trans ((cell1088 0 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1077 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1077 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 19) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1089 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1089 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1089 = (1089 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JLEZ T AFTER_SIGN at pc 1089. -/
theorem ap_enc_jlez_1089 {s : Machine}
    (hpc : s.pc = 1089)
    (hcode : ∀ k : Nat, 1089 ≤ k → k < 1089+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1152 := by
  have hp : s.pc = UInt16.ofNat 1089 :=
    hpc.trans (rfl : (1089 : Word) = UInt16.ofNat 1089)
  have g (k : Nat) (h1 : 1089 ≤ k) (h2 : k < 1089+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk068[1]! = 0 := rfl
    exact (g 1089 (by decide) (by decide)).trans ((cell1088 1 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1090 : Word) := by simp [hpc]
    rw [this, (rfl : (1090 : Word) = UInt16.ofNat 1090)]
    have hval : decChunk068[2]! = 18 := rfl
    exact (g 1090 (by decide) (by decide)).trans ((cell1088 2 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1152 := by
    have : s.pc + 2 = (1091 : Word) := by simp [hpc]
    rw [this, (rfl : (1091 : Word) = UInt16.ofNat 1091)]
    have hval : decChunk068[3]! = 1152 := rfl
    exact (g 1091 (by decide) (by decide)).trans ((cell1088 3 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP EMIT_DIGS at AFTER_SIGN (pc 1152). -/
theorem ap_enc_jmp_1152 {s : Machine}
    (hpc : s.pc = 1152)
    (hcode : ∀ k : Nat, 1152 ≤ k → k < 1152+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1575 := by
  have hp : s.pc = UInt16.ofNat 1152 :=
    hpc.trans (rfl : (1152 : Word) = UInt16.ofNat 1152)
  have g (k : Nat) (h1 : 1152 ≤ k) (h2 : k < 1152+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk072[0]! = 0 := rfl
    exact (g 1152 (by decide) (by decide)).trans ((cell1152 0 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1153 : Word) := by simp [hpc]
    rw [this, (rfl : (1153 : Word) = UInt16.ofNat 1153)]
    have hval : decChunk072[1]! = 0 := rfl
    exact (g 1153 (by decide) (by decide)).trans ((cell1152 1 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1575 := by
    have : s.pc + 2 = (1154 : Word) := by simp [hpc]
    rw [this, (rfl : (1154 : Word) = UInt16.ofNat 1154)]
    have hval : decChunk072[2]! = 1575 := rfl
    exact (g 1154 (by decide) (by decide)).trans ((cell1152 2 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV K32 CH at WRITE_SPACE (pc 1155). -/
theorem ap_mov_K32_CH {s : Machine}
    (hpc : s.pc = 1155)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1155 ≤ k → k < 1167 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1167 ∧
    s4.halted = false ∧
    s4.mem.get 30 = s.mem.get 10 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 10 = s.mem.get 10 ∧
    (∀ a, a ≠ 30 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1155 :=
    hpc.trans (rfl : (1155 : Word) = UInt16.ofNat 1155)
  have g (k : Nat) (h1 : 1155 ≤ k) (h2 : k < 1167) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1155 + off) :=
    word_pc_off 1155 off hp (by omega)
  have m0 : s.mem.get s.pc = 30 := by
    rw [hp]
    have hval : decChunk072[3]! = 30 := rfl
    exact (g 1155 (by decide) (by decide)).trans ((cell1152 3 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 30 := by
    rw [poff 1 (by decide)]
    have hval : decChunk072[4]! = 30 := rfl
    exact (g 1156 (by decide) (by decide)).trans ((cell1152 4 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk072[5]! = 1158 := rfl
    have hv : (1158 : Word) = UInt16.ofNat 1158 := rfl
    exact (g 1157 (by decide) (by decide)).trans ((cell1152 5 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 10 := by
    rw [poff 3 (by decide)]
    have hval : decChunk072[6]! = 10 := rfl
    exact (g 1158 (by decide) (by decide)).trans ((cell1152 6 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk072[7]! = 0 := rfl
    exact (g 1159 (by decide) (by decide)).trans ((cell1152 7 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk072[8]! = 1161 := rfl
    have hv : (1161 : Word) = UInt16.ofNat 1161 := rfl
    exact (g 1160 (by decide) (by decide)).trans ((cell1152 8 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk072[9]! = 0 := rfl
    exact (g 1161 (by decide) (by decide)).trans ((cell1152 9 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 30 := by
    rw [poff 7 (by decide)]
    have hval : decChunk072[10]! = 30 := rfl
    exact (g 1162 (by decide) (by decide)).trans ((cell1152 10 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk072[11]! = 1164 := rfl
    have hv : (1164 : Word) = UInt16.ofNat 1164 := rfl
    exact (g 1163 (by decide) (by decide)).trans ((cell1152 11 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk072[12]! = 0 := rfl
    exact (g 1164 (by decide) (by decide)).trans ((cell1152 12 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk072[13]! = 0 := rfl
    exact (g 1165 (by decide) (by decide)).trans ((cell1152 13 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk072[14]! = 1167 := rfl
    have hv : (1167 : Word) = UInt16.ofNat 1167 := rfl
    exact (g 1166 (by decide) (by decide)).trans ((cell1152 14 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (30 : Word) := by
    intro i hi
    have : (30 : Word) = UInt16.ofNat 30 := rfl
    rw [this]
    exact pc_off_ne 1155 i 30 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1155 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 10) (dst := 30)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1167 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1167 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1167 = (1167 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORE_CH at pc 1167 (WRITE_SPACE). -/
theorem ap_enc_jmp_1167 {s : Machine}
    (hpc : s.pc = 1167)
    (hcode : ∀ k : Nat, 1167 ≤ k → k < 1167+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1185 := by
  have hp : s.pc = UInt16.ofNat 1167 :=
    hpc.trans (rfl : (1167 : Word) = UInt16.ofNat 1167)
  have g (k : Nat) (h1 : 1167 ≤ k) (h2 : k < 1167+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk072[15]! = 0 := rfl
    exact (g 1167 (by decide) (by decide)).trans ((cell1152 15 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1168 : Word) := by simp [hpc]
    rw [this, (rfl : (1168 : Word) = UInt16.ofNat 1168)]
    have hval : decChunk073[0]! = 0 := rfl
    exact (g 1168 (by decide) (by decide)).trans ((cell1168 0 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1185 := by
    have : s.pc + 2 = (1169 : Word) := by simp [hpc]
    rw [this, (rfl : (1169 : Word) = UInt16.ofNat 1169)]
    have hval : decChunk073[1]! = 1185 := rfl
    exact (g 1169 (by decide) (by decide)).trans ((cell1168 1 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV K45 CH at WRITE_MINUS (pc 1170). -/
theorem ap_mov_K45_CH {s : Machine}
    (hpc : s.pc = 1170)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1170 ≤ k → k < 1182 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1182 ∧
    s4.halted = false ∧
    s4.mem.get 30 = s.mem.get 9 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 9 = s.mem.get 9 ∧
    (∀ a, a ≠ 30 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1170 :=
    hpc.trans (rfl : (1170 : Word) = UInt16.ofNat 1170)
  have g (k : Nat) (h1 : 1170 ≤ k) (h2 : k < 1182) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1170 + off) :=
    word_pc_off 1170 off hp (by omega)
  have m0 : s.mem.get s.pc = 30 := by
    rw [hp]
    have hval : decChunk073[2]! = 30 := rfl
    exact (g 1170 (by decide) (by decide)).trans ((cell1168 2 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 30 := by
    rw [poff 1 (by decide)]
    have hval : decChunk073[3]! = 30 := rfl
    exact (g 1171 (by decide) (by decide)).trans ((cell1168 3 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk073[4]! = 1173 := rfl
    have hv : (1173 : Word) = UInt16.ofNat 1173 := rfl
    exact (g 1172 (by decide) (by decide)).trans ((cell1168 4 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 9 := by
    rw [poff 3 (by decide)]
    have hval : decChunk073[5]! = 9 := rfl
    exact (g 1173 (by decide) (by decide)).trans ((cell1168 5 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk073[6]! = 0 := rfl
    exact (g 1174 (by decide) (by decide)).trans ((cell1168 6 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk073[7]! = 1176 := rfl
    have hv : (1176 : Word) = UInt16.ofNat 1176 := rfl
    exact (g 1175 (by decide) (by decide)).trans ((cell1168 7 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk073[8]! = 0 := rfl
    exact (g 1176 (by decide) (by decide)).trans ((cell1168 8 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 30 := by
    rw [poff 7 (by decide)]
    have hval : decChunk073[9]! = 30 := rfl
    exact (g 1177 (by decide) (by decide)).trans ((cell1168 9 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk073[10]! = 1179 := rfl
    have hv : (1179 : Word) = UInt16.ofNat 1179 := rfl
    exact (g 1178 (by decide) (by decide)).trans ((cell1168 10 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk073[11]! = 0 := rfl
    exact (g 1179 (by decide) (by decide)).trans ((cell1168 11 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk073[12]! = 0 := rfl
    exact (g 1180 (by decide) (by decide)).trans ((cell1168 12 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk073[13]! = 1182 := rfl
    have hv : (1182 : Word) = UInt16.ofNat 1182 := rfl
    exact (g 1181 (by decide) (by decide)).trans ((cell1168 13 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (30 : Word) := by
    intro i hi
    have : (30 : Word) = UInt16.ofNat 30 := rfl
    rw [this]
    exact pc_off_ne 1170 i 30 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1170 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 9) (dst := 30)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1182 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1182 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1182 = (1182 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORE_CH at pc 1182 (WRITE_MINUS). -/
theorem ap_enc_jmp_1182 {s : Machine}
    (hpc : s.pc = 1182)
    (hcode : ∀ k : Nat, 1182 ≤ k → k < 1182+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1185 := by
  have hp : s.pc = UInt16.ofNat 1182 :=
    hpc.trans (rfl : (1182 : Word) = UInt16.ofNat 1182)
  have g (k : Nat) (h1 : 1182 ≤ k) (h2 : k < 1182+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk073[14]! = 0 := rfl
    exact (g 1182 (by decide) (by decide)).trans ((cell1168 14 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1183 : Word) := by simp [hpc]
    rw [this, (rfl : (1183 : Word) = UInt16.ofNat 1183)]
    have hval : decChunk073[15]! = 0 := rfl
    exact (g 1183 (by decide) (by decide)).trans ((cell1168 15 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1185 := by
    have : s.pc + 2 = (1184 : Word) := by simp [hpc]
    rw [this, (rfl : (1184 : Word) = UInt16.ofNat 1184)]
    have hval : decChunk074[0]! = 1185 := rfl
    exact (g 1184 (by decide) (by decide)).trans ((cell1184 0 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV IDX T at STORE_CH (pc 1185). -/
theorem sc_mov_IDX_T {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1197 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1197 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 29 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 29 = s.mem.get 29 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1185 :=
    hpc.trans (rfl : (1185 : Word) = UInt16.ofNat 1185)
  have g (k : Nat) (h1 : 1185 ≤ k) (h2 : k < 1197) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1185 + off) :=
    word_pc_off 1185 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk074[1]! = 18 := rfl
    exact (g 1185 (by decide) (by decide)).trans ((cell1184 1 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk074[2]! = 18 := rfl
    exact (g 1186 (by decide) (by decide)).trans ((cell1184 2 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk074[3]! = 1188 := rfl
    have hv : (1188 : Word) = UInt16.ofNat 1188 := rfl
    exact (g 1187 (by decide) (by decide)).trans ((cell1184 3 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 29 := by
    rw [poff 3 (by decide)]
    have hval : decChunk074[4]! = 29 := rfl
    exact (g 1188 (by decide) (by decide)).trans ((cell1184 4 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk074[5]! = 0 := rfl
    exact (g 1189 (by decide) (by decide)).trans ((cell1184 5 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk074[6]! = 1191 := rfl
    have hv : (1191 : Word) = UInt16.ofNat 1191 := rfl
    exact (g 1190 (by decide) (by decide)).trans ((cell1184 6 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk074[7]! = 0 := rfl
    exact (g 1191 (by decide) (by decide)).trans ((cell1184 7 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk074[8]! = 18 := rfl
    exact (g 1192 (by decide) (by decide)).trans ((cell1184 8 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk074[9]! = 1194 := rfl
    have hv : (1194 : Word) = UInt16.ofNat 1194 := rfl
    exact (g 1193 (by decide) (by decide)).trans ((cell1184 9 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk074[10]! = 0 := rfl
    exact (g 1194 (by decide) (by decide)).trans ((cell1184 10 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk074[11]! = 0 := rfl
    exact (g 1195 (by decide) (by decide)).trans ((cell1184 11 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk074[12]! = 1197 := rfl
    have hv : (1197 : Word) = UInt16.ofNat 1197 := rfl
    exact (g 1196 (by decide) (by decide)).trans ((cell1184 12 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1185 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1185 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 29) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1197 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1197 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1197 = (1197 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JLEZ T ST0 at pc 1197. -/
theorem sc_enc_jlez_1197 {s : Machine}
    (hpc : s.pc = 1197)
    (hcode : ∀ k : Nat, 1197 ≤ k → k < 1197+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1287 := by
  have hp : s.pc = UInt16.ofNat 1197 :=
    hpc.trans (rfl : (1197 : Word) = UInt16.ofNat 1197)
  have g (k : Nat) (h1 : 1197 ≤ k) (h2 : k < 1197+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk074[13]! = 0 := rfl
    exact (g 1197 (by decide) (by decide)).trans ((cell1184 13 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1198 : Word) := by simp [hpc]
    rw [this, (rfl : (1198 : Word) = UInt16.ofNat 1198)]
    have hval : decChunk074[14]! = 18 := rfl
    exact (g 1198 (by decide) (by decide)).trans ((cell1184 14 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1287 := by
    have : s.pc + 2 = (1199 : Word) := by simp [hpc]
    rw [this, (rfl : (1199 : Word) = UInt16.ofNat 1199)]
    have hval : decChunk074[15]! = 1287 := rfl
    exact (g 1199 (by decide) (by decide)).trans ((cell1184 15 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+0 at ST0 (pc 1287). -/
theorem sc_st0_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1287)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1287 ≤ k → k < 1299 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1299 ∧
    s4.halted = false ∧
    s4.mem.get 32 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 32 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1287 :=
    hpc.trans (rfl : (1287 : Word) = UInt16.ofNat 1287)
  have g (k : Nat) (h1 : 1287 ≤ k) (h2 : k < 1299) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1287 + off) :=
    word_pc_off 1287 off hp (by omega)
  have m0 : s.mem.get s.pc = 32 := by
    rw [hp]
    have hval : decChunk080[7]! = 32 := rfl
    exact (g 1287 (by decide) (by decide)).trans ((cell1280 7 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 32 := by
    rw [poff 1 (by decide)]
    have hval : decChunk080[8]! = 32 := rfl
    exact (g 1288 (by decide) (by decide)).trans ((cell1280 8 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk080[9]! = 1290 := rfl
    have hv : (1290 : Word) = UInt16.ofNat 1290 := rfl
    exact (g 1289 (by decide) (by decide)).trans ((cell1280 9 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk080[10]! = 30 := rfl
    exact (g 1290 (by decide) (by decide)).trans ((cell1280 10 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk080[11]! = 0 := rfl
    exact (g 1291 (by decide) (by decide)).trans ((cell1280 11 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk080[12]! = 1293 := rfl
    have hv : (1293 : Word) = UInt16.ofNat 1293 := rfl
    exact (g 1292 (by decide) (by decide)).trans ((cell1280 12 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk080[13]! = 0 := rfl
    exact (g 1293 (by decide) (by decide)).trans ((cell1280 13 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 32 := by
    rw [poff 7 (by decide)]
    have hval : decChunk080[14]! = 32 := rfl
    exact (g 1294 (by decide) (by decide)).trans ((cell1280 14 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk080[15]! = 1296 := rfl
    have hv : (1296 : Word) = UInt16.ofNat 1296 := rfl
    exact (g 1295 (by decide) (by decide)).trans ((cell1280 15 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk081[0]! = 0 := rfl
    exact (g 1296 (by decide) (by decide)).trans ((cell1296 0 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk081[1]! = 0 := rfl
    exact (g 1297 (by decide) (by decide)).trans ((cell1296 1 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk081[2]! = 1299 := rfl
    have hv : (1299 : Word) = UInt16.ofNat 1299 := rfl
    exact (g 1298 (by decide) (by decide)).trans ((cell1296 2 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (32 : Word) := by
    intro i hi
    have : (32 : Word) = UInt16.ofNat 32 := rfl
    rw [this]
    exact pc_off_ne 1287 i 32 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1287 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 32)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1299 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1299 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1299 = (1299 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST0 (pc 1299). -/
theorem sc_st0_jmp_stored {s : Machine}
    (hpc : s.pc = 1299)
    (hcode : ∀ k : Nat, 1299 ≤ k → k < 1299+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1299 :=
    hpc.trans (rfl : (1299 : Word) = UInt16.ofNat 1299)
  have g (k : Nat) (h1 : 1299 ≤ k) (h2 : k < 1299+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk081[3]! = 0 := rfl
    exact (g 1299 (by decide) (by decide)).trans ((cell1296 3 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1300 : Word) := by simp [hpc]
    rw [this, (rfl : (1300 : Word) = UInt16.ofNat 1300)]
    have hval : decChunk081[4]! = 0 := rfl
    exact (g 1300 (by decide) (by decide)).trans ((cell1296 4 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1301 : Word) := by simp [hpc]
    rw [this, (rfl : (1301 : Word) = UInt16.ofNat 1301)]
    have hval : decChunk081[5]! = 1527 := rfl
    exact (g 1301 (by decide) (by decide)).trans ((cell1296 5 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+1 at ST1 (pc 1302). -/
theorem sc_st1_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1302)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1302 ≤ k → k < 1314 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1314 ∧
    s4.halted = false ∧
    s4.mem.get 33 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 33 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1302 :=
    hpc.trans (rfl : (1302 : Word) = UInt16.ofNat 1302)
  have g (k : Nat) (h1 : 1302 ≤ k) (h2 : k < 1314) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1302 + off) :=
    word_pc_off 1302 off hp (by omega)
  have m0 : s.mem.get s.pc = 33 := by
    rw [hp]
    have hval : decChunk081[6]! = 33 := rfl
    exact (g 1302 (by decide) (by decide)).trans ((cell1296 6 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 33 := by
    rw [poff 1 (by decide)]
    have hval : decChunk081[7]! = 33 := rfl
    exact (g 1303 (by decide) (by decide)).trans ((cell1296 7 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk081[8]! = 1305 := rfl
    have hv : (1305 : Word) = UInt16.ofNat 1305 := rfl
    exact (g 1304 (by decide) (by decide)).trans ((cell1296 8 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk081[9]! = 30 := rfl
    exact (g 1305 (by decide) (by decide)).trans ((cell1296 9 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk081[10]! = 0 := rfl
    exact (g 1306 (by decide) (by decide)).trans ((cell1296 10 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk081[11]! = 1308 := rfl
    have hv : (1308 : Word) = UInt16.ofNat 1308 := rfl
    exact (g 1307 (by decide) (by decide)).trans ((cell1296 11 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk081[12]! = 0 := rfl
    exact (g 1308 (by decide) (by decide)).trans ((cell1296 12 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 33 := by
    rw [poff 7 (by decide)]
    have hval : decChunk081[13]! = 33 := rfl
    exact (g 1309 (by decide) (by decide)).trans ((cell1296 13 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk081[14]! = 1311 := rfl
    have hv : (1311 : Word) = UInt16.ofNat 1311 := rfl
    exact (g 1310 (by decide) (by decide)).trans ((cell1296 14 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk081[15]! = 0 := rfl
    exact (g 1311 (by decide) (by decide)).trans ((cell1296 15 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk082[0]! = 0 := rfl
    exact (g 1312 (by decide) (by decide)).trans ((cell1312 0 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk082[1]! = 1314 := rfl
    have hv : (1314 : Word) = UInt16.ofNat 1314 := rfl
    exact (g 1313 (by decide) (by decide)).trans ((cell1312 1 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (33 : Word) := by
    intro i hi
    have : (33 : Word) = UInt16.ofNat 33 := rfl
    rw [this]
    exact pc_off_ne 1302 i 33 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1302 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 33)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1314 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1314 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1314 = (1314 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST1 (pc 1314). -/
theorem sc_st1_jmp_stored {s : Machine}
    (hpc : s.pc = 1314)
    (hcode : ∀ k : Nat, 1314 ≤ k → k < 1314+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1314 :=
    hpc.trans (rfl : (1314 : Word) = UInt16.ofNat 1314)
  have g (k : Nat) (h1 : 1314 ≤ k) (h2 : k < 1314+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk082[2]! = 0 := rfl
    exact (g 1314 (by decide) (by decide)).trans ((cell1312 2 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1315 : Word) := by simp [hpc]
    rw [this, (rfl : (1315 : Word) = UInt16.ofNat 1315)]
    have hval : decChunk082[3]! = 0 := rfl
    exact (g 1315 (by decide) (by decide)).trans ((cell1312 3 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1316 : Word) := by simp [hpc]
    rw [this, (rfl : (1316 : Word) = UInt16.ofNat 1316)]
    have hval : decChunk082[4]! = 1527 := rfl
    exact (g 1316 (by decide) (by decide)).trans ((cell1312 4 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+2 at ST2 (pc 1317). -/
theorem sc_st2_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1317)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1317 ≤ k → k < 1329 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1329 ∧
    s4.halted = false ∧
    s4.mem.get 34 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 34 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1317 :=
    hpc.trans (rfl : (1317 : Word) = UInt16.ofNat 1317)
  have g (k : Nat) (h1 : 1317 ≤ k) (h2 : k < 1329) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1317 + off) :=
    word_pc_off 1317 off hp (by omega)
  have m0 : s.mem.get s.pc = 34 := by
    rw [hp]
    have hval : decChunk082[5]! = 34 := rfl
    exact (g 1317 (by decide) (by decide)).trans ((cell1312 5 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 34 := by
    rw [poff 1 (by decide)]
    have hval : decChunk082[6]! = 34 := rfl
    exact (g 1318 (by decide) (by decide)).trans ((cell1312 6 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk082[7]! = 1320 := rfl
    have hv : (1320 : Word) = UInt16.ofNat 1320 := rfl
    exact (g 1319 (by decide) (by decide)).trans ((cell1312 7 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk082[8]! = 30 := rfl
    exact (g 1320 (by decide) (by decide)).trans ((cell1312 8 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk082[9]! = 0 := rfl
    exact (g 1321 (by decide) (by decide)).trans ((cell1312 9 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk082[10]! = 1323 := rfl
    have hv : (1323 : Word) = UInt16.ofNat 1323 := rfl
    exact (g 1322 (by decide) (by decide)).trans ((cell1312 10 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk082[11]! = 0 := rfl
    exact (g 1323 (by decide) (by decide)).trans ((cell1312 11 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 34 := by
    rw [poff 7 (by decide)]
    have hval : decChunk082[12]! = 34 := rfl
    exact (g 1324 (by decide) (by decide)).trans ((cell1312 12 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk082[13]! = 1326 := rfl
    have hv : (1326 : Word) = UInt16.ofNat 1326 := rfl
    exact (g 1325 (by decide) (by decide)).trans ((cell1312 13 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk082[14]! = 0 := rfl
    exact (g 1326 (by decide) (by decide)).trans ((cell1312 14 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk082[15]! = 0 := rfl
    exact (g 1327 (by decide) (by decide)).trans ((cell1312 15 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk083[0]! = 1329 := rfl
    have hv : (1329 : Word) = UInt16.ofNat 1329 := rfl
    exact (g 1328 (by decide) (by decide)).trans ((cell1328 0 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (34 : Word) := by
    intro i hi
    have : (34 : Word) = UInt16.ofNat 34 := rfl
    rw [this]
    exact pc_off_ne 1317 i 34 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1317 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 34)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1329 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1329 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1329 = (1329 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST2 (pc 1329). -/
theorem sc_st2_jmp_stored {s : Machine}
    (hpc : s.pc = 1329)
    (hcode : ∀ k : Nat, 1329 ≤ k → k < 1329+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1329 :=
    hpc.trans (rfl : (1329 : Word) = UInt16.ofNat 1329)
  have g (k : Nat) (h1 : 1329 ≤ k) (h2 : k < 1329+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk083[1]! = 0 := rfl
    exact (g 1329 (by decide) (by decide)).trans ((cell1328 1 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1330 : Word) := by simp [hpc]
    rw [this, (rfl : (1330 : Word) = UInt16.ofNat 1330)]
    have hval : decChunk083[2]! = 0 := rfl
    exact (g 1330 (by decide) (by decide)).trans ((cell1328 2 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1331 : Word) := by simp [hpc]
    rw [this, (rfl : (1331 : Word) = UInt16.ofNat 1331)]
    have hval : decChunk083[3]! = 1527 := rfl
    exact (g 1331 (by decide) (by decide)).trans ((cell1328 3 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+3 at ST3 (pc 1332). -/
theorem sc_st3_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1332)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1332 ≤ k → k < 1344 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1344 ∧
    s4.halted = false ∧
    s4.mem.get 35 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 35 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1332 :=
    hpc.trans (rfl : (1332 : Word) = UInt16.ofNat 1332)
  have g (k : Nat) (h1 : 1332 ≤ k) (h2 : k < 1344) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1332 + off) :=
    word_pc_off 1332 off hp (by omega)
  have m0 : s.mem.get s.pc = 35 := by
    rw [hp]
    have hval : decChunk083[4]! = 35 := rfl
    exact (g 1332 (by decide) (by decide)).trans ((cell1328 4 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 35 := by
    rw [poff 1 (by decide)]
    have hval : decChunk083[5]! = 35 := rfl
    exact (g 1333 (by decide) (by decide)).trans ((cell1328 5 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk083[6]! = 1335 := rfl
    have hv : (1335 : Word) = UInt16.ofNat 1335 := rfl
    exact (g 1334 (by decide) (by decide)).trans ((cell1328 6 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk083[7]! = 30 := rfl
    exact (g 1335 (by decide) (by decide)).trans ((cell1328 7 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk083[8]! = 0 := rfl
    exact (g 1336 (by decide) (by decide)).trans ((cell1328 8 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk083[9]! = 1338 := rfl
    have hv : (1338 : Word) = UInt16.ofNat 1338 := rfl
    exact (g 1337 (by decide) (by decide)).trans ((cell1328 9 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk083[10]! = 0 := rfl
    exact (g 1338 (by decide) (by decide)).trans ((cell1328 10 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 35 := by
    rw [poff 7 (by decide)]
    have hval : decChunk083[11]! = 35 := rfl
    exact (g 1339 (by decide) (by decide)).trans ((cell1328 11 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk083[12]! = 1341 := rfl
    have hv : (1341 : Word) = UInt16.ofNat 1341 := rfl
    exact (g 1340 (by decide) (by decide)).trans ((cell1328 12 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk083[13]! = 0 := rfl
    exact (g 1341 (by decide) (by decide)).trans ((cell1328 13 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk083[14]! = 0 := rfl
    exact (g 1342 (by decide) (by decide)).trans ((cell1328 14 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk083[15]! = 1344 := rfl
    have hv : (1344 : Word) = UInt16.ofNat 1344 := rfl
    exact (g 1343 (by decide) (by decide)).trans ((cell1328 15 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (35 : Word) := by
    intro i hi
    have : (35 : Word) = UInt16.ofNat 35 := rfl
    rw [this]
    exact pc_off_ne 1332 i 35 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1332 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 35)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1344 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1344 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1344 = (1344 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST3 (pc 1344). -/
theorem sc_st3_jmp_stored {s : Machine}
    (hpc : s.pc = 1344)
    (hcode : ∀ k : Nat, 1344 ≤ k → k < 1344+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1344 :=
    hpc.trans (rfl : (1344 : Word) = UInt16.ofNat 1344)
  have g (k : Nat) (h1 : 1344 ≤ k) (h2 : k < 1344+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk084[0]! = 0 := rfl
    exact (g 1344 (by decide) (by decide)).trans ((cell1344 0 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1345 : Word) := by simp [hpc]
    rw [this, (rfl : (1345 : Word) = UInt16.ofNat 1345)]
    have hval : decChunk084[1]! = 0 := rfl
    exact (g 1345 (by decide) (by decide)).trans ((cell1344 1 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1346 : Word) := by simp [hpc]
    rw [this, (rfl : (1346 : Word) = UInt16.ofNat 1346)]
    have hval : decChunk084[2]! = 1527 := rfl
    exact (g 1346 (by decide) (by decide)).trans ((cell1344 2 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+4 at ST4 (pc 1347). -/
theorem sc_st4_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1347)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1347 ≤ k → k < 1359 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1359 ∧
    s4.halted = false ∧
    s4.mem.get 36 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 36 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1347 :=
    hpc.trans (rfl : (1347 : Word) = UInt16.ofNat 1347)
  have g (k : Nat) (h1 : 1347 ≤ k) (h2 : k < 1359) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1347 + off) :=
    word_pc_off 1347 off hp (by omega)
  have m0 : s.mem.get s.pc = 36 := by
    rw [hp]
    have hval : decChunk084[3]! = 36 := rfl
    exact (g 1347 (by decide) (by decide)).trans ((cell1344 3 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 36 := by
    rw [poff 1 (by decide)]
    have hval : decChunk084[4]! = 36 := rfl
    exact (g 1348 (by decide) (by decide)).trans ((cell1344 4 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk084[5]! = 1350 := rfl
    have hv : (1350 : Word) = UInt16.ofNat 1350 := rfl
    exact (g 1349 (by decide) (by decide)).trans ((cell1344 5 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk084[6]! = 30 := rfl
    exact (g 1350 (by decide) (by decide)).trans ((cell1344 6 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk084[7]! = 0 := rfl
    exact (g 1351 (by decide) (by decide)).trans ((cell1344 7 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk084[8]! = 1353 := rfl
    have hv : (1353 : Word) = UInt16.ofNat 1353 := rfl
    exact (g 1352 (by decide) (by decide)).trans ((cell1344 8 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk084[9]! = 0 := rfl
    exact (g 1353 (by decide) (by decide)).trans ((cell1344 9 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 36 := by
    rw [poff 7 (by decide)]
    have hval : decChunk084[10]! = 36 := rfl
    exact (g 1354 (by decide) (by decide)).trans ((cell1344 10 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk084[11]! = 1356 := rfl
    have hv : (1356 : Word) = UInt16.ofNat 1356 := rfl
    exact (g 1355 (by decide) (by decide)).trans ((cell1344 11 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk084[12]! = 0 := rfl
    exact (g 1356 (by decide) (by decide)).trans ((cell1344 12 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk084[13]! = 0 := rfl
    exact (g 1357 (by decide) (by decide)).trans ((cell1344 13 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk084[14]! = 1359 := rfl
    have hv : (1359 : Word) = UInt16.ofNat 1359 := rfl
    exact (g 1358 (by decide) (by decide)).trans ((cell1344 14 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (36 : Word) := by
    intro i hi
    have : (36 : Word) = UInt16.ofNat 36 := rfl
    rw [this]
    exact pc_off_ne 1347 i 36 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1347 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 36)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1359 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1359 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1359 = (1359 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST4 (pc 1359). -/
theorem sc_st4_jmp_stored {s : Machine}
    (hpc : s.pc = 1359)
    (hcode : ∀ k : Nat, 1359 ≤ k → k < 1359+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1359 :=
    hpc.trans (rfl : (1359 : Word) = UInt16.ofNat 1359)
  have g (k : Nat) (h1 : 1359 ≤ k) (h2 : k < 1359+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk084[15]! = 0 := rfl
    exact (g 1359 (by decide) (by decide)).trans ((cell1344 15 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1360 : Word) := by simp [hpc]
    rw [this, (rfl : (1360 : Word) = UInt16.ofNat 1360)]
    have hval : decChunk085[0]! = 0 := rfl
    exact (g 1360 (by decide) (by decide)).trans ((cell1360 0 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1361 : Word) := by simp [hpc]
    rw [this, (rfl : (1361 : Word) = UInt16.ofNat 1361)]
    have hval : decChunk085[1]! = 1527 := rfl
    exact (g 1361 (by decide) (by decide)).trans ((cell1360 1 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+5 at ST5 (pc 1362). -/
theorem sc_st5_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1362)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1362 ≤ k → k < 1374 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1374 ∧
    s4.halted = false ∧
    s4.mem.get 37 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 37 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1362 :=
    hpc.trans (rfl : (1362 : Word) = UInt16.ofNat 1362)
  have g (k : Nat) (h1 : 1362 ≤ k) (h2 : k < 1374) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1362 + off) :=
    word_pc_off 1362 off hp (by omega)
  have m0 : s.mem.get s.pc = 37 := by
    rw [hp]
    have hval : decChunk085[2]! = 37 := rfl
    exact (g 1362 (by decide) (by decide)).trans ((cell1360 2 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 37 := by
    rw [poff 1 (by decide)]
    have hval : decChunk085[3]! = 37 := rfl
    exact (g 1363 (by decide) (by decide)).trans ((cell1360 3 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk085[4]! = 1365 := rfl
    have hv : (1365 : Word) = UInt16.ofNat 1365 := rfl
    exact (g 1364 (by decide) (by decide)).trans ((cell1360 4 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk085[5]! = 30 := rfl
    exact (g 1365 (by decide) (by decide)).trans ((cell1360 5 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk085[6]! = 0 := rfl
    exact (g 1366 (by decide) (by decide)).trans ((cell1360 6 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk085[7]! = 1368 := rfl
    have hv : (1368 : Word) = UInt16.ofNat 1368 := rfl
    exact (g 1367 (by decide) (by decide)).trans ((cell1360 7 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk085[8]! = 0 := rfl
    exact (g 1368 (by decide) (by decide)).trans ((cell1360 8 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 37 := by
    rw [poff 7 (by decide)]
    have hval : decChunk085[9]! = 37 := rfl
    exact (g 1369 (by decide) (by decide)).trans ((cell1360 9 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk085[10]! = 1371 := rfl
    have hv : (1371 : Word) = UInt16.ofNat 1371 := rfl
    exact (g 1370 (by decide) (by decide)).trans ((cell1360 10 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk085[11]! = 0 := rfl
    exact (g 1371 (by decide) (by decide)).trans ((cell1360 11 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk085[12]! = 0 := rfl
    exact (g 1372 (by decide) (by decide)).trans ((cell1360 12 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk085[13]! = 1374 := rfl
    have hv : (1374 : Word) = UInt16.ofNat 1374 := rfl
    exact (g 1373 (by decide) (by decide)).trans ((cell1360 13 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (37 : Word) := by
    intro i hi
    have : (37 : Word) = UInt16.ofNat 37 := rfl
    rw [this]
    exact pc_off_ne 1362 i 37 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1362 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 37)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1374 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1374 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1374 = (1374 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST5 (pc 1374). -/
theorem sc_st5_jmp_stored {s : Machine}
    (hpc : s.pc = 1374)
    (hcode : ∀ k : Nat, 1374 ≤ k → k < 1374+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1374 :=
    hpc.trans (rfl : (1374 : Word) = UInt16.ofNat 1374)
  have g (k : Nat) (h1 : 1374 ≤ k) (h2 : k < 1374+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk085[14]! = 0 := rfl
    exact (g 1374 (by decide) (by decide)).trans ((cell1360 14 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1375 : Word) := by simp [hpc]
    rw [this, (rfl : (1375 : Word) = UInt16.ofNat 1375)]
    have hval : decChunk085[15]! = 0 := rfl
    exact (g 1375 (by decide) (by decide)).trans ((cell1360 15 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1376 : Word) := by simp [hpc]
    rw [this, (rfl : (1376 : Word) = UInt16.ofNat 1376)]
    have hval : decChunk086[0]! = 1527 := rfl
    exact (g 1376 (by decide) (by decide)).trans ((cell1376 0 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+6 at ST6 (pc 1377). -/
theorem sc_st6_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1377)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1377 ≤ k → k < 1389 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1389 ∧
    s4.halted = false ∧
    s4.mem.get 38 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 38 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1377 :=
    hpc.trans (rfl : (1377 : Word) = UInt16.ofNat 1377)
  have g (k : Nat) (h1 : 1377 ≤ k) (h2 : k < 1389) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1377 + off) :=
    word_pc_off 1377 off hp (by omega)
  have m0 : s.mem.get s.pc = 38 := by
    rw [hp]
    have hval : decChunk086[1]! = 38 := rfl
    exact (g 1377 (by decide) (by decide)).trans ((cell1376 1 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 38 := by
    rw [poff 1 (by decide)]
    have hval : decChunk086[2]! = 38 := rfl
    exact (g 1378 (by decide) (by decide)).trans ((cell1376 2 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk086[3]! = 1380 := rfl
    have hv : (1380 : Word) = UInt16.ofNat 1380 := rfl
    exact (g 1379 (by decide) (by decide)).trans ((cell1376 3 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk086[4]! = 30 := rfl
    exact (g 1380 (by decide) (by decide)).trans ((cell1376 4 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk086[5]! = 0 := rfl
    exact (g 1381 (by decide) (by decide)).trans ((cell1376 5 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk086[6]! = 1383 := rfl
    have hv : (1383 : Word) = UInt16.ofNat 1383 := rfl
    exact (g 1382 (by decide) (by decide)).trans ((cell1376 6 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk086[7]! = 0 := rfl
    exact (g 1383 (by decide) (by decide)).trans ((cell1376 7 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 38 := by
    rw [poff 7 (by decide)]
    have hval : decChunk086[8]! = 38 := rfl
    exact (g 1384 (by decide) (by decide)).trans ((cell1376 8 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk086[9]! = 1386 := rfl
    have hv : (1386 : Word) = UInt16.ofNat 1386 := rfl
    exact (g 1385 (by decide) (by decide)).trans ((cell1376 9 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk086[10]! = 0 := rfl
    exact (g 1386 (by decide) (by decide)).trans ((cell1376 10 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk086[11]! = 0 := rfl
    exact (g 1387 (by decide) (by decide)).trans ((cell1376 11 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk086[12]! = 1389 := rfl
    have hv : (1389 : Word) = UInt16.ofNat 1389 := rfl
    exact (g 1388 (by decide) (by decide)).trans ((cell1376 12 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (38 : Word) := by
    intro i hi
    have : (38 : Word) = UInt16.ofNat 38 := rfl
    rw [this]
    exact pc_off_ne 1377 i 38 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1377 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 38)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1389 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1389 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1389 = (1389 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST6 (pc 1389). -/
theorem sc_st6_jmp_stored {s : Machine}
    (hpc : s.pc = 1389)
    (hcode : ∀ k : Nat, 1389 ≤ k → k < 1389+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1389 :=
    hpc.trans (rfl : (1389 : Word) = UInt16.ofNat 1389)
  have g (k : Nat) (h1 : 1389 ≤ k) (h2 : k < 1389+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk086[13]! = 0 := rfl
    exact (g 1389 (by decide) (by decide)).trans ((cell1376 13 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1390 : Word) := by simp [hpc]
    rw [this, (rfl : (1390 : Word) = UInt16.ofNat 1390)]
    have hval : decChunk086[14]! = 0 := rfl
    exact (g 1390 (by decide) (by decide)).trans ((cell1376 14 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1391 : Word) := by simp [hpc]
    rw [this, (rfl : (1391 : Word) = UInt16.ofNat 1391)]
    have hval : decChunk086[15]! = 1527 := rfl
    exact (g 1391 (by decide) (by decide)).trans ((cell1376 15 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+7 at ST7 (pc 1392). -/
theorem sc_st7_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1392)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1392 ≤ k → k < 1404 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1404 ∧
    s4.halted = false ∧
    s4.mem.get 39 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 39 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1392 :=
    hpc.trans (rfl : (1392 : Word) = UInt16.ofNat 1392)
  have g (k : Nat) (h1 : 1392 ≤ k) (h2 : k < 1404) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1392 + off) :=
    word_pc_off 1392 off hp (by omega)
  have m0 : s.mem.get s.pc = 39 := by
    rw [hp]
    have hval : decChunk087[0]! = 39 := rfl
    exact (g 1392 (by decide) (by decide)).trans ((cell1392 0 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 39 := by
    rw [poff 1 (by decide)]
    have hval : decChunk087[1]! = 39 := rfl
    exact (g 1393 (by decide) (by decide)).trans ((cell1392 1 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk087[2]! = 1395 := rfl
    have hv : (1395 : Word) = UInt16.ofNat 1395 := rfl
    exact (g 1394 (by decide) (by decide)).trans ((cell1392 2 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk087[3]! = 30 := rfl
    exact (g 1395 (by decide) (by decide)).trans ((cell1392 3 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk087[4]! = 0 := rfl
    exact (g 1396 (by decide) (by decide)).trans ((cell1392 4 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk087[5]! = 1398 := rfl
    have hv : (1398 : Word) = UInt16.ofNat 1398 := rfl
    exact (g 1397 (by decide) (by decide)).trans ((cell1392 5 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk087[6]! = 0 := rfl
    exact (g 1398 (by decide) (by decide)).trans ((cell1392 6 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 39 := by
    rw [poff 7 (by decide)]
    have hval : decChunk087[7]! = 39 := rfl
    exact (g 1399 (by decide) (by decide)).trans ((cell1392 7 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk087[8]! = 1401 := rfl
    have hv : (1401 : Word) = UInt16.ofNat 1401 := rfl
    exact (g 1400 (by decide) (by decide)).trans ((cell1392 8 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk087[9]! = 0 := rfl
    exact (g 1401 (by decide) (by decide)).trans ((cell1392 9 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk087[10]! = 0 := rfl
    exact (g 1402 (by decide) (by decide)).trans ((cell1392 10 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk087[11]! = 1404 := rfl
    have hv : (1404 : Word) = UInt16.ofNat 1404 := rfl
    exact (g 1403 (by decide) (by decide)).trans ((cell1392 11 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (39 : Word) := by
    intro i hi
    have : (39 : Word) = UInt16.ofNat 39 := rfl
    rw [this]
    exact pc_off_ne 1392 i 39 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1392 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 39)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1404 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1404 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1404 = (1404 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST7 (pc 1404). -/
theorem sc_st7_jmp_stored {s : Machine}
    (hpc : s.pc = 1404)
    (hcode : ∀ k : Nat, 1404 ≤ k → k < 1404+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1404 :=
    hpc.trans (rfl : (1404 : Word) = UInt16.ofNat 1404)
  have g (k : Nat) (h1 : 1404 ≤ k) (h2 : k < 1404+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk087[12]! = 0 := rfl
    exact (g 1404 (by decide) (by decide)).trans ((cell1392 12 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1405 : Word) := by simp [hpc]
    rw [this, (rfl : (1405 : Word) = UInt16.ofNat 1405)]
    have hval : decChunk087[13]! = 0 := rfl
    exact (g 1405 (by decide) (by decide)).trans ((cell1392 13 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1406 : Word) := by simp [hpc]
    rw [this, (rfl : (1406 : Word) = UInt16.ofNat 1406)]
    have hval : decChunk087[14]! = 1527 := rfl
    exact (g 1406 (by decide) (by decide)).trans ((cell1392 14 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+8 at ST8 (pc 1407). -/
theorem sc_st8_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1407)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1407 ≤ k → k < 1419 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1419 ∧
    s4.halted = false ∧
    s4.mem.get 40 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 40 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1407 :=
    hpc.trans (rfl : (1407 : Word) = UInt16.ofNat 1407)
  have g (k : Nat) (h1 : 1407 ≤ k) (h2 : k < 1419) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1407 + off) :=
    word_pc_off 1407 off hp (by omega)
  have m0 : s.mem.get s.pc = 40 := by
    rw [hp]
    have hval : decChunk087[15]! = 40 := rfl
    exact (g 1407 (by decide) (by decide)).trans ((cell1392 15 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 40 := by
    rw [poff 1 (by decide)]
    have hval : decChunk088[0]! = 40 := rfl
    exact (g 1408 (by decide) (by decide)).trans ((cell1408 0 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk088[1]! = 1410 := rfl
    have hv : (1410 : Word) = UInt16.ofNat 1410 := rfl
    exact (g 1409 (by decide) (by decide)).trans ((cell1408 1 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk088[2]! = 30 := rfl
    exact (g 1410 (by decide) (by decide)).trans ((cell1408 2 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk088[3]! = 0 := rfl
    exact (g 1411 (by decide) (by decide)).trans ((cell1408 3 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk088[4]! = 1413 := rfl
    have hv : (1413 : Word) = UInt16.ofNat 1413 := rfl
    exact (g 1412 (by decide) (by decide)).trans ((cell1408 4 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk088[5]! = 0 := rfl
    exact (g 1413 (by decide) (by decide)).trans ((cell1408 5 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 40 := by
    rw [poff 7 (by decide)]
    have hval : decChunk088[6]! = 40 := rfl
    exact (g 1414 (by decide) (by decide)).trans ((cell1408 6 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk088[7]! = 1416 := rfl
    have hv : (1416 : Word) = UInt16.ofNat 1416 := rfl
    exact (g 1415 (by decide) (by decide)).trans ((cell1408 7 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk088[8]! = 0 := rfl
    exact (g 1416 (by decide) (by decide)).trans ((cell1408 8 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk088[9]! = 0 := rfl
    exact (g 1417 (by decide) (by decide)).trans ((cell1408 9 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk088[10]! = 1419 := rfl
    have hv : (1419 : Word) = UInt16.ofNat 1419 := rfl
    exact (g 1418 (by decide) (by decide)).trans ((cell1408 10 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (40 : Word) := by
    intro i hi
    have : (40 : Word) = UInt16.ofNat 40 := rfl
    rw [this]
    exact pc_off_ne 1407 i 40 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1407 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 40)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1419 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1419 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1419 = (1419 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST8 (pc 1419). -/
theorem sc_st8_jmp_stored {s : Machine}
    (hpc : s.pc = 1419)
    (hcode : ∀ k : Nat, 1419 ≤ k → k < 1419+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1419 :=
    hpc.trans (rfl : (1419 : Word) = UInt16.ofNat 1419)
  have g (k : Nat) (h1 : 1419 ≤ k) (h2 : k < 1419+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk088[11]! = 0 := rfl
    exact (g 1419 (by decide) (by decide)).trans ((cell1408 11 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1420 : Word) := by simp [hpc]
    rw [this, (rfl : (1420 : Word) = UInt16.ofNat 1420)]
    have hval : decChunk088[12]! = 0 := rfl
    exact (g 1420 (by decide) (by decide)).trans ((cell1408 12 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1421 : Word) := by simp [hpc]
    rw [this, (rfl : (1421 : Word) = UInt16.ofNat 1421)]
    have hval : decChunk088[13]! = 1527 := rfl
    exact (g 1421 (by decide) (by decide)).trans ((cell1408 13 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+9 at ST9 (pc 1422). -/
theorem sc_st9_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1422)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1422 ≤ k → k < 1434 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1434 ∧
    s4.halted = false ∧
    s4.mem.get 41 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 41 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1422 :=
    hpc.trans (rfl : (1422 : Word) = UInt16.ofNat 1422)
  have g (k : Nat) (h1 : 1422 ≤ k) (h2 : k < 1434) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1422 + off) :=
    word_pc_off 1422 off hp (by omega)
  have m0 : s.mem.get s.pc = 41 := by
    rw [hp]
    have hval : decChunk088[14]! = 41 := rfl
    exact (g 1422 (by decide) (by decide)).trans ((cell1408 14 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 41 := by
    rw [poff 1 (by decide)]
    have hval : decChunk088[15]! = 41 := rfl
    exact (g 1423 (by decide) (by decide)).trans ((cell1408 15 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk089[0]! = 1425 := rfl
    have hv : (1425 : Word) = UInt16.ofNat 1425 := rfl
    exact (g 1424 (by decide) (by decide)).trans ((cell1424 0 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk089[1]! = 30 := rfl
    exact (g 1425 (by decide) (by decide)).trans ((cell1424 1 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk089[2]! = 0 := rfl
    exact (g 1426 (by decide) (by decide)).trans ((cell1424 2 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk089[3]! = 1428 := rfl
    have hv : (1428 : Word) = UInt16.ofNat 1428 := rfl
    exact (g 1427 (by decide) (by decide)).trans ((cell1424 3 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk089[4]! = 0 := rfl
    exact (g 1428 (by decide) (by decide)).trans ((cell1424 4 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 41 := by
    rw [poff 7 (by decide)]
    have hval : decChunk089[5]! = 41 := rfl
    exact (g 1429 (by decide) (by decide)).trans ((cell1424 5 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk089[6]! = 1431 := rfl
    have hv : (1431 : Word) = UInt16.ofNat 1431 := rfl
    exact (g 1430 (by decide) (by decide)).trans ((cell1424 6 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk089[7]! = 0 := rfl
    exact (g 1431 (by decide) (by decide)).trans ((cell1424 7 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk089[8]! = 0 := rfl
    exact (g 1432 (by decide) (by decide)).trans ((cell1424 8 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk089[9]! = 1434 := rfl
    have hv : (1434 : Word) = UInt16.ofNat 1434 := rfl
    exact (g 1433 (by decide) (by decide)).trans ((cell1424 9 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (41 : Word) := by
    intro i hi
    have : (41 : Word) = UInt16.ofNat 41 := rfl
    rw [this]
    exact pc_off_ne 1422 i 41 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1422 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 41)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1434 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1434 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1434 = (1434 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST9 (pc 1434). -/
theorem sc_st9_jmp_stored {s : Machine}
    (hpc : s.pc = 1434)
    (hcode : ∀ k : Nat, 1434 ≤ k → k < 1434+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1434 :=
    hpc.trans (rfl : (1434 : Word) = UInt16.ofNat 1434)
  have g (k : Nat) (h1 : 1434 ≤ k) (h2 : k < 1434+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk089[10]! = 0 := rfl
    exact (g 1434 (by decide) (by decide)).trans ((cell1424 10 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1435 : Word) := by simp [hpc]
    rw [this, (rfl : (1435 : Word) = UInt16.ofNat 1435)]
    have hval : decChunk089[11]! = 0 := rfl
    exact (g 1435 (by decide) (by decide)).trans ((cell1424 11 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1436 : Word) := by simp [hpc]
    rw [this, (rfl : (1436 : Word) = UInt16.ofNat 1436)]
    have hval : decChunk089[12]! = 1527 := rfl
    exact (g 1436 (by decide) (by decide)).trans ((cell1424 12 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+10 at ST10 (pc 1437). -/
theorem sc_st10_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1437)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1437 ≤ k → k < 1449 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1449 ∧
    s4.halted = false ∧
    s4.mem.get 42 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 42 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1437 :=
    hpc.trans (rfl : (1437 : Word) = UInt16.ofNat 1437)
  have g (k : Nat) (h1 : 1437 ≤ k) (h2 : k < 1449) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1437 + off) :=
    word_pc_off 1437 off hp (by omega)
  have m0 : s.mem.get s.pc = 42 := by
    rw [hp]
    have hval : decChunk089[13]! = 42 := rfl
    exact (g 1437 (by decide) (by decide)).trans ((cell1424 13 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 42 := by
    rw [poff 1 (by decide)]
    have hval : decChunk089[14]! = 42 := rfl
    exact (g 1438 (by decide) (by decide)).trans ((cell1424 14 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk089[15]! = 1440 := rfl
    have hv : (1440 : Word) = UInt16.ofNat 1440 := rfl
    exact (g 1439 (by decide) (by decide)).trans ((cell1424 15 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk090[0]! = 30 := rfl
    exact (g 1440 (by decide) (by decide)).trans ((cell1440 0 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk090[1]! = 0 := rfl
    exact (g 1441 (by decide) (by decide)).trans ((cell1440 1 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk090[2]! = 1443 := rfl
    have hv : (1443 : Word) = UInt16.ofNat 1443 := rfl
    exact (g 1442 (by decide) (by decide)).trans ((cell1440 2 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk090[3]! = 0 := rfl
    exact (g 1443 (by decide) (by decide)).trans ((cell1440 3 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 42 := by
    rw [poff 7 (by decide)]
    have hval : decChunk090[4]! = 42 := rfl
    exact (g 1444 (by decide) (by decide)).trans ((cell1440 4 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk090[5]! = 1446 := rfl
    have hv : (1446 : Word) = UInt16.ofNat 1446 := rfl
    exact (g 1445 (by decide) (by decide)).trans ((cell1440 5 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk090[6]! = 0 := rfl
    exact (g 1446 (by decide) (by decide)).trans ((cell1440 6 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk090[7]! = 0 := rfl
    exact (g 1447 (by decide) (by decide)).trans ((cell1440 7 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk090[8]! = 1449 := rfl
    have hv : (1449 : Word) = UInt16.ofNat 1449 := rfl
    exact (g 1448 (by decide) (by decide)).trans ((cell1440 8 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (42 : Word) := by
    intro i hi
    have : (42 : Word) = UInt16.ofNat 42 := rfl
    rw [this]
    exact pc_off_ne 1437 i 42 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1437 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 42)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1449 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1449 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1449 = (1449 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST10 (pc 1449). -/
theorem sc_st10_jmp_stored {s : Machine}
    (hpc : s.pc = 1449)
    (hcode : ∀ k : Nat, 1449 ≤ k → k < 1449+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1449 :=
    hpc.trans (rfl : (1449 : Word) = UInt16.ofNat 1449)
  have g (k : Nat) (h1 : 1449 ≤ k) (h2 : k < 1449+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk090[9]! = 0 := rfl
    exact (g 1449 (by decide) (by decide)).trans ((cell1440 9 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1450 : Word) := by simp [hpc]
    rw [this, (rfl : (1450 : Word) = UInt16.ofNat 1450)]
    have hval : decChunk090[10]! = 0 := rfl
    exact (g 1450 (by decide) (by decide)).trans ((cell1440 10 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1451 : Word) := by simp [hpc]
    rw [this, (rfl : (1451 : Word) = UInt16.ofNat 1451)]
    have hval : decChunk090[11]! = 1527 := rfl
    exact (g 1451 (by decide) (by decide)).trans ((cell1440 11 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+11 at ST11 (pc 1452). -/
theorem sc_st11_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1452)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1452 ≤ k → k < 1464 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1464 ∧
    s4.halted = false ∧
    s4.mem.get 43 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 43 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1452 :=
    hpc.trans (rfl : (1452 : Word) = UInt16.ofNat 1452)
  have g (k : Nat) (h1 : 1452 ≤ k) (h2 : k < 1464) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1452 + off) :=
    word_pc_off 1452 off hp (by omega)
  have m0 : s.mem.get s.pc = 43 := by
    rw [hp]
    have hval : decChunk090[12]! = 43 := rfl
    exact (g 1452 (by decide) (by decide)).trans ((cell1440 12 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 43 := by
    rw [poff 1 (by decide)]
    have hval : decChunk090[13]! = 43 := rfl
    exact (g 1453 (by decide) (by decide)).trans ((cell1440 13 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk090[14]! = 1455 := rfl
    have hv : (1455 : Word) = UInt16.ofNat 1455 := rfl
    exact (g 1454 (by decide) (by decide)).trans ((cell1440 14 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk090[15]! = 30 := rfl
    exact (g 1455 (by decide) (by decide)).trans ((cell1440 15 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk091[0]! = 0 := rfl
    exact (g 1456 (by decide) (by decide)).trans ((cell1456 0 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk091[1]! = 1458 := rfl
    have hv : (1458 : Word) = UInt16.ofNat 1458 := rfl
    exact (g 1457 (by decide) (by decide)).trans ((cell1456 1 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk091[2]! = 0 := rfl
    exact (g 1458 (by decide) (by decide)).trans ((cell1456 2 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 43 := by
    rw [poff 7 (by decide)]
    have hval : decChunk091[3]! = 43 := rfl
    exact (g 1459 (by decide) (by decide)).trans ((cell1456 3 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk091[4]! = 1461 := rfl
    have hv : (1461 : Word) = UInt16.ofNat 1461 := rfl
    exact (g 1460 (by decide) (by decide)).trans ((cell1456 4 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk091[5]! = 0 := rfl
    exact (g 1461 (by decide) (by decide)).trans ((cell1456 5 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk091[6]! = 0 := rfl
    exact (g 1462 (by decide) (by decide)).trans ((cell1456 6 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk091[7]! = 1464 := rfl
    have hv : (1464 : Word) = UInt16.ofNat 1464 := rfl
    exact (g 1463 (by decide) (by decide)).trans ((cell1456 7 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (43 : Word) := by
    intro i hi
    have : (43 : Word) = UInt16.ofNat 43 := rfl
    rw [this]
    exact pc_off_ne 1452 i 43 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1452 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 43)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1464 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1464 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1464 = (1464 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST11 (pc 1464). -/
theorem sc_st11_jmp_stored {s : Machine}
    (hpc : s.pc = 1464)
    (hcode : ∀ k : Nat, 1464 ≤ k → k < 1464+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1464 :=
    hpc.trans (rfl : (1464 : Word) = UInt16.ofNat 1464)
  have g (k : Nat) (h1 : 1464 ≤ k) (h2 : k < 1464+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk091[8]! = 0 := rfl
    exact (g 1464 (by decide) (by decide)).trans ((cell1456 8 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1465 : Word) := by simp [hpc]
    rw [this, (rfl : (1465 : Word) = UInt16.ofNat 1465)]
    have hval : decChunk091[9]! = 0 := rfl
    exact (g 1465 (by decide) (by decide)).trans ((cell1456 9 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1466 : Word) := by simp [hpc]
    rw [this, (rfl : (1466 : Word) = UInt16.ofNat 1466)]
    have hval : decChunk091[10]! = 1527 := rfl
    exact (g 1466 (by decide) (by decide)).trans ((cell1456 10 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+12 at ST12 (pc 1467). -/
theorem sc_st12_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1467)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1467 ≤ k → k < 1479 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1479 ∧
    s4.halted = false ∧
    s4.mem.get 44 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 44 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1467 :=
    hpc.trans (rfl : (1467 : Word) = UInt16.ofNat 1467)
  have g (k : Nat) (h1 : 1467 ≤ k) (h2 : k < 1479) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1467 + off) :=
    word_pc_off 1467 off hp (by omega)
  have m0 : s.mem.get s.pc = 44 := by
    rw [hp]
    have hval : decChunk091[11]! = 44 := rfl
    exact (g 1467 (by decide) (by decide)).trans ((cell1456 11 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 44 := by
    rw [poff 1 (by decide)]
    have hval : decChunk091[12]! = 44 := rfl
    exact (g 1468 (by decide) (by decide)).trans ((cell1456 12 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk091[13]! = 1470 := rfl
    have hv : (1470 : Word) = UInt16.ofNat 1470 := rfl
    exact (g 1469 (by decide) (by decide)).trans ((cell1456 13 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk091[14]! = 30 := rfl
    exact (g 1470 (by decide) (by decide)).trans ((cell1456 14 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk091[15]! = 0 := rfl
    exact (g 1471 (by decide) (by decide)).trans ((cell1456 15 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk092[0]! = 1473 := rfl
    have hv : (1473 : Word) = UInt16.ofNat 1473 := rfl
    exact (g 1472 (by decide) (by decide)).trans ((cell1472 0 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk092[1]! = 0 := rfl
    exact (g 1473 (by decide) (by decide)).trans ((cell1472 1 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 44 := by
    rw [poff 7 (by decide)]
    have hval : decChunk092[2]! = 44 := rfl
    exact (g 1474 (by decide) (by decide)).trans ((cell1472 2 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk092[3]! = 1476 := rfl
    have hv : (1476 : Word) = UInt16.ofNat 1476 := rfl
    exact (g 1475 (by decide) (by decide)).trans ((cell1472 3 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk092[4]! = 0 := rfl
    exact (g 1476 (by decide) (by decide)).trans ((cell1472 4 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk092[5]! = 0 := rfl
    exact (g 1477 (by decide) (by decide)).trans ((cell1472 5 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk092[6]! = 1479 := rfl
    have hv : (1479 : Word) = UInt16.ofNat 1479 := rfl
    exact (g 1478 (by decide) (by decide)).trans ((cell1472 6 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (44 : Word) := by
    intro i hi
    have : (44 : Word) = UInt16.ofNat 44 := rfl
    rw [this]
    exact pc_off_ne 1467 i 44 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1467 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 44)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1479 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1479 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1479 = (1479 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST12 (pc 1479). -/
theorem sc_st12_jmp_stored {s : Machine}
    (hpc : s.pc = 1479)
    (hcode : ∀ k : Nat, 1479 ≤ k → k < 1479+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1479 :=
    hpc.trans (rfl : (1479 : Word) = UInt16.ofNat 1479)
  have g (k : Nat) (h1 : 1479 ≤ k) (h2 : k < 1479+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk092[7]! = 0 := rfl
    exact (g 1479 (by decide) (by decide)).trans ((cell1472 7 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1480 : Word) := by simp [hpc]
    rw [this, (rfl : (1480 : Word) = UInt16.ofNat 1480)]
    have hval : decChunk092[8]! = 0 := rfl
    exact (g 1480 (by decide) (by decide)).trans ((cell1472 8 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1481 : Word) := by simp [hpc]
    rw [this, (rfl : (1481 : Word) = UInt16.ofNat 1481)]
    have hval : decChunk092[9]! = 1527 := rfl
    exact (g 1481 (by decide) (by decide)).trans ((cell1472 9 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+13 at ST13 (pc 1482). -/
theorem sc_st13_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1482)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1482 ≤ k → k < 1494 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1494 ∧
    s4.halted = false ∧
    s4.mem.get 45 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 45 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1482 :=
    hpc.trans (rfl : (1482 : Word) = UInt16.ofNat 1482)
  have g (k : Nat) (h1 : 1482 ≤ k) (h2 : k < 1494) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1482 + off) :=
    word_pc_off 1482 off hp (by omega)
  have m0 : s.mem.get s.pc = 45 := by
    rw [hp]
    have hval : decChunk092[10]! = 45 := rfl
    exact (g 1482 (by decide) (by decide)).trans ((cell1472 10 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 45 := by
    rw [poff 1 (by decide)]
    have hval : decChunk092[11]! = 45 := rfl
    exact (g 1483 (by decide) (by decide)).trans ((cell1472 11 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk092[12]! = 1485 := rfl
    have hv : (1485 : Word) = UInt16.ofNat 1485 := rfl
    exact (g 1484 (by decide) (by decide)).trans ((cell1472 12 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk092[13]! = 30 := rfl
    exact (g 1485 (by decide) (by decide)).trans ((cell1472 13 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk092[14]! = 0 := rfl
    exact (g 1486 (by decide) (by decide)).trans ((cell1472 14 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk092[15]! = 1488 := rfl
    have hv : (1488 : Word) = UInt16.ofNat 1488 := rfl
    exact (g 1487 (by decide) (by decide)).trans ((cell1472 15 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk093[0]! = 0 := rfl
    exact (g 1488 (by decide) (by decide)).trans ((cell1488 0 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 45 := by
    rw [poff 7 (by decide)]
    have hval : decChunk093[1]! = 45 := rfl
    exact (g 1489 (by decide) (by decide)).trans ((cell1488 1 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk093[2]! = 1491 := rfl
    have hv : (1491 : Word) = UInt16.ofNat 1491 := rfl
    exact (g 1490 (by decide) (by decide)).trans ((cell1488 2 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk093[3]! = 0 := rfl
    exact (g 1491 (by decide) (by decide)).trans ((cell1488 3 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk093[4]! = 0 := rfl
    exact (g 1492 (by decide) (by decide)).trans ((cell1488 4 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk093[5]! = 1494 := rfl
    have hv : (1494 : Word) = UInt16.ofNat 1494 := rfl
    exact (g 1493 (by decide) (by decide)).trans ((cell1488 5 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (45 : Word) := by
    intro i hi
    have : (45 : Word) = UInt16.ofNat 45 := rfl
    rw [this]
    exact pc_off_ne 1482 i 45 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1482 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 45)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1494 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1494 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1494 = (1494 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST13 (pc 1494). -/
theorem sc_st13_jmp_stored {s : Machine}
    (hpc : s.pc = 1494)
    (hcode : ∀ k : Nat, 1494 ≤ k → k < 1494+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1494 :=
    hpc.trans (rfl : (1494 : Word) = UInt16.ofNat 1494)
  have g (k : Nat) (h1 : 1494 ≤ k) (h2 : k < 1494+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk093[6]! = 0 := rfl
    exact (g 1494 (by decide) (by decide)).trans ((cell1488 6 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1495 : Word) := by simp [hpc]
    rw [this, (rfl : (1495 : Word) = UInt16.ofNat 1495)]
    have hval : decChunk093[7]! = 0 := rfl
    exact (g 1495 (by decide) (by decide)).trans ((cell1488 7 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1496 : Word) := by simp [hpc]
    rw [this, (rfl : (1496 : Word) = UInt16.ofNat 1496)]
    have hval : decChunk093[8]! = 1527 := rfl
    exact (g 1496 (by decide) (by decide)).trans ((cell1488 8 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+14 at ST14 (pc 1497). -/
theorem sc_st14_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1497)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1497 ≤ k → k < 1509 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1509 ∧
    s4.halted = false ∧
    s4.mem.get 46 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 46 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1497 :=
    hpc.trans (rfl : (1497 : Word) = UInt16.ofNat 1497)
  have g (k : Nat) (h1 : 1497 ≤ k) (h2 : k < 1509) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1497 + off) :=
    word_pc_off 1497 off hp (by omega)
  have m0 : s.mem.get s.pc = 46 := by
    rw [hp]
    have hval : decChunk093[9]! = 46 := rfl
    exact (g 1497 (by decide) (by decide)).trans ((cell1488 9 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 46 := by
    rw [poff 1 (by decide)]
    have hval : decChunk093[10]! = 46 := rfl
    exact (g 1498 (by decide) (by decide)).trans ((cell1488 10 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk093[11]! = 1500 := rfl
    have hv : (1500 : Word) = UInt16.ofNat 1500 := rfl
    exact (g 1499 (by decide) (by decide)).trans ((cell1488 11 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk093[12]! = 30 := rfl
    exact (g 1500 (by decide) (by decide)).trans ((cell1488 12 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk093[13]! = 0 := rfl
    exact (g 1501 (by decide) (by decide)).trans ((cell1488 13 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk093[14]! = 1503 := rfl
    have hv : (1503 : Word) = UInt16.ofNat 1503 := rfl
    exact (g 1502 (by decide) (by decide)).trans ((cell1488 14 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk093[15]! = 0 := rfl
    exact (g 1503 (by decide) (by decide)).trans ((cell1488 15 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 46 := by
    rw [poff 7 (by decide)]
    have hval : decChunk094[0]! = 46 := rfl
    exact (g 1504 (by decide) (by decide)).trans ((cell1504 0 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk094[1]! = 1506 := rfl
    have hv : (1506 : Word) = UInt16.ofNat 1506 := rfl
    exact (g 1505 (by decide) (by decide)).trans ((cell1504 1 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk094[2]! = 0 := rfl
    exact (g 1506 (by decide) (by decide)).trans ((cell1504 2 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk094[3]! = 0 := rfl
    exact (g 1507 (by decide) (by decide)).trans ((cell1504 3 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk094[4]! = 1509 := rfl
    have hv : (1509 : Word) = UInt16.ofNat 1509 := rfl
    exact (g 1508 (by decide) (by decide)).trans ((cell1504 4 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (46 : Word) := by
    intro i hi
    have : (46 : Word) = UInt16.ofNat 46 := rfl
    rw [this]
    exact pc_off_ne 1497 i 46 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1497 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 46)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1509 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1509 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1509 = (1509 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST14 (pc 1509). -/
theorem sc_st14_jmp_stored {s : Machine}
    (hpc : s.pc = 1509)
    (hcode : ∀ k : Nat, 1509 ≤ k → k < 1509+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1509 :=
    hpc.trans (rfl : (1509 : Word) = UInt16.ofNat 1509)
  have g (k : Nat) (h1 : 1509 ≤ k) (h2 : k < 1509+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk094[5]! = 0 := rfl
    exact (g 1509 (by decide) (by decide)).trans ((cell1504 5 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1510 : Word) := by simp [hpc]
    rw [this, (rfl : (1510 : Word) = UInt16.ofNat 1510)]
    have hval : decChunk094[6]! = 0 := rfl
    exact (g 1510 (by decide) (by decide)).trans ((cell1504 6 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1511 : Word) := by simp [hpc]
    rw [this, (rfl : (1511 : Word) = UInt16.ofNat 1511)]
    have hval : decChunk094[7]! = 1527 := rfl
    exact (g 1511 (by decide) (by decide)).trans ((cell1504 7 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- MOV CH BUF+15 at ST15 (pc 1512). -/
theorem sc_st15_mov_CH_BUF {s : Machine}
    (hpc : s.pc = 1512)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1512 ≤ k → k < 1524 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1524 ∧
    s4.halted = false ∧
    s4.mem.get 47 = s.mem.get 30 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 30 = s.mem.get 30 ∧
    (∀ a, a ≠ 47 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1512 :=
    hpc.trans (rfl : (1512 : Word) = UInt16.ofNat 1512)
  have g (k : Nat) (h1 : 1512 ≤ k) (h2 : k < 1524) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1512 + off) :=
    word_pc_off 1512 off hp (by omega)
  have m0 : s.mem.get s.pc = 47 := by
    rw [hp]
    have hval : decChunk094[8]! = 47 := rfl
    exact (g 1512 (by decide) (by decide)).trans ((cell1504 8 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 47 := by
    rw [poff 1 (by decide)]
    have hval : decChunk094[9]! = 47 := rfl
    exact (g 1513 (by decide) (by decide)).trans ((cell1504 9 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk094[10]! = 1515 := rfl
    have hv : (1515 : Word) = UInt16.ofNat 1515 := rfl
    exact (g 1514 (by decide) (by decide)).trans ((cell1504 10 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 30 := by
    rw [poff 3 (by decide)]
    have hval : decChunk094[11]! = 30 := rfl
    exact (g 1515 (by decide) (by decide)).trans ((cell1504 11 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk094[12]! = 0 := rfl
    exact (g 1516 (by decide) (by decide)).trans ((cell1504 12 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk094[13]! = 1518 := rfl
    have hv : (1518 : Word) = UInt16.ofNat 1518 := rfl
    exact (g 1517 (by decide) (by decide)).trans ((cell1504 13 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk094[14]! = 0 := rfl
    exact (g 1518 (by decide) (by decide)).trans ((cell1504 14 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 47 := by
    rw [poff 7 (by decide)]
    have hval : decChunk094[15]! = 47 := rfl
    exact (g 1519 (by decide) (by decide)).trans ((cell1504 15 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk095[0]! = 1521 := rfl
    have hv : (1521 : Word) = UInt16.ofNat 1521 := rfl
    exact (g 1520 (by decide) (by decide)).trans ((cell1520 0 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk095[1]! = 0 := rfl
    exact (g 1521 (by decide) (by decide)).trans ((cell1520 1 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk095[2]! = 0 := rfl
    exact (g 1522 (by decide) (by decide)).trans ((cell1520 2 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk095[3]! = 1524 := rfl
    have hv : (1524 : Word) = UInt16.ofNat 1524 := rfl
    exact (g 1523 (by decide) (by decide)).trans ((cell1520 3 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (47 : Word) := by
    intro i hi
    have : (47 : Word) = UInt16.ofNat 47 := rfl
    rw [this]
    exact pc_off_ne 1512 i 47 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1512 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 30) (dst := 47)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1524 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1524 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1524 = (1524 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- JMP STORED at ST15 (pc 1524). -/
theorem sc_st15_jmp_stored {s : Machine}
    (hpc : s.pc = 1524)
    (hcode : ∀ k : Nat, 1524 ≤ k → k < 1524+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1527 := by
  have hp : s.pc = UInt16.ofNat 1524 :=
    hpc.trans (rfl : (1524 : Word) = UInt16.ofNat 1524)
  have g (k : Nat) (h1 : 1524 ≤ k) (h2 : k < 1524+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk095[4]! = 0 := rfl
    exact (g 1524 (by decide) (by decide)).trans ((cell1520 4 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1525 : Word) := by simp [hpc]
    rw [this, (rfl : (1525 : Word) = UInt16.ofNat 1525)]
    have hval : decChunk095[5]! = 0 := rfl
    exact (g 1525 (by decide) (by decide)).trans ((cell1520 5 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1527 := by
    have : s.pc + 2 = (1526 : Word) := by simp [hpc]
    rw [this, (rfl : (1526 : Word) = UInt16.ofNat 1526)]
    have hval : decChunk095[6]! = 1527 := rfl
    exact (g 1526 (by decide) (by decide)).trans ((cell1520 6 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- INC IDX at STORED (pc 1527). -/
theorem sc_inc_IDX {s : Machine}
    (hpc : s.pc = 1527)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcode : ∀ k : Nat, 1527 ≤ k → k < 1536 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = 1536 ∧
    s3.halted = false ∧
    s3.mem.get 29 = s.mem.get 29 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 29 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hp : s.pc = UInt16.ofNat 1527 :=
    hpc.trans (rfl : (1527 : Word) = UInt16.ofNat 1527)
  have g (k : Nat) (h1 : 1527 ≤ k) (h2 : k < 1536) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1527 + off) :=
    word_pc_off 1527 off hp (by omega)
  have i0 : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk095[7]! = 3 := rfl
    exact (g 1527 (by decide) (by decide)).trans ((cell1520 7 (by decide)).trans hval)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have hval : decChunk095[8]! = 0 := rfl
    exact (g 1528 (by decide) (by decide)).trans ((cell1520 8 (by decide)).trans hval)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk095[9]! = 1530 := rfl
    have hv : (1530 : Word) = UInt16.ofNat 1530 := rfl
    exact (g 1529 (by decide) (by decide)).trans ((cell1520 9 (by decide)).trans (hval.trans hv))
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have hval : decChunk095[10]! = 0 := rfl
    exact (g 1530 (by decide) (by decide)).trans ((cell1520 10 (by decide)).trans hval)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 29 := by
    rw [poff 4 (by decide)]
    have hval : decChunk095[11]! = 29 := rfl
    exact (g 1531 (by decide) (by decide)).trans ((cell1520 11 (by decide)).trans hval)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk095[12]! = 1533 := rfl
    have hv : (1533 : Word) = UInt16.ofNat 1533 := rfl
    exact (g 1532 (by decide) (by decide)).trans ((cell1520 12 (by decide)).trans (hval.trans hv))
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk095[13]! = 0 := rfl
    exact (g 1533 (by decide) (by decide)).trans ((cell1520 13 (by decide)).trans hval)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have hval : decChunk095[14]! = 0 := rfl
    exact (g 1534 (by decide) (by decide)).trans ((cell1520 14 (by decide)).trans hval)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk095[15]! = 1536 := rfl
    have hv : (1536 : Word) = UInt16.ofNat 1536 := rfl
    exact (g 1535 (by decide) (by decide)).trans ((cell1520 15 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (29 : Word) := by
    intro i hi
    have : (29 : Word) = UInt16.ofNat 29 := rfl
    rw [this]
    exact pc_off_ne 1527 i 29 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1527 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 29)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = 1536 := by
    have hadd : s.pc + UInt16.ofNat 9 =
        (1536 : Word) := by
      rw [poff 9 (by decide)]
      exact (rfl : UInt16.ofNat 1536 = (1536 : Word))
    exact hinc.1.trans hadd
  have hQ : s3.mem.get 29 = s.mem.get 29 + 1 := by
    have : s.mem.get 29 + s.mem.get 3 = s.mem.get 29 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hQ, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- MOV RETID T at pc 1536 (STORED). -/
theorem sc_mov_RETID_T {s : Machine}
    (hpc : s.pc = 1536)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1536 ≤ k → k < 1548 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = 1548 ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 2319 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 2319 = s.mem.get 2319 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hp : s.pc = UInt16.ofNat 1536 :=
    hpc.trans (rfl : (1536 : Word) = UInt16.ofNat 1536)
  have g (k : Nat) (h1 : 1536 ≤ k) (h2 : k < 1548) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (1536 + off) :=
    word_pc_off 1536 off hp (by omega)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk096[0]! = 18 := rfl
    exact (g 1536 (by decide) (by decide)).trans ((cell1536 0 (by decide)).trans hval)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk096[1]! = 18 := rfl
    exact (g 1537 (by decide) (by decide)).trans ((cell1536 1 (by decide)).trans hval)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk096[2]! = 1539 := rfl
    have hv : (1539 : Word) = UInt16.ofNat 1539 := rfl
    exact (g 1538 (by decide) (by decide)).trans ((cell1536 2 (by decide)).trans (hval.trans hv))
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 2319 := by
    rw [poff 3 (by decide)]
    have hval : decChunk096[3]! = 2319 := rfl
    exact (g 1539 (by decide) (by decide)).trans ((cell1536 3 (by decide)).trans hval)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk096[4]! = 0 := rfl
    exact (g 1540 (by decide) (by decide)).trans ((cell1536 4 (by decide)).trans hval)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk096[5]! = 1542 := rfl
    have hv : (1542 : Word) = UInt16.ofNat 1542 := rfl
    exact (g 1541 (by decide) (by decide)).trans ((cell1536 5 (by decide)).trans (hval.trans hv))
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk096[6]! = 0 := rfl
    exact (g 1542 (by decide) (by decide)).trans ((cell1536 6 (by decide)).trans hval)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk096[7]! = 18 := rfl
    exact (g 1543 (by decide) (by decide)).trans ((cell1536 7 (by decide)).trans hval)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk096[8]! = 1545 := rfl
    have hv : (1545 : Word) = UInt16.ofNat 1545 := rfl
    exact (g 1544 (by decide) (by decide)).trans ((cell1536 8 (by decide)).trans (hval.trans hv))
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk096[9]! = 0 := rfl
    exact (g 1545 (by decide) (by decide)).trans ((cell1536 9 (by decide)).trans hval)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk096[10]! = 0 := rfl
    exact (g 1546 (by decide) (by decide)).trans ((cell1536 10 (by decide)).trans hval)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk096[11]! = 1548 := rfl
    have hv : (1548 : Word) = UInt16.ofNat 1548 := rfl
    exact (g 1547 (by decide) (by decide)).trans ((cell1536 11 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 1536 i 18 hp (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 1536 i 0 hp (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by simp [hpc]
  have hpcM0 : 0 < s.pc.toNat := by simp [hpc]
  have hmov :=
    runN_MOV (s := s) (src := 2319) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = 1548 := by
    have hadd : s.pc + UInt16.ofNat 12 =
        (1548 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 1548 = (1548 : Word))
    exact hmov.1.trans hadd
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩

/-- DEC T at pc 1548 (STORED, RETID test). -/
theorem sc_dec_T_1548 {s : Machine}
    (hpc : s.pc = 1548)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1548 ≤ k → k < 1551 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1551 } := by
  have hp : s.pc = UInt16.ofNat 1548 :=
    hpc.trans (rfl : (1548 : Word) = UInt16.ofNat 1548)
  have g (k : Nat) (h1 : 1548 ≤ k) (h2 : k < 1551) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk096[12]! = 3 := rfl
    exact (g 1548 (by decide) (by decide)).trans ((cell1536 12 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1549 : Word) := by simp [hpc]
    rw [this, (rfl : (1549 : Word) = UInt16.ofNat 1549)]
    have hval : decChunk096[13]! = 18 := rfl
    exact (g 1549 (by decide) (by decide)).trans ((cell1536 13 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1550 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1551 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1550 : Word) = UInt16.ofNat 1550)]
    have hval : decChunk096[14]! = 1551 := rfl
    have hv : (1551 : Word) = UInt16.ofNat 1551 := rfl
    exact (g 1550 (by decide) (by decide)).trans ((cell1536 14 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1551 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T RET_PAD at pc 1551. -/
theorem sc_enc_jlez_1551 {s : Machine}
    (hpc : s.pc = 1551)
    (hcode : ∀ k : Nat, 1551 ≤ k → k < 1551+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1563 := by
  have hp : s.pc = UInt16.ofNat 1551 :=
    hpc.trans (rfl : (1551 : Word) = UInt16.ofNat 1551)
  have g (k : Nat) (h1 : 1551 ≤ k) (h2 : k < 1551+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk096[15]! = 0 := rfl
    exact (g 1551 (by decide) (by decide)).trans ((cell1536 15 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1552 : Word) := by simp [hpc]
    rw [this, (rfl : (1552 : Word) = UInt16.ofNat 1552)]
    have hval : decChunk097[0]! = 18 := rfl
    exact (g 1552 (by decide) (by decide)).trans ((cell1552 0 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1563 := by
    have : s.pc + 2 = (1553 : Word) := by simp [hpc]
    rw [this, (rfl : (1553 : Word) = UInt16.ofNat 1553)]
    have hval : decChunk097[1]! = 1563 := rfl
    exact (g 1553 (by decide) (by decide)).trans ((cell1552 1 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1554 (STORED, RETID test). -/
theorem sc_dec_T_1554 {s : Machine}
    (hpc : s.pc = 1554)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1554 ≤ k → k < 1557 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1557 } := by
  have hp : s.pc = UInt16.ofNat 1554 :=
    hpc.trans (rfl : (1554 : Word) = UInt16.ofNat 1554)
  have g (k : Nat) (h1 : 1554 ≤ k) (h2 : k < 1557) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk097[2]! = 3 := rfl
    exact (g 1554 (by decide) (by decide)).trans ((cell1552 2 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1555 : Word) := by simp [hpc]
    rw [this, (rfl : (1555 : Word) = UInt16.ofNat 1555)]
    have hval : decChunk097[3]! = 18 := rfl
    exact (g 1555 (by decide) (by decide)).trans ((cell1552 3 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1556 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1557 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1556 : Word) = UInt16.ofNat 1556)]
    have hval : decChunk097[4]! = 1557 := rfl
    have hv : (1557 : Word) = UInt16.ofNat 1557 := rfl
    exact (g 1556 (by decide) (by decide)).trans ((cell1552 4 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1557 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T RET_SIGN at pc 1557. -/
theorem sc_enc_jlez_1557 {s : Machine}
    (hpc : s.pc = 1557)
    (hcode : ∀ k : Nat, 1557 ≤ k → k < 1557+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1569 := by
  have hp : s.pc = UInt16.ofNat 1557 :=
    hpc.trans (rfl : (1557 : Word) = UInt16.ofNat 1557)
  have g (k : Nat) (h1 : 1557 ≤ k) (h2 : k < 1557+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk097[5]! = 0 := rfl
    exact (g 1557 (by decide) (by decide)).trans ((cell1552 5 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1558 : Word) := by simp [hpc]
    rw [this, (rfl : (1558 : Word) = UInt16.ofNat 1558)]
    have hval : decChunk097[6]! = 18 := rfl
    exact (g 1558 (by decide) (by decide)).trans ((cell1552 6 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1569 := by
    have : s.pc + 2 = (1559 : Word) := by simp [hpc]
    rw [this, (rfl : (1559 : Word) = UInt16.ofNat 1559)]
    have hval : decChunk097[7]! = 1569 := rfl
    exact (g 1559 (by decide) (by decide)).trans ((cell1552 7 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP RET_DIG at pc 1560. -/
theorem sc_enc_jmp_1560 {s : Machine}
    (hpc : s.pc = 1560)
    (hcode : ∀ k : Nat, 1560 ≤ k → k < 1560+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1572 := by
  have hp : s.pc = UInt16.ofNat 1560 :=
    hpc.trans (rfl : (1560 : Word) = UInt16.ofNat 1560)
  have g (k : Nat) (h1 : 1560 ≤ k) (h2 : k < 1560+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk097[8]! = 0 := rfl
    exact (g 1560 (by decide) (by decide)).trans ((cell1552 8 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1561 : Word) := by simp [hpc]
    rw [this, (rfl : (1561 : Word) = UInt16.ofNat 1561)]
    have hval : decChunk097[9]! = 0 := rfl
    exact (g 1561 (by decide) (by decide)).trans ((cell1552 9 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1572 := by
    have : s.pc + 2 = (1562 : Word) := by simp [hpc]
    rw [this, (rfl : (1562 : Word) = UInt16.ofNat 1562)]
    have hval : decChunk097[10]! = 1572 := rfl
    exact (g 1562 (by decide) (by decide)).trans ((cell1552 10 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC PAD at RET_PAD (pc 1563). -/
theorem sc_dec_PAD_1563 {s : Machine}
    (hpc : s.pc = 1563)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1563 ≤ k → k < 1566 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 27 (s.mem.get 27 - s.mem.get 3)
        pc := 1566 } := by
  have hp : s.pc = UInt16.ofNat 1563 :=
    hpc.trans (rfl : (1563 : Word) = UInt16.ofNat 1563)
  have g (k : Nat) (h1 : 1563 ≤ k) (h2 : k < 1566) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk097[11]! = 3 := rfl
    exact (g 1563 (by decide) (by decide)).trans ((cell1552 11 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 27 := by
    have : s.pc + 1 = (1564 : Word) := by simp [hpc]
    rw [this, (rfl : (1564 : Word) = UInt16.ofNat 1564)]
    have hval : decChunk097[12]! = 27 := rfl
    exact (g 1564 (by decide) (by decide)).trans ((cell1552 12 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1565 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1566 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1565 : Word) = UInt16.ofNat 1565)]
    have hval : decChunk097[13]! = 1566 := rfl
    have hv : (1566 : Word) = UInt16.ofNat 1566 := rfl
    exact (g 1565 (by decide) (by decide)).trans ((cell1552 13 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 27) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1566 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JMP SP_LOOP at pc 1566 (RET_PAD). -/
theorem sc_enc_jmp_1566 {s : Machine}
    (hpc : s.pc = 1566)
    (hcode : ∀ k : Nat, 1566 ≤ k → k < 1566+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1011 := by
  have hp : s.pc = UInt16.ofNat 1566 :=
    hpc.trans (rfl : (1566 : Word) = UInt16.ofNat 1566)
  have g (k : Nat) (h1 : 1566 ≤ k) (h2 : k < 1566+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk097[14]! = 0 := rfl
    exact (g 1566 (by decide) (by decide)).trans ((cell1552 14 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1567 : Word) := by simp [hpc]
    rw [this, (rfl : (1567 : Word) = UInt16.ofNat 1567)]
    have hval : decChunk097[15]! = 0 := rfl
    exact (g 1567 (by decide) (by decide)).trans ((cell1552 15 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1011 := by
    have : s.pc + 2 = (1568 : Word) := by simp [hpc]
    rw [this, (rfl : (1568 : Word) = UInt16.ofNat 1568)]
    have hval : decChunk098[0]! = 1011 := rfl
    exact (g 1568 (by decide) (by decide)).trans ((cell1568 0 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP AFTER_SIGN at RET_SIGN (pc 1569). -/
theorem sc_enc_jmp_1569 {s : Machine}
    (hpc : s.pc = 1569)
    (hcode : ∀ k : Nat, 1569 ≤ k → k < 1569+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1152 := by
  have hp : s.pc = UInt16.ofNat 1569 :=
    hpc.trans (rfl : (1569 : Word) = UInt16.ofNat 1569)
  have g (k : Nat) (h1 : 1569 ≤ k) (h2 : k < 1569+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk098[1]! = 0 := rfl
    exact (g 1569 (by decide) (by decide)).trans ((cell1568 1 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1570 : Word) := by simp [hpc]
    rw [this, (rfl : (1570 : Word) = UInt16.ofNat 1570)]
    have hval : decChunk098[2]! = 0 := rfl
    exact (g 1570 (by decide) (by decide)).trans ((cell1568 2 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1152 := by
    have : s.pc + 2 = (1571 : Word) := by simp [hpc]
    rw [this, (rfl : (1571 : Word) = UInt16.ofNat 1571)]
    have hval : decChunk098[3]! = 1152 := rfl
    exact (g 1571 (by decide) (by decide)).trans ((cell1568 3 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP DIG_NEXT at RET_DIG (pc 1572). -/
theorem sc_enc_jmp_1572 {s : Machine}
    (hpc : s.pc = 1572)
    (hcode : ∀ k : Nat, 1572 ≤ k → k < 1572+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1893 := by
  have hp : s.pc = UInt16.ofNat 1572 :=
    hpc.trans (rfl : (1572 : Word) = UInt16.ofNat 1572)
  have g (k : Nat) (h1 : 1572 ≤ k) (h2 : k < 1572+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk098[4]! = 0 := rfl
    exact (g 1572 (by decide) (by decide)).trans ((cell1568 4 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1573 : Word) := by simp [hpc]
    rw [this, (rfl : (1573 : Word) = UInt16.ofNat 1573)]
    have hval : decChunk098[5]! = 0 := rfl
    exact (g 1573 (by decide) (by decide)).trans ((cell1568 5 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1893 := by
    have : s.pc + 2 = (1574 : Word) := by simp [hpc]
    rw [this, (rfl : (1574 : Word) = UInt16.ofNat 1574)]
    have hval : decChunk098[6]! = 1893 := rfl
    exact (g 1574 (by decide) (by decide)).trans ((cell1568 6 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩


/-- `SIGN = 0` at `AFTER_PAD`: 6 steps to `EMIT_DIGS` (pc 1575). -/
theorem after_pad_sign0 {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hS : s.mem.get 19 = 0)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 1092 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hjmp : ∀ k : Nat, 1152 ≤ k → k < 1155 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s6 := runN s 6
    s6.pc = 1575 ∧
    s6.halted = false ∧
    s6.mem.get 0 = 0 ∧
    s6.mem.get 18 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a) := by
  intro s6
  have hm := ap_mov_SIGN_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1089 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 0 := hm.2.2.1.trans hS
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
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
  have henc := ap_enc_jlez_1089 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez :=
    step_JLEZ (s := s4) (x := 18) (dest := 1152)
      hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = true := by
    have : le0 (s4.mem.get 18) = true := by
      rw [hs4T]; exact le0_zero
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1152 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1152 : Word) else s4.pc + 3) = (1152 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1152 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 : ∀ k : Nat, 1152 ≤ k → k < 1155 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hjmp k h1 h2)
  have hencj := ap_enc_jmp_1152 (s := s5) hs5pc g5
  have hpc5 : s5.pc.toNat < 32768 := by simp [hs5pc]
  have hjmp := step_JMP (s := s5) (dest := 1575)
    hs5h hpc5 hs5Z hencj.1 hencj.2.1 hencj.2.2
  have hrun : s6 = step s5 := by
    have h6 : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact h6.trans (runN_one s5 hs5h hpc5)
  have hs6pc : s6.pc = 1575 := by rw [hrun, hjmp]
  have hs6h : s6.halted = false := by rw [hrun, hjmp]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs5Z
  have hs6T : s6.mem.get 18 = 0 := by rw [hrun, hjmp]; exact hs5T
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hjmp]; exact hpres5 a ha18 ha0
  exact ⟨hs6pc, hs6h, hs6Z, hs6T, hpres⟩

/-- From `ST0`, write `CH` to `BUF+0` and jump to `STORED`. 5 steps, 1287 → 1527. -/
theorem st0_store {s : Machine}
    (hpc : s.pc = 1287)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1287 ≤ k → k < 1302 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 32 = s.mem.get 30 ∧
    (∀ a, a ≠ 32 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st0_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1299 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 32 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1299 ≤ k → k < 1302 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n32 n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st0_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 32 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 32 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha32 ha0
    rw [hrun, hjmp]; exact hpres4 a ha32 ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩

/-- `IDX = 0` at `STORE_CH`: 10 steps to `STORED`, `BUF+0 = CH`. -/
theorem store_ch_idx0 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hI : s.mem.get 29 = 0)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1200 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hst : ∀ k : Nat, 1287 ≤ k → k < 1302 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s10 := runN s 10
    s10.pc = 1527 ∧
    s10.halted = false ∧
    s10.mem.get 0 = 0 ∧
    s10.mem.get 32 = s.mem.get 30 ∧
    s10.mem.get 29 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a) := by
  intro s10
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 0 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 0 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have g4 : ∀ k : Nat, 1197 ≤ k → k < 1200 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have henc := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = true := by
    have : le0 (s4.mem.get 18) = true := by
      rw [hs4T]; exact le0_zero
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1287 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1287 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1287 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hI5 : s5.mem.get 29 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 : ∀ k : Nat, 1287 ≤ k → k < 1302 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n18 n0).trans (hst k h1 h2)
  have hs := st0_store (s := s5) hs5pc hs5h hs5Z g5
  have hrun : s10 = runN s5 5 := runN_add_eq s 5 5 10 (by decide)
  have hs10pc : s10.pc = 1527 := by rw [hrun]; exact hs.1
  have hs10h : s10.halted = false := by rw [hrun]; exact hs.2.1
  have hs10Z : s10.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hs10B : s10.mem.get 32 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH5
  have hs10I : s10.mem.get 29 = 0 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI5
  have hpres : ∀ a, a ≠ 32 → a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha32 ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a ha32 ha0).trans (hpres5 a ha18 ha0)
  exact ⟨hs10pc, hs10h, hs10Z, hs10B, hs10I, hpres⟩
/-- DEC T at pc 1200 (STORE_CH dispatch, test for ST1). -/
theorem sc_dec_T_1200 {s : Machine}
    (hpc : s.pc = 1200)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1200 ≤ k → k < 1203 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1203 } := by
  have hp : s.pc = UInt16.ofNat 1200 :=
    hpc.trans (rfl : (1200 : Word) = UInt16.ofNat 1200)
  have g (k : Nat) (h1 : 1200 ≤ k) (h2 : k < 1203) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk075[0]! = 3 := rfl
    exact (g 1200 (by decide) (by decide)).trans ((cell1200 0 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1201 : Word) := by simp [hpc]
    rw [this, (rfl : (1201 : Word) = UInt16.ofNat 1201)]
    have hval : decChunk075[1]! = 18 := rfl
    exact (g 1201 (by decide) (by decide)).trans ((cell1200 1 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1202 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1203 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1202 : Word) = UInt16.ofNat 1202)]
    have hval : decChunk075[2]! = 1203 := rfl
    have hv : (1203 : Word) = UInt16.ofNat 1203 := rfl
    exact (g 1202 (by decide) (by decide)).trans ((cell1200 2 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1203 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST1 at pc 1203. -/
theorem sc_enc_jlez_1203 {s : Machine}
    (hpc : s.pc = 1203)
    (hcode : ∀ k : Nat, 1203 ≤ k → k < 1203+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1302 := by
  have hp : s.pc = UInt16.ofNat 1203 :=
    hpc.trans (rfl : (1203 : Word) = UInt16.ofNat 1203)
  have g (k : Nat) (h1 : 1203 ≤ k) (h2 : k < 1203+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk075[3]! = 0 := rfl
    exact (g 1203 (by decide) (by decide)).trans ((cell1200 3 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1204 : Word) := by simp [hpc]
    rw [this, (rfl : (1204 : Word) = UInt16.ofNat 1204)]
    have hval : decChunk075[4]! = 18 := rfl
    exact (g 1204 (by decide) (by decide)).trans ((cell1200 4 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1302 := by
    have : s.pc + 2 = (1205 : Word) := by simp [hpc]
    rw [this, (rfl : (1205 : Word) = UInt16.ofNat 1205)]
    have hval : decChunk075[5]! = 1302 := rfl
    exact (g 1205 (by decide) (by decide)).trans ((cell1200 5 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1206 (STORE_CH dispatch, test for ST2). -/
theorem sc_dec_T_1206 {s : Machine}
    (hpc : s.pc = 1206)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1206 ≤ k → k < 1209 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1209 } := by
  have hp : s.pc = UInt16.ofNat 1206 :=
    hpc.trans (rfl : (1206 : Word) = UInt16.ofNat 1206)
  have g (k : Nat) (h1 : 1206 ≤ k) (h2 : k < 1209) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk075[6]! = 3 := rfl
    exact (g 1206 (by decide) (by decide)).trans ((cell1200 6 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1207 : Word) := by simp [hpc]
    rw [this, (rfl : (1207 : Word) = UInt16.ofNat 1207)]
    have hval : decChunk075[7]! = 18 := rfl
    exact (g 1207 (by decide) (by decide)).trans ((cell1200 7 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1208 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1209 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1208 : Word) = UInt16.ofNat 1208)]
    have hval : decChunk075[8]! = 1209 := rfl
    have hv : (1209 : Word) = UInt16.ofNat 1209 := rfl
    exact (g 1208 (by decide) (by decide)).trans ((cell1200 8 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1209 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST2 at pc 1209. -/
theorem sc_enc_jlez_1209 {s : Machine}
    (hpc : s.pc = 1209)
    (hcode : ∀ k : Nat, 1209 ≤ k → k < 1209+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1317 := by
  have hp : s.pc = UInt16.ofNat 1209 :=
    hpc.trans (rfl : (1209 : Word) = UInt16.ofNat 1209)
  have g (k : Nat) (h1 : 1209 ≤ k) (h2 : k < 1209+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk075[9]! = 0 := rfl
    exact (g 1209 (by decide) (by decide)).trans ((cell1200 9 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1210 : Word) := by simp [hpc]
    rw [this, (rfl : (1210 : Word) = UInt16.ofNat 1210)]
    have hval : decChunk075[10]! = 18 := rfl
    exact (g 1210 (by decide) (by decide)).trans ((cell1200 10 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1317 := by
    have : s.pc + 2 = (1211 : Word) := by simp [hpc]
    rw [this, (rfl : (1211 : Word) = UInt16.ofNat 1211)]
    have hval : decChunk075[11]! = 1317 := rfl
    exact (g 1211 (by decide) (by decide)).trans ((cell1200 11 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1212 (STORE_CH dispatch, test for ST3). -/
theorem sc_dec_T_1212 {s : Machine}
    (hpc : s.pc = 1212)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1212 ≤ k → k < 1215 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1215 } := by
  have hp : s.pc = UInt16.ofNat 1212 :=
    hpc.trans (rfl : (1212 : Word) = UInt16.ofNat 1212)
  have g (k : Nat) (h1 : 1212 ≤ k) (h2 : k < 1215) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk075[12]! = 3 := rfl
    exact (g 1212 (by decide) (by decide)).trans ((cell1200 12 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1213 : Word) := by simp [hpc]
    rw [this, (rfl : (1213 : Word) = UInt16.ofNat 1213)]
    have hval : decChunk075[13]! = 18 := rfl
    exact (g 1213 (by decide) (by decide)).trans ((cell1200 13 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1214 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1215 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1214 : Word) = UInt16.ofNat 1214)]
    have hval : decChunk075[14]! = 1215 := rfl
    have hv : (1215 : Word) = UInt16.ofNat 1215 := rfl
    exact (g 1214 (by decide) (by decide)).trans ((cell1200 14 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1215 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST3 at pc 1215. -/
theorem sc_enc_jlez_1215 {s : Machine}
    (hpc : s.pc = 1215)
    (hcode : ∀ k : Nat, 1215 ≤ k → k < 1215+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1332 := by
  have hp : s.pc = UInt16.ofNat 1215 :=
    hpc.trans (rfl : (1215 : Word) = UInt16.ofNat 1215)
  have g (k : Nat) (h1 : 1215 ≤ k) (h2 : k < 1215+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk075[15]! = 0 := rfl
    exact (g 1215 (by decide) (by decide)).trans ((cell1200 15 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1216 : Word) := by simp [hpc]
    rw [this, (rfl : (1216 : Word) = UInt16.ofNat 1216)]
    have hval : decChunk076[0]! = 18 := rfl
    exact (g 1216 (by decide) (by decide)).trans ((cell1216 0 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1332 := by
    have : s.pc + 2 = (1217 : Word) := by simp [hpc]
    rw [this, (rfl : (1217 : Word) = UInt16.ofNat 1217)]
    have hval : decChunk076[1]! = 1332 := rfl
    exact (g 1217 (by decide) (by decide)).trans ((cell1216 1 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1218 (STORE_CH dispatch, test for ST4). -/
theorem sc_dec_T_1218 {s : Machine}
    (hpc : s.pc = 1218)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1218 ≤ k → k < 1221 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1221 } := by
  have hp : s.pc = UInt16.ofNat 1218 :=
    hpc.trans (rfl : (1218 : Word) = UInt16.ofNat 1218)
  have g (k : Nat) (h1 : 1218 ≤ k) (h2 : k < 1221) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk076[2]! = 3 := rfl
    exact (g 1218 (by decide) (by decide)).trans ((cell1216 2 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1219 : Word) := by simp [hpc]
    rw [this, (rfl : (1219 : Word) = UInt16.ofNat 1219)]
    have hval : decChunk076[3]! = 18 := rfl
    exact (g 1219 (by decide) (by decide)).trans ((cell1216 3 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1220 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1221 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1220 : Word) = UInt16.ofNat 1220)]
    have hval : decChunk076[4]! = 1221 := rfl
    have hv : (1221 : Word) = UInt16.ofNat 1221 := rfl
    exact (g 1220 (by decide) (by decide)).trans ((cell1216 4 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1221 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST4 at pc 1221. -/
theorem sc_enc_jlez_1221 {s : Machine}
    (hpc : s.pc = 1221)
    (hcode : ∀ k : Nat, 1221 ≤ k → k < 1221+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1347 := by
  have hp : s.pc = UInt16.ofNat 1221 :=
    hpc.trans (rfl : (1221 : Word) = UInt16.ofNat 1221)
  have g (k : Nat) (h1 : 1221 ≤ k) (h2 : k < 1221+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk076[5]! = 0 := rfl
    exact (g 1221 (by decide) (by decide)).trans ((cell1216 5 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1222 : Word) := by simp [hpc]
    rw [this, (rfl : (1222 : Word) = UInt16.ofNat 1222)]
    have hval : decChunk076[6]! = 18 := rfl
    exact (g 1222 (by decide) (by decide)).trans ((cell1216 6 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1347 := by
    have : s.pc + 2 = (1223 : Word) := by simp [hpc]
    rw [this, (rfl : (1223 : Word) = UInt16.ofNat 1223)]
    have hval : decChunk076[7]! = 1347 := rfl
    exact (g 1223 (by decide) (by decide)).trans ((cell1216 7 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1224 (STORE_CH dispatch, test for ST5). -/
theorem sc_dec_T_1224 {s : Machine}
    (hpc : s.pc = 1224)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1224 ≤ k → k < 1227 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1227 } := by
  have hp : s.pc = UInt16.ofNat 1224 :=
    hpc.trans (rfl : (1224 : Word) = UInt16.ofNat 1224)
  have g (k : Nat) (h1 : 1224 ≤ k) (h2 : k < 1227) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk076[8]! = 3 := rfl
    exact (g 1224 (by decide) (by decide)).trans ((cell1216 8 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1225 : Word) := by simp [hpc]
    rw [this, (rfl : (1225 : Word) = UInt16.ofNat 1225)]
    have hval : decChunk076[9]! = 18 := rfl
    exact (g 1225 (by decide) (by decide)).trans ((cell1216 9 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1226 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1227 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1226 : Word) = UInt16.ofNat 1226)]
    have hval : decChunk076[10]! = 1227 := rfl
    have hv : (1227 : Word) = UInt16.ofNat 1227 := rfl
    exact (g 1226 (by decide) (by decide)).trans ((cell1216 10 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1227 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST5 at pc 1227. -/
theorem sc_enc_jlez_1227 {s : Machine}
    (hpc : s.pc = 1227)
    (hcode : ∀ k : Nat, 1227 ≤ k → k < 1227+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1362 := by
  have hp : s.pc = UInt16.ofNat 1227 :=
    hpc.trans (rfl : (1227 : Word) = UInt16.ofNat 1227)
  have g (k : Nat) (h1 : 1227 ≤ k) (h2 : k < 1227+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk076[11]! = 0 := rfl
    exact (g 1227 (by decide) (by decide)).trans ((cell1216 11 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1228 : Word) := by simp [hpc]
    rw [this, (rfl : (1228 : Word) = UInt16.ofNat 1228)]
    have hval : decChunk076[12]! = 18 := rfl
    exact (g 1228 (by decide) (by decide)).trans ((cell1216 12 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1362 := by
    have : s.pc + 2 = (1229 : Word) := by simp [hpc]
    rw [this, (rfl : (1229 : Word) = UInt16.ofNat 1229)]
    have hval : decChunk076[13]! = 1362 := rfl
    exact (g 1229 (by decide) (by decide)).trans ((cell1216 13 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1230 (STORE_CH dispatch, test for ST6). -/
theorem sc_dec_T_1230 {s : Machine}
    (hpc : s.pc = 1230)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1230 ≤ k → k < 1233 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1233 } := by
  have hp : s.pc = UInt16.ofNat 1230 :=
    hpc.trans (rfl : (1230 : Word) = UInt16.ofNat 1230)
  have g (k : Nat) (h1 : 1230 ≤ k) (h2 : k < 1233) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk076[14]! = 3 := rfl
    exact (g 1230 (by decide) (by decide)).trans ((cell1216 14 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1231 : Word) := by simp [hpc]
    rw [this, (rfl : (1231 : Word) = UInt16.ofNat 1231)]
    have hval : decChunk076[15]! = 18 := rfl
    exact (g 1231 (by decide) (by decide)).trans ((cell1216 15 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1232 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1233 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1232 : Word) = UInt16.ofNat 1232)]
    have hval : decChunk077[0]! = 1233 := rfl
    have hv : (1233 : Word) = UInt16.ofNat 1233 := rfl
    exact (g 1232 (by decide) (by decide)).trans ((cell1232 0 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1233 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST6 at pc 1233. -/
theorem sc_enc_jlez_1233 {s : Machine}
    (hpc : s.pc = 1233)
    (hcode : ∀ k : Nat, 1233 ≤ k → k < 1233+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1377 := by
  have hp : s.pc = UInt16.ofNat 1233 :=
    hpc.trans (rfl : (1233 : Word) = UInt16.ofNat 1233)
  have g (k : Nat) (h1 : 1233 ≤ k) (h2 : k < 1233+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk077[1]! = 0 := rfl
    exact (g 1233 (by decide) (by decide)).trans ((cell1232 1 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1234 : Word) := by simp [hpc]
    rw [this, (rfl : (1234 : Word) = UInt16.ofNat 1234)]
    have hval : decChunk077[2]! = 18 := rfl
    exact (g 1234 (by decide) (by decide)).trans ((cell1232 2 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1377 := by
    have : s.pc + 2 = (1235 : Word) := by simp [hpc]
    rw [this, (rfl : (1235 : Word) = UInt16.ofNat 1235)]
    have hval : decChunk077[3]! = 1377 := rfl
    exact (g 1235 (by decide) (by decide)).trans ((cell1232 3 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1236 (STORE_CH dispatch, test for ST7). -/
theorem sc_dec_T_1236 {s : Machine}
    (hpc : s.pc = 1236)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1236 ≤ k → k < 1239 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1239 } := by
  have hp : s.pc = UInt16.ofNat 1236 :=
    hpc.trans (rfl : (1236 : Word) = UInt16.ofNat 1236)
  have g (k : Nat) (h1 : 1236 ≤ k) (h2 : k < 1239) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk077[4]! = 3 := rfl
    exact (g 1236 (by decide) (by decide)).trans ((cell1232 4 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1237 : Word) := by simp [hpc]
    rw [this, (rfl : (1237 : Word) = UInt16.ofNat 1237)]
    have hval : decChunk077[5]! = 18 := rfl
    exact (g 1237 (by decide) (by decide)).trans ((cell1232 5 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1238 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1239 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1238 : Word) = UInt16.ofNat 1238)]
    have hval : decChunk077[6]! = 1239 := rfl
    have hv : (1239 : Word) = UInt16.ofNat 1239 := rfl
    exact (g 1238 (by decide) (by decide)).trans ((cell1232 6 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1239 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST7 at pc 1239. -/
theorem sc_enc_jlez_1239 {s : Machine}
    (hpc : s.pc = 1239)
    (hcode : ∀ k : Nat, 1239 ≤ k → k < 1239+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1392 := by
  have hp : s.pc = UInt16.ofNat 1239 :=
    hpc.trans (rfl : (1239 : Word) = UInt16.ofNat 1239)
  have g (k : Nat) (h1 : 1239 ≤ k) (h2 : k < 1239+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk077[7]! = 0 := rfl
    exact (g 1239 (by decide) (by decide)).trans ((cell1232 7 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1240 : Word) := by simp [hpc]
    rw [this, (rfl : (1240 : Word) = UInt16.ofNat 1240)]
    have hval : decChunk077[8]! = 18 := rfl
    exact (g 1240 (by decide) (by decide)).trans ((cell1232 8 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1392 := by
    have : s.pc + 2 = (1241 : Word) := by simp [hpc]
    rw [this, (rfl : (1241 : Word) = UInt16.ofNat 1241)]
    have hval : decChunk077[9]! = 1392 := rfl
    exact (g 1241 (by decide) (by decide)).trans ((cell1232 9 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1242 (STORE_CH dispatch, test for ST8). -/
theorem sc_dec_T_1242 {s : Machine}
    (hpc : s.pc = 1242)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1242 ≤ k → k < 1245 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1245 } := by
  have hp : s.pc = UInt16.ofNat 1242 :=
    hpc.trans (rfl : (1242 : Word) = UInt16.ofNat 1242)
  have g (k : Nat) (h1 : 1242 ≤ k) (h2 : k < 1245) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk077[10]! = 3 := rfl
    exact (g 1242 (by decide) (by decide)).trans ((cell1232 10 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1243 : Word) := by simp [hpc]
    rw [this, (rfl : (1243 : Word) = UInt16.ofNat 1243)]
    have hval : decChunk077[11]! = 18 := rfl
    exact (g 1243 (by decide) (by decide)).trans ((cell1232 11 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1244 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1245 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1244 : Word) = UInt16.ofNat 1244)]
    have hval : decChunk077[12]! = 1245 := rfl
    have hv : (1245 : Word) = UInt16.ofNat 1245 := rfl
    exact (g 1244 (by decide) (by decide)).trans ((cell1232 12 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1245 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST8 at pc 1245. -/
theorem sc_enc_jlez_1245 {s : Machine}
    (hpc : s.pc = 1245)
    (hcode : ∀ k : Nat, 1245 ≤ k → k < 1245+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1407 := by
  have hp : s.pc = UInt16.ofNat 1245 :=
    hpc.trans (rfl : (1245 : Word) = UInt16.ofNat 1245)
  have g (k : Nat) (h1 : 1245 ≤ k) (h2 : k < 1245+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk077[13]! = 0 := rfl
    exact (g 1245 (by decide) (by decide)).trans ((cell1232 13 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1246 : Word) := by simp [hpc]
    rw [this, (rfl : (1246 : Word) = UInt16.ofNat 1246)]
    have hval : decChunk077[14]! = 18 := rfl
    exact (g 1246 (by decide) (by decide)).trans ((cell1232 14 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1407 := by
    have : s.pc + 2 = (1247 : Word) := by simp [hpc]
    rw [this, (rfl : (1247 : Word) = UInt16.ofNat 1247)]
    have hval : decChunk077[15]! = 1407 := rfl
    exact (g 1247 (by decide) (by decide)).trans ((cell1232 15 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1248 (STORE_CH dispatch, test for ST9). -/
theorem sc_dec_T_1248 {s : Machine}
    (hpc : s.pc = 1248)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1248 ≤ k → k < 1251 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1251 } := by
  have hp : s.pc = UInt16.ofNat 1248 :=
    hpc.trans (rfl : (1248 : Word) = UInt16.ofNat 1248)
  have g (k : Nat) (h1 : 1248 ≤ k) (h2 : k < 1251) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk078[0]! = 3 := rfl
    exact (g 1248 (by decide) (by decide)).trans ((cell1248 0 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1249 : Word) := by simp [hpc]
    rw [this, (rfl : (1249 : Word) = UInt16.ofNat 1249)]
    have hval : decChunk078[1]! = 18 := rfl
    exact (g 1249 (by decide) (by decide)).trans ((cell1248 1 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1250 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1251 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1250 : Word) = UInt16.ofNat 1250)]
    have hval : decChunk078[2]! = 1251 := rfl
    have hv : (1251 : Word) = UInt16.ofNat 1251 := rfl
    exact (g 1250 (by decide) (by decide)).trans ((cell1248 2 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1251 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST9 at pc 1251. -/
theorem sc_enc_jlez_1251 {s : Machine}
    (hpc : s.pc = 1251)
    (hcode : ∀ k : Nat, 1251 ≤ k → k < 1251+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1422 := by
  have hp : s.pc = UInt16.ofNat 1251 :=
    hpc.trans (rfl : (1251 : Word) = UInt16.ofNat 1251)
  have g (k : Nat) (h1 : 1251 ≤ k) (h2 : k < 1251+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk078[3]! = 0 := rfl
    exact (g 1251 (by decide) (by decide)).trans ((cell1248 3 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1252 : Word) := by simp [hpc]
    rw [this, (rfl : (1252 : Word) = UInt16.ofNat 1252)]
    have hval : decChunk078[4]! = 18 := rfl
    exact (g 1252 (by decide) (by decide)).trans ((cell1248 4 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1422 := by
    have : s.pc + 2 = (1253 : Word) := by simp [hpc]
    rw [this, (rfl : (1253 : Word) = UInt16.ofNat 1253)]
    have hval : decChunk078[5]! = 1422 := rfl
    exact (g 1253 (by decide) (by decide)).trans ((cell1248 5 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1254 (STORE_CH dispatch, test for ST10). -/
theorem sc_dec_T_1254 {s : Machine}
    (hpc : s.pc = 1254)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1254 ≤ k → k < 1257 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1257 } := by
  have hp : s.pc = UInt16.ofNat 1254 :=
    hpc.trans (rfl : (1254 : Word) = UInt16.ofNat 1254)
  have g (k : Nat) (h1 : 1254 ≤ k) (h2 : k < 1257) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk078[6]! = 3 := rfl
    exact (g 1254 (by decide) (by decide)).trans ((cell1248 6 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1255 : Word) := by simp [hpc]
    rw [this, (rfl : (1255 : Word) = UInt16.ofNat 1255)]
    have hval : decChunk078[7]! = 18 := rfl
    exact (g 1255 (by decide) (by decide)).trans ((cell1248 7 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1256 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1257 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1256 : Word) = UInt16.ofNat 1256)]
    have hval : decChunk078[8]! = 1257 := rfl
    have hv : (1257 : Word) = UInt16.ofNat 1257 := rfl
    exact (g 1256 (by decide) (by decide)).trans ((cell1248 8 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1257 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST10 at pc 1257. -/
theorem sc_enc_jlez_1257 {s : Machine}
    (hpc : s.pc = 1257)
    (hcode : ∀ k : Nat, 1257 ≤ k → k < 1257+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1437 := by
  have hp : s.pc = UInt16.ofNat 1257 :=
    hpc.trans (rfl : (1257 : Word) = UInt16.ofNat 1257)
  have g (k : Nat) (h1 : 1257 ≤ k) (h2 : k < 1257+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk078[9]! = 0 := rfl
    exact (g 1257 (by decide) (by decide)).trans ((cell1248 9 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1258 : Word) := by simp [hpc]
    rw [this, (rfl : (1258 : Word) = UInt16.ofNat 1258)]
    have hval : decChunk078[10]! = 18 := rfl
    exact (g 1258 (by decide) (by decide)).trans ((cell1248 10 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1437 := by
    have : s.pc + 2 = (1259 : Word) := by simp [hpc]
    rw [this, (rfl : (1259 : Word) = UInt16.ofNat 1259)]
    have hval : decChunk078[11]! = 1437 := rfl
    exact (g 1259 (by decide) (by decide)).trans ((cell1248 11 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1260 (STORE_CH dispatch, test for ST11). -/
theorem sc_dec_T_1260 {s : Machine}
    (hpc : s.pc = 1260)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1260 ≤ k → k < 1263 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1263 } := by
  have hp : s.pc = UInt16.ofNat 1260 :=
    hpc.trans (rfl : (1260 : Word) = UInt16.ofNat 1260)
  have g (k : Nat) (h1 : 1260 ≤ k) (h2 : k < 1263) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk078[12]! = 3 := rfl
    exact (g 1260 (by decide) (by decide)).trans ((cell1248 12 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1261 : Word) := by simp [hpc]
    rw [this, (rfl : (1261 : Word) = UInt16.ofNat 1261)]
    have hval : decChunk078[13]! = 18 := rfl
    exact (g 1261 (by decide) (by decide)).trans ((cell1248 13 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1262 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1263 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1262 : Word) = UInt16.ofNat 1262)]
    have hval : decChunk078[14]! = 1263 := rfl
    have hv : (1263 : Word) = UInt16.ofNat 1263 := rfl
    exact (g 1262 (by decide) (by decide)).trans ((cell1248 14 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1263 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST11 at pc 1263. -/
theorem sc_enc_jlez_1263 {s : Machine}
    (hpc : s.pc = 1263)
    (hcode : ∀ k : Nat, 1263 ≤ k → k < 1263+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1452 := by
  have hp : s.pc = UInt16.ofNat 1263 :=
    hpc.trans (rfl : (1263 : Word) = UInt16.ofNat 1263)
  have g (k : Nat) (h1 : 1263 ≤ k) (h2 : k < 1263+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk078[15]! = 0 := rfl
    exact (g 1263 (by decide) (by decide)).trans ((cell1248 15 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1264 : Word) := by simp [hpc]
    rw [this, (rfl : (1264 : Word) = UInt16.ofNat 1264)]
    have hval : decChunk079[0]! = 18 := rfl
    exact (g 1264 (by decide) (by decide)).trans ((cell1264 0 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1452 := by
    have : s.pc + 2 = (1265 : Word) := by simp [hpc]
    rw [this, (rfl : (1265 : Word) = UInt16.ofNat 1265)]
    have hval : decChunk079[1]! = 1452 := rfl
    exact (g 1265 (by decide) (by decide)).trans ((cell1264 1 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1266 (STORE_CH dispatch, test for ST12). -/
theorem sc_dec_T_1266 {s : Machine}
    (hpc : s.pc = 1266)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1266 ≤ k → k < 1269 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1269 } := by
  have hp : s.pc = UInt16.ofNat 1266 :=
    hpc.trans (rfl : (1266 : Word) = UInt16.ofNat 1266)
  have g (k : Nat) (h1 : 1266 ≤ k) (h2 : k < 1269) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk079[2]! = 3 := rfl
    exact (g 1266 (by decide) (by decide)).trans ((cell1264 2 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1267 : Word) := by simp [hpc]
    rw [this, (rfl : (1267 : Word) = UInt16.ofNat 1267)]
    have hval : decChunk079[3]! = 18 := rfl
    exact (g 1267 (by decide) (by decide)).trans ((cell1264 3 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1268 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1269 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1268 : Word) = UInt16.ofNat 1268)]
    have hval : decChunk079[4]! = 1269 := rfl
    have hv : (1269 : Word) = UInt16.ofNat 1269 := rfl
    exact (g 1268 (by decide) (by decide)).trans ((cell1264 4 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1269 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST12 at pc 1269. -/
theorem sc_enc_jlez_1269 {s : Machine}
    (hpc : s.pc = 1269)
    (hcode : ∀ k : Nat, 1269 ≤ k → k < 1269+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1467 := by
  have hp : s.pc = UInt16.ofNat 1269 :=
    hpc.trans (rfl : (1269 : Word) = UInt16.ofNat 1269)
  have g (k : Nat) (h1 : 1269 ≤ k) (h2 : k < 1269+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk079[5]! = 0 := rfl
    exact (g 1269 (by decide) (by decide)).trans ((cell1264 5 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1270 : Word) := by simp [hpc]
    rw [this, (rfl : (1270 : Word) = UInt16.ofNat 1270)]
    have hval : decChunk079[6]! = 18 := rfl
    exact (g 1270 (by decide) (by decide)).trans ((cell1264 6 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1467 := by
    have : s.pc + 2 = (1271 : Word) := by simp [hpc]
    rw [this, (rfl : (1271 : Word) = UInt16.ofNat 1271)]
    have hval : decChunk079[7]! = 1467 := rfl
    exact (g 1271 (by decide) (by decide)).trans ((cell1264 7 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1272 (STORE_CH dispatch, test for ST13). -/
theorem sc_dec_T_1272 {s : Machine}
    (hpc : s.pc = 1272)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1272 ≤ k → k < 1275 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1275 } := by
  have hp : s.pc = UInt16.ofNat 1272 :=
    hpc.trans (rfl : (1272 : Word) = UInt16.ofNat 1272)
  have g (k : Nat) (h1 : 1272 ≤ k) (h2 : k < 1275) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk079[8]! = 3 := rfl
    exact (g 1272 (by decide) (by decide)).trans ((cell1264 8 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1273 : Word) := by simp [hpc]
    rw [this, (rfl : (1273 : Word) = UInt16.ofNat 1273)]
    have hval : decChunk079[9]! = 18 := rfl
    exact (g 1273 (by decide) (by decide)).trans ((cell1264 9 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1274 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1275 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1274 : Word) = UInt16.ofNat 1274)]
    have hval : decChunk079[10]! = 1275 := rfl
    have hv : (1275 : Word) = UInt16.ofNat 1275 := rfl
    exact (g 1274 (by decide) (by decide)).trans ((cell1264 10 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1275 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST13 at pc 1275. -/
theorem sc_enc_jlez_1275 {s : Machine}
    (hpc : s.pc = 1275)
    (hcode : ∀ k : Nat, 1275 ≤ k → k < 1275+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1482 := by
  have hp : s.pc = UInt16.ofNat 1275 :=
    hpc.trans (rfl : (1275 : Word) = UInt16.ofNat 1275)
  have g (k : Nat) (h1 : 1275 ≤ k) (h2 : k < 1275+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk079[11]! = 0 := rfl
    exact (g 1275 (by decide) (by decide)).trans ((cell1264 11 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1276 : Word) := by simp [hpc]
    rw [this, (rfl : (1276 : Word) = UInt16.ofNat 1276)]
    have hval : decChunk079[12]! = 18 := rfl
    exact (g 1276 (by decide) (by decide)).trans ((cell1264 12 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1482 := by
    have : s.pc + 2 = (1277 : Word) := by simp [hpc]
    rw [this, (rfl : (1277 : Word) = UInt16.ofNat 1277)]
    have hval : decChunk079[13]! = 1482 := rfl
    exact (g 1277 (by decide) (by decide)).trans ((cell1264 13 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- DEC T at pc 1278 (STORE_CH dispatch, test for ST14). -/
theorem sc_dec_T_1278 {s : Machine}
    (hpc : s.pc = 1278)
    (hh : s.halted = false)
    (hcode : ∀ k : Nat, 1278 ≤ k → k < 1281 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - s.mem.get 3)
        pc := 1281 } := by
  have hp : s.pc = UInt16.ofNat 1278 :=
    hpc.trans (rfl : (1278 : Word) = UInt16.ofNat 1278)
  have g (k : Nat) (h1 : 1278 ≤ k) (h2 : k < 1281) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have ha : s.mem.get s.pc = 3 := by
    rw [hp]
    have hval : decChunk079[14]! = 3 := rfl
    exact (g 1278 (by decide) (by decide)).trans ((cell1264 14 (by decide)).trans hval)
  have hb : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1279 : Word) := by simp [hpc]
    rw [this, (rfl : (1279 : Word) = UInt16.ofNat 1279)]
    have hval : decChunk079[15]! = 18 := rfl
    exact (g 1279 (by decide) (by decide)).trans ((cell1264 15 (by decide)).trans hval)
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have hp2 : s.pc + 2 = (1280 : Word) := by simp [hpc]
    have hp3 : s.pc + 3 = (1281 : Word) := by simp [hpc]
    rw [hp2, hp3, (rfl : (1280 : Word) = UInt16.ofNat 1280)]
    have hval : decChunk080[0]! = 1281 := rfl
    have hv : (1281 : Word) = UInt16.ofNat 1281 := rfl
    exact (g 1280 (by decide) (by decide)).trans ((cell1280 0 (by decide)).trans (hval.trans hv))
  have hpc0 : s.pc.toNat < 32768 := by simp [hpc]
  have hsub :=
    step_SUB (s := s) (a := 3) (b := 18) hh hpc0 ha hb hc (by decide) (by decide)
  have hpc' : s.pc + 3 = (1281 : Word) := by simp [hpc]
  rw [hsub, hpc']

/-- JLEZ T ST14 at pc 1281. -/
theorem sc_enc_jlez_1281 {s : Machine}
    (hpc : s.pc = 1281)
    (hcode : ∀ k : Nat, 1281 ≤ k → k < 1281+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = 1497 := by
  have hp : s.pc = UInt16.ofNat 1281 :=
    hpc.trans (rfl : (1281 : Word) = UInt16.ofNat 1281)
  have g (k : Nat) (h1 : 1281 ≤ k) (h2 : k < 1281+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk080[1]! = 0 := rfl
    exact (g 1281 (by decide) (by decide)).trans ((cell1280 1 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 18 := by
    have : s.pc + 1 = (1282 : Word) := by simp [hpc]
    rw [this, (rfl : (1282 : Word) = UInt16.ofNat 1282)]
    have hval : decChunk080[2]! = 18 := rfl
    exact (g 1282 (by decide) (by decide)).trans ((cell1280 2 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1497 := by
    have : s.pc + 2 = (1283 : Word) := by simp [hpc]
    rw [this, (rfl : (1283 : Word) = UInt16.ofNat 1283)]
    have hval : decChunk080[3]! = 1497 := rfl
    exact (g 1283 (by decide) (by decide)).trans ((cell1280 3 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩

/-- JMP ST15 at pc 1284. -/
theorem sc_enc_jmp_1284 {s : Machine}
    (hpc : s.pc = 1284)
    (hcode : ∀ k : Nat, 1284 ≤ k → k < 1284+3 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = 1512 := by
  have hp : s.pc = UInt16.ofNat 1284 :=
    hpc.trans (rfl : (1284 : Word) = UInt16.ofNat 1284)
  have g (k : Nat) (h1 : 1284 ≤ k) (h2 : k < 1284+3) :
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := hcode k h1 h2
  have e0 : s.mem.get s.pc = 0 := by
    rw [hp]
    have hval : decChunk080[4]! = 0 := rfl
    exact (g 1284 (by decide) (by decide)).trans ((cell1280 4 (by decide)).trans hval)
  have e1 : s.mem.get (s.pc + 1) = 0 := by
    have : s.pc + 1 = (1285 : Word) := by simp [hpc]
    rw [this, (rfl : (1285 : Word) = UInt16.ofNat 1285)]
    have hval : decChunk080[5]! = 0 := rfl
    exact (g 1285 (by decide) (by decide)).trans ((cell1280 5 (by decide)).trans hval)
  have e2 : s.mem.get (s.pc + 2) = 1512 := by
    have : s.pc + 2 = (1286 : Word) := by simp [hpc]
    rw [this, (rfl : (1286 : Word) = UInt16.ofNat 1286)]
    have hval : decChunk080[6]! = 1512 := rfl
    exact (g 1286 (by decide) (by decide)).trans ((cell1280 6 (by decide)).trans hval)
  exact ⟨e0, e1, e2⟩


/-- From `ST1`, write `CH` to `BUF+1` and jump to `STORED`. 5 steps, 1302 → 1527. -/
theorem st1_store {s : Machine}
    (hpc : s.pc = 1302)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1302 ≤ k → k < 1317 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 33 = s.mem.get 30 ∧
    (∀ a, a ≠ 33 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st1_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1314 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 33 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1314 ≤ k → k < 1317 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st1_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 33 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 33 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST2`, write `CH` to `BUF+2` and jump to `STORED`. 5 steps, 1317 → 1527. -/
theorem st2_store {s : Machine}
    (hpc : s.pc = 1317)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1317 ≤ k → k < 1332 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 34 = s.mem.get 30 ∧
    (∀ a, a ≠ 34 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st2_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1329 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 34 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1329 ≤ k → k < 1332 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st2_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 34 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 34 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST3`, write `CH` to `BUF+3` and jump to `STORED`. 5 steps, 1332 → 1527. -/
theorem st3_store {s : Machine}
    (hpc : s.pc = 1332)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1332 ≤ k → k < 1347 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 35 = s.mem.get 30 ∧
    (∀ a, a ≠ 35 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st3_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1344 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 35 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1344 ≤ k → k < 1347 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st3_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 35 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 35 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST4`, write `CH` to `BUF+4` and jump to `STORED`. 5 steps, 1347 → 1527. -/
theorem st4_store {s : Machine}
    (hpc : s.pc = 1347)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1347 ≤ k → k < 1362 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 36 = s.mem.get 30 ∧
    (∀ a, a ≠ 36 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st4_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1359 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 36 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1359 ≤ k → k < 1362 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st4_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 36 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 36 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST5`, write `CH` to `BUF+5` and jump to `STORED`. 5 steps, 1362 → 1527. -/
theorem st5_store {s : Machine}
    (hpc : s.pc = 1362)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1362 ≤ k → k < 1377 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 37 = s.mem.get 30 ∧
    (∀ a, a ≠ 37 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st5_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1374 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 37 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1374 ≤ k → k < 1377 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st5_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 37 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 37 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST6`, write `CH` to `BUF+6` and jump to `STORED`. 5 steps, 1377 → 1527. -/
theorem st6_store {s : Machine}
    (hpc : s.pc = 1377)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1377 ≤ k → k < 1392 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 38 = s.mem.get 30 ∧
    (∀ a, a ≠ 38 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st6_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1389 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 38 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1389 ≤ k → k < 1392 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (38 : Word) := by
      have : (38 : Word) = UInt16.ofNat 38 := rfl
      rw [this]; exact ofNat_ne k 38 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st6_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 38 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 38 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST7`, write `CH` to `BUF+7` and jump to `STORED`. 5 steps, 1392 → 1527. -/
theorem st7_store {s : Machine}
    (hpc : s.pc = 1392)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1392 ≤ k → k < 1407 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 39 = s.mem.get 30 ∧
    (∀ a, a ≠ 39 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st7_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1404 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 39 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1404 ≤ k → k < 1407 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (39 : Word) := by
      have : (39 : Word) = UInt16.ofNat 39 := rfl
      rw [this]; exact ofNat_ne k 39 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st7_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 39 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 39 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST8`, write `CH` to `BUF+8` and jump to `STORED`. 5 steps, 1407 → 1527. -/
theorem st8_store {s : Machine}
    (hpc : s.pc = 1407)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1407 ≤ k → k < 1422 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 40 = s.mem.get 30 ∧
    (∀ a, a ≠ 40 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st8_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1419 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 40 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1419 ≤ k → k < 1422 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (40 : Word) := by
      have : (40 : Word) = UInt16.ofNat 40 := rfl
      rw [this]; exact ofNat_ne k 40 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st8_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 40 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 40 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST9`, write `CH` to `BUF+9` and jump to `STORED`. 5 steps, 1422 → 1527. -/
theorem st9_store {s : Machine}
    (hpc : s.pc = 1422)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1422 ≤ k → k < 1437 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 41 = s.mem.get 30 ∧
    (∀ a, a ≠ 41 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st9_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1434 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 41 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1434 ≤ k → k < 1437 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (41 : Word) := by
      have : (41 : Word) = UInt16.ofNat 41 := rfl
      rw [this]; exact ofNat_ne k 41 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st9_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 41 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 41 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST10`, write `CH` to `BUF+10` and jump to `STORED`. 5 steps, 1437 → 1527. -/
theorem st10_store {s : Machine}
    (hpc : s.pc = 1437)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1437 ≤ k → k < 1452 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 42 = s.mem.get 30 ∧
    (∀ a, a ≠ 42 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st10_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1449 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 42 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1449 ≤ k → k < 1452 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (42 : Word) := by
      have : (42 : Word) = UInt16.ofNat 42 := rfl
      rw [this]; exact ofNat_ne k 42 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st10_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 42 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 42 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST11`, write `CH` to `BUF+11` and jump to `STORED`. 5 steps, 1452 → 1527. -/
theorem st11_store {s : Machine}
    (hpc : s.pc = 1452)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1452 ≤ k → k < 1467 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 43 = s.mem.get 30 ∧
    (∀ a, a ≠ 43 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st11_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1464 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 43 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1464 ≤ k → k < 1467 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (43 : Word) := by
      have : (43 : Word) = UInt16.ofNat 43 := rfl
      rw [this]; exact ofNat_ne k 43 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st11_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 43 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 43 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST12`, write `CH` to `BUF+12` and jump to `STORED`. 5 steps, 1467 → 1527. -/
theorem st12_store {s : Machine}
    (hpc : s.pc = 1467)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1467 ≤ k → k < 1482 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 44 = s.mem.get 30 ∧
    (∀ a, a ≠ 44 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st12_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1479 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 44 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1479 ≤ k → k < 1482 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (44 : Word) := by
      have : (44 : Word) = UInt16.ofNat 44 := rfl
      rw [this]; exact ofNat_ne k 44 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st12_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 44 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 44 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST13`, write `CH` to `BUF+13` and jump to `STORED`. 5 steps, 1482 → 1527. -/
theorem st13_store {s : Machine}
    (hpc : s.pc = 1482)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1482 ≤ k → k < 1497 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 45 = s.mem.get 30 ∧
    (∀ a, a ≠ 45 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st13_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1494 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 45 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1494 ≤ k → k < 1497 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (45 : Word) := by
      have : (45 : Word) = UInt16.ofNat 45 := rfl
      rw [this]; exact ofNat_ne k 45 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st13_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 45 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 45 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST14`, write `CH` to `BUF+14` and jump to `STORED`. 5 steps, 1497 → 1527. -/
theorem st14_store {s : Machine}
    (hpc : s.pc = 1497)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1497 ≤ k → k < 1512 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 46 = s.mem.get 30 ∧
    (∀ a, a ≠ 46 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st14_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1509 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 46 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1509 ≤ k → k < 1512 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (46 : Word) := by
      have : (46 : Word) = UInt16.ofNat 46 := rfl
      rw [this]; exact ofNat_ne k 46 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st14_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 46 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 46 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- From `ST15`, write `CH` to `BUF+15` and jump to `STORED`. 5 steps, 1512 → 1527. -/
theorem st15_store {s : Machine}
    (hpc : s.pc = 1512)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcode : ∀ k : Nat, 1512 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    s5.pc = 1527 ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 47 = s.mem.get 30 ∧
    (∀ a, a ≠ 47 → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5
  have hm := sc_st15_mov_CH_BUF (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1524 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4B : s4.mem.get 47 = s.mem.get 30 := hm.2.2.1
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have g4 : ∀ k : Nat, 1524 ≤ k → k < 1527 →
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have nD : UInt16.ofNat k ≠ (47 : Word) := by
      have : (47 : Word) = UInt16.ofNat 47 := rfl
      rw [this]; exact ofNat_ne k 47 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres4 (UInt16.ofNat k) nD n0).trans (hcode k (by omega) (by omega))
  have henc := sc_st15_jmp_stored (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjmp := step_JMP (s := s4) (dest := 1527)
    hs4h hpc4 hs4Z henc.1 henc.2.1 henc.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  have hs5pc : s5.pc = 1527 := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5B : s5.mem.get 47 = s.mem.get 30 := by rw [hrun, hjmp]; exact hs4B
  have hpres : ∀ a, a ≠ 47 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a haD ha0
    rw [hrun, hjmp]; exact hpres4 a haD ha0
  exact ⟨hs5pc, hs5h, hs5Z, hs5B, hpres⟩


/-- Instruction cells in the `STORE_CH` / `STi` region are never `T` or `Z`. -/
theorem sc_code_shrink {s s' : Machine} {lo hi : Nat}
    (hpres : ∀ a, a ≠ (18 : Word) → a ≠ 0 → s'.mem.get a = s.mem.get a)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hlo : 1185 ≤ lo) (hhi : hi ≤ 1527) :
    ∀ k : Nat, lo ≤ k → k < hi →
      s'.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
  intro k h1 h2
  have hk0 : 1185 ≤ k := by omega
  have hk1 : k < 1527 := by omega
  have n18 : UInt16.ofNat k ≠ (18 : Word) := by
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact ofNat_ne k 18 (by omega) (by decide) (by omega)
  have n0 : UInt16.ofNat k ≠ (0 : Word) := by
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact ofNat_ne k 0 (by omega) (by decide) (by omega)
  exact (hpres (UInt16.ofNat k) n18 n0).trans (hcode k hk0 hk1)

theorem sc_stored_code_shrink {s s' : Machine} {lo hi : Nat}
    (hpres : ∀ a, a ≠ (18 : Word) → a ≠ (29 : Word) → a ≠ (27 : Word) → a ≠ 0 →
      s'.mem.get a = s.mem.get a)
    (hcode : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hlo : 1527 ≤ lo) (hhi : hi ≤ 1575) :
    ∀ k : Nat, lo ≤ k → k < hi →
      s'.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
  intro k h1 h2
  have hk0 : 1527 ≤ k := by omega
  have hk1 : k < 1575 := by omega
  have n18 : UInt16.ofNat k ≠ (18 : Word) := by
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
  have n29 : UInt16.ofNat k ≠ (29 : Word) := by
    have : (29 : Word) = UInt16.ofNat 29 := rfl
    rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
  have n27 : UInt16.ofNat k ≠ (27 : Word) := by
    have : (27 : Word) = UInt16.ofNat 27 := rfl
    rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
  have n0 : UInt16.ofNat k ≠ (0 : Word) := by
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
  exact (hpres (UInt16.ofNat k) n18 n29 n27 n0).trans (hcode k hk0 hk1)


/-- `RETID = 1` at `STORED`: 11 steps to `SP_LOOP`, `IDX += 1`, `PAD -= 1`. -/
theorem stored_ret_pad {s : Machine}
    (hpc : s.pc = 1527)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hR : s.mem.get 2319 = 1)
    (hcode : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s11 := runN s 11
    s11.pc = 1011 ∧
    s11.halted = false ∧
    s11.mem.get 0 = 0 ∧
    s11.mem.get 29 = s.mem.get 29 + 1 ∧
    s11.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a) := by
  intro s11
  have hi := sc_inc_IDX (s := s) hpc hh hZ hONE
    (fun k h1 h2 => hcode k h1 (by omega))
  let s3 := runN s 3
  have hs3pc : s3.pc = 1536 := hi.1
  have hs3h : s3.halted = false := hi.2.1
  have hs3I : s3.mem.get 29 = s.mem.get 29 + 1 := hi.2.2.1
  have hs3Z : s3.mem.get 0 = 0 := hi.2.2.2.1
  have hpres3 := hi.2.2.2.2
  have hONE3 : s3.mem.get 3 = 1 := (hpres3 3 (by decide) (by decide)).trans hONE
  have hR3 : s3.mem.get 2319 = 1 := (hpres3 2319 (by decide) (by decide)).trans hR
  have hP3 : s3.mem.get 27 = s.mem.get 27 := hpres3 27 (by decide) (by decide)
  have g3 := sc_stored_code_shrink (s := s) (s' := s3) (lo := 1536) (hi := 1548)
    (fun a ha18 ha29 ha27 ha0 => hpres3 a ha29 ha0) hcode (by decide) (by decide)
  have hm := sc_mov_RETID_T (s := s3) hs3pc hs3h hs3Z g3
  have hrun7 : runN s 7 = runN s3 4 := runN_add_eq s 3 4 7 (by decide)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1548 := by have : s7 = runN s3 4 := hrun7; rw [this]; exact hm.1
  have hs7h : s7.halted = false := by have : s7 = runN s3 4 := hrun7; rw [this]; exact hm.2.1
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = runN s3 4 := hrun7; rw [this]; exact hm.2.2.2.1
  have hs7T : s7.mem.get 18 = 1 := by
    have : s7 = runN s3 4 := hrun7
    rw [this]; exact hm.2.2.1.trans hR3
  have hs7I' : s7.mem.get 29 = s.mem.get 29 + 1 := by
    have : s7 = runN s3 4 := hrun7
    rw [this]
    exact (hm.2.2.2.2.2 29 (by decide) (by decide)).trans hs3I
  have hONE7 : s7.mem.get 3 = 1 := by
    have : s7 = runN s3 4 := hrun7
    rw [this]; exact (hm.2.2.2.2.2 3 (by decide) (by decide)).trans hONE3
  have hP7 : s7.mem.get 27 = s.mem.get 27 := by
    have : s7 = runN s3 4 := hrun7
    rw [this]; exact (hm.2.2.2.2.2 27 (by decide) (by decide)).trans hP3
  have hpres7 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    have : s7 = runN s3 4 := hrun7
    rw [this]
    exact (hm.2.2.2.2.2 a ha18 ha0).trans (hpres3 a ha29 ha0)
  have g7 := sc_stored_code_shrink (s := s) (s' := s7) (lo := 1548) (hi := 1551)
    (fun a ha18 ha29 _ha27 ha0 => hpres7 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have hdec := sc_dec_T_1548 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1551 } := hdec
  have hs8pc : (step s7).pc = 1551 := by rw [hs8eq]
  have hs8h : (step s7).halted = false := by rw [hs8eq]; exact hs7h
  have hs8Z : (step s7).mem.get 0 = 0 := by
    rw [hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : (step s7).mem.get 18 = 0 := by
    rw [hs8eq, Mem.get_set_eq]
    have : s7.mem.get 18 - s7.mem.get 3 = (1 : Word) - 1 := by rw [hs7T, hONE7]
    exact this.trans (rfl : (1 : Word) - 1 = 0)
  have hs8I : (step s7).mem.get 29 = s.mem.get 29 + 1 := by
    rw [hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7I'
  have hs8P : (step s7).mem.get 27 = s.mem.get 27 := by
    rw [hs8eq]
    exact (Mem.get_set_ne s7.mem 18 27 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hP7
  have hONE8 : (step s7).mem.get 3 = 1 := by
    rw [hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → (step s7).mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    rw [hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha29 ha18 ha0)
  have g8 := sc_stored_code_shrink (s := s) (s' := step s7) (lo := 1551) (hi := 1554)
    (fun a ha18 ha29 _ha27 ha0 => hpres8 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have henc := sc_enc_jlez_1551 (s := step s7) hs8pc g8
  have hpc8 : (step s7).pc.toNat < 32768 := by simp [hs8pc]
  have hjlez :=
    step_JLEZ (s := step s7) (x := 18) (dest := 1563)
      hs8h hpc8 hs8Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : ((step s7).mem.get 18 = 0 || 0x8000 ≤ (step s7).mem.get 18) = true := by
    have : le0 ((step s7).mem.get 18) = true := by
      rw [hs8T]; exact le0_zero
    simpa [le0] using this
  have hs9eq : step (step s7) = { step s7 with pc := 1563 } := by
    have hif :
        (if (step s7).mem.get 18 = 0 || 0x8000 ≤ (step s7).mem.get 18
          then (1563 : Word) else (step s7).pc + 3) = (1563 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hrun9 : runN s 9 = step (step s7) := by
    have h9 : runN s 9 = runN s7 2 := runN_add_eq s 7 2 9 (by decide)
    exact h9.trans (runN_2_steps s7 hs7h (by simp [hs7pc]) hs8h (by simp [hs8pc]))
  let s9 := runN s 9
  have hs9pc : s9.pc = 1563 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9I : s9.mem.get 29 = s.mem.get 29 + 1 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hs8I
  have hs9P : s9.mem.get 27 = s.mem.get 27 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hs8P
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    have : s9 = step (step s7) := hrun9
    rw [this, hs9eq]; exact hpres8 a ha29 ha18 ha0
  have g9 := sc_stored_code_shrink (s := s) (s' := s9) (lo := 1563) (hi := 1566)
    (fun a ha18 ha29 _ha27 ha0 => hpres9 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have hdecP := sc_dec_PAD_1563 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 27 (s9.mem.get 27 - s9.mem.get 3), pc := 1566 } := hdecP
  have hrun10 : runN s 10 = step s9 := by
    have h10 : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact h10.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1566 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 27 0 (s9.mem.get 27 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10P : s10.mem.get 27 = s.mem.get 27 - 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 27 - s9.mem.get 3 = s.mem.get 27 - 1 := by
      rw [hs9P, hONE9]
    exact h1
  have hs10I : s10.mem.get 29 = s.mem.get 29 + 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 27 29 (s9.mem.get 27 - s9.mem.get 3) (by decide)).trans hs9I
  have hpres10 : ∀ a, a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha29 ha27 ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 27 a (s9.mem.get 27 - s9.mem.get 3) ha27).trans
      (hpres9 a ha29 ha18 ha0)
  have g10 := sc_stored_code_shrink (s := s) (s' := s10) (lo := 1566) (hi := 1569)
    (fun a ha18 ha29 ha27 ha0 => hpres10 a ha29 ha27 ha18 ha0) hcode (by decide) (by decide)
  have hencj := sc_enc_jmp_1566 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjmp := step_JMP (s := s10) (dest := 1011)
    hs10h hpc10 hs10Z hencj.1 hencj.2.1 hencj.2.2
  have hrun : s11 = step s10 := by
    have h11 : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact h11.trans (runN_one s10 hs10h hpc10)
  have hs11pc : s11.pc = 1011 := by rw [hrun, hjmp]
  have hs11h : s11.halted = false := by rw [hrun, hjmp]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs10Z
  have hs11I : s11.mem.get 29 = s.mem.get 29 + 1 := by rw [hrun, hjmp]; exact hs10I
  have hs11P : s11.mem.get 27 = s.mem.get 27 - 1 := by rw [hrun, hjmp]; exact hs10P
  have hpres : ∀ a, a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha29 ha27 ha18 ha0
    rw [hrun, hjmp]; exact hpres10 a ha29 ha27 ha18 ha0
  exact ⟨hs11pc, hs11h, hs11Z, hs11I, hs11P, hpres⟩

/-- `RETID = 2` at `STORED`: 12 steps to `AFTER_SIGN`, `IDX += 1`. -/
theorem stored_ret_sign {s : Machine}
    (hpc : s.pc = 1527)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hR : s.mem.get 2319 = 2)
    (hcode : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s12 := runN s 12
    s12.pc = 1152 ∧
    s12.halted = false ∧
    s12.mem.get 0 = 0 ∧
    s12.mem.get 29 = s.mem.get 29 + 1 ∧
    (∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a) := by
  intro s12
  have hi := sc_inc_IDX (s := s) hpc hh hZ hONE
    (fun k h1 h2 => hcode k h1 (by omega))
  let s3 := runN s 3
  have hs3pc : s3.pc = 1536 := hi.1
  have hs3h : s3.halted = false := hi.2.1
  have hs3I : s3.mem.get 29 = s.mem.get 29 + 1 := hi.2.2.1
  have hs3Z : s3.mem.get 0 = 0 := hi.2.2.2.1
  have hpres3 := hi.2.2.2.2
  have hONE3 : s3.mem.get 3 = 1 := (hpres3 3 (by decide) (by decide)).trans hONE
  have hR3 : s3.mem.get 2319 = 2 := (hpres3 2319 (by decide) (by decide)).trans hR
  have g3 := sc_stored_code_shrink (s := s) (s' := s3) (lo := 1536) (hi := 1548)
    (fun a ha18 ha29 ha27 ha0 => hpres3 a ha29 ha0) hcode (by decide) (by decide)
  have hm := sc_mov_RETID_T (s := s3) hs3pc hs3h hs3Z g3
  have hrun7 : runN s 7 = runN s3 4 := runN_add_eq s 3 4 7 (by decide)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1548 := by have : s7 = runN s3 4 := hrun7; rw [this]; exact hm.1
  have hs7h : s7.halted = false := by have : s7 = runN s3 4 := hrun7; rw [this]; exact hm.2.1
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = runN s3 4 := hrun7; rw [this]; exact hm.2.2.2.1
  have hs7T : s7.mem.get 18 = 2 := by
    have : s7 = runN s3 4 := hrun7
    rw [this]; exact hm.2.2.1.trans hR3
  have hs7I : s7.mem.get 29 = s.mem.get 29 + 1 := by
    have : s7 = runN s3 4 := hrun7
    rw [this]; exact (hm.2.2.2.2.2 29 (by decide) (by decide)).trans hs3I
  have hONE7 : s7.mem.get 3 = 1 := by
    have : s7 = runN s3 4 := hrun7
    rw [this]; exact (hm.2.2.2.2.2 3 (by decide) (by decide)).trans hONE3
  have hpres7 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    have : s7 = runN s3 4 := hrun7
    rw [this]
    exact (hm.2.2.2.2.2 a ha18 ha0).trans (hpres3 a ha29 ha0)
  have g7 := sc_stored_code_shrink (s := s) (s' := s7) (lo := 1548) (hi := 1551)
    (fun a ha18 ha29 _ha27 ha0 => hpres7 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have hdec := sc_dec_T_1548 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1551 } := hdec
  have hs8pc : (step s7).pc = 1551 := by rw [hs8eq]
  have hs8h : (step s7).halted = false := by rw [hs8eq]; exact hs7h
  have hs8Z : (step s7).mem.get 0 = 0 := by
    rw [hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : (step s7).mem.get 18 = 1 := by
    rw [hs8eq, Mem.get_set_eq]
    have : s7.mem.get 18 - s7.mem.get 3 = (2 : Word) - 1 := by rw [hs7T, hONE7]
    exact this.trans (rfl : (2 : Word) - 1 = 1)
  have hs8I : (step s7).mem.get 29 = s.mem.get 29 + 1 := by
    rw [hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7I
  have hONE8 : (step s7).mem.get 3 = 1 := by
    rw [hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → (step s7).mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    rw [hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha29 ha18 ha0)
  have g8 := sc_stored_code_shrink (s := s) (s' := step s7) (lo := 1551) (hi := 1554)
    (fun a ha18 ha29 _ha27 ha0 => hpres8 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have henc := sc_enc_jlez_1551 (s := step s7) hs8pc g8
  have hpc8 : (step s7).pc.toNat < 32768 := by simp [hs8pc]
  have hjlez :=
    step_JLEZ (s := step s7) (x := 18) (dest := 1563)
      hs8h hpc8 hs8Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : ((step s7).mem.get 18 = 0 || 0x8000 ≤ (step s7).mem.get 18) = false := by
    have : le0 ((step s7).mem.get 18) = false := by
      rw [hs8T]
      exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step (step s7) = { step s7 with pc := 1554 } := by
    have hif :
        (if (step s7).mem.get 18 = 0 || 0x8000 ≤ (step s7).mem.get 18
          then (1563 : Word) else (step s7).pc + 3) = (1554 : Word) := by
      have hfall : (step s7).pc + 3 = (1554 : Word) := by simp [hs8pc]
      simp [hle, hfall]
    rw [hjlez, hif]
  have hrun9 : runN s 9 = step (step s7) := by
    have h9 : runN s 9 = runN s7 2 := runN_add_eq s 7 2 9 (by decide)
    exact h9.trans (runN_2_steps s7 hs7h (by simp [hs7pc]) hs8h (by simp [hs8pc]))
  let s9 := runN s 9
  have hs9pc : s9.pc = 1554 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 1 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hs8T
  have hs9I : s9.mem.get 29 = s.mem.get 29 + 1 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hs8I
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    have : s9 = step (step s7) := hrun9
    rw [this, hs9eq]; exact hpres8 a ha29 ha18 ha0
  have g9 := sc_stored_code_shrink (s := s) (s' := s9) (lo := 1554) (hi := 1557)
    (fun a ha18 ha29 _ha27 ha0 => hpres9 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1554 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1557 } := hdec2
  have hs10pc : (step s9).pc = 1557 := by rw [hs10eq]
  have hs10h : (step s9).halted = false := by rw [hs10eq]; exact hs9h
  have hs10Z : (step s9).mem.get 0 = 0 := by
    rw [hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : (step s9).mem.get 18 = 0 := by
    rw [hs10eq, Mem.get_set_eq]
    have : s9.mem.get 18 - s9.mem.get 3 = (1 : Word) - 1 := by rw [hs9T, hONE9]
    exact this.trans (rfl : (1 : Word) - 1 = 0)
  have hs10I : (step s9).mem.get 29 = s.mem.get 29 + 1 := by
    rw [hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9I
  have hpres10 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → (step s9).mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    rw [hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha29 ha18 ha0)
  have g10 := sc_stored_code_shrink (s := s) (s' := step s9) (lo := 1557) (hi := 1560)
    (fun a ha18 ha29 _ha27 ha0 => hpres10 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1557 (s := step s9) hs10pc g10
  have hpc10 : (step s9).pc.toNat < 32768 := by simp [hs10pc]
  have hjlez2 :=
    step_JLEZ (s := step s9) (x := 18) (dest := 1569)
      hs10h hpc10 hs10Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : ((step s9).mem.get 18 = 0 || 0x8000 ≤ (step s9).mem.get 18) = true := by
    have : le0 ((step s9).mem.get 18) = true := by
      rw [hs10T]; exact le0_zero
    simpa [le0] using this
  have hs11eq : step (step s9) = { step s9 with pc := 1569 } := by
    have hif :
        (if (step s9).mem.get 18 = 0 || 0x8000 ≤ (step s9).mem.get 18
          then (1569 : Word) else (step s9).pc + 3) = (1569 : Word) := by
      simp [hle2]
    rw [hjlez2, hif]
  have hrun11 : runN s 11 = step (step s9) := by
    have h11 : runN s 11 = runN s9 2 := runN_add_eq s 9 2 11 (by decide)
    exact h11.trans (runN_2_steps s9 hs9h (by simp [hs9pc]) hs10h (by simp [hs10pc]))
  let s11 := runN s 11
  have hs11pc : s11.pc = 1569 := by have : s11 = step (step s9) := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step (step s9) := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step (step s9) := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11I : s11.mem.get 29 = s.mem.get 29 + 1 := by have : s11 = step (step s9) := hrun11; rw [this, hs11eq]; exact hs10I
  have hpres11 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    have : s11 = step (step s9) := hrun11
    rw [this, hs11eq]; exact hpres10 a ha29 ha18 ha0
  have g11 := sc_stored_code_shrink (s := s) (s' := s11) (lo := 1569) (hi := 1572)
    (fun a ha18 ha29 _ha27 ha0 => hpres11 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have hencj := sc_enc_jmp_1569 (s := s11) hs11pc g11
  have hpc11 : s11.pc.toNat < 32768 := by simp [hs11pc]
  have hjmp := step_JMP (s := s11) (dest := 1152)
    hs11h hpc11 hs11Z hencj.1 hencj.2.1 hencj.2.2
  have hrun : s12 = step s11 := by
    have h12 : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact h12.trans (runN_one s11 hs11h hpc11)
  have hs12pc : s12.pc = 1152 := by rw [hrun, hjmp]
  have hs12h : s12.halted = false := by rw [hrun, hjmp]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs11Z
  have hs12I : s12.mem.get 29 = s.mem.get 29 + 1 := by rw [hrun, hjmp]; exact hs11I
  have hpres : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    rw [hrun, hjmp]; exact hpres11 a ha29 ha18 ha0
  exact ⟨hs12pc, hs12h, hs12Z, hs12I, hpres⟩

/-- `RETID = 3` at `STORED`: 13 steps to `DIG_NEXT`, `IDX += 1`. -/
theorem stored_ret_dig {s : Machine}
    (hpc : s.pc = 1527)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hR : s.mem.get 2319 = 3)
    (hcode : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s13 := runN s 13
    s13.pc = 1893 ∧
    s13.halted = false ∧
    s13.mem.get 0 = 0 ∧
    s13.mem.get 29 = s.mem.get 29 + 1 ∧
    (∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a) := by
  intro s13
  have hi := sc_inc_IDX (s := s) hpc hh hZ hONE
    (fun k h1 h2 => hcode k h1 (by omega))
  let s3 := runN s 3
  have hs3pc : s3.pc = 1536 := hi.1
  have hs3h : s3.halted = false := hi.2.1
  have hs3I : s3.mem.get 29 = s.mem.get 29 + 1 := hi.2.2.1
  have hs3Z : s3.mem.get 0 = 0 := hi.2.2.2.1
  have hpres3 := hi.2.2.2.2
  have hONE3 : s3.mem.get 3 = 1 := (hpres3 3 (by decide) (by decide)).trans hONE
  have hR3 : s3.mem.get 2319 = 3 := (hpres3 2319 (by decide) (by decide)).trans hR
  have g3 := sc_stored_code_shrink (s := s) (s' := s3) (lo := 1536) (hi := 1548)
    (fun a ha18 ha29 ha27 ha0 => hpres3 a ha29 ha0) hcode (by decide) (by decide)
  have hm := sc_mov_RETID_T (s := s3) hs3pc hs3h hs3Z g3
  have hrun7 : runN s 7 = runN s3 4 := runN_add_eq s 3 4 7 (by decide)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1548 := by have : s7 = runN s3 4 := hrun7; rw [this]; exact hm.1
  have hs7h : s7.halted = false := by have : s7 = runN s3 4 := hrun7; rw [this]; exact hm.2.1
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = runN s3 4 := hrun7; rw [this]; exact hm.2.2.2.1
  have hs7T : s7.mem.get 18 = 3 := by
    have : s7 = runN s3 4 := hrun7
    rw [this]; exact hm.2.2.1.trans hR3
  have hs7I : s7.mem.get 29 = s.mem.get 29 + 1 := by
    have : s7 = runN s3 4 := hrun7
    rw [this]; exact (hm.2.2.2.2.2 29 (by decide) (by decide)).trans hs3I
  have hONE7 : s7.mem.get 3 = 1 := by
    have : s7 = runN s3 4 := hrun7
    rw [this]; exact (hm.2.2.2.2.2 3 (by decide) (by decide)).trans hONE3
  have hpres7 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    have : s7 = runN s3 4 := hrun7
    rw [this]
    exact (hm.2.2.2.2.2 a ha18 ha0).trans (hpres3 a ha29 ha0)
  have g7 := sc_stored_code_shrink (s := s) (s' := s7) (lo := 1548) (hi := 1551)
    (fun a ha18 ha29 _ha27 ha0 => hpres7 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have hdec := sc_dec_T_1548 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1551 } := hdec
  have hs8pc : (step s7).pc = 1551 := by rw [hs8eq]
  have hs8h : (step s7).halted = false := by rw [hs8eq]; exact hs7h
  have hs8Z : (step s7).mem.get 0 = 0 := by
    rw [hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : (step s7).mem.get 18 = 2 := by
    rw [hs8eq, Mem.get_set_eq]
    have : s7.mem.get 18 - s7.mem.get 3 = (3 : Word) - 1 := by rw [hs7T, hONE7]
    exact this.trans (rfl : (3 : Word) - 1 = 2)
  have hs8I : (step s7).mem.get 29 = s.mem.get 29 + 1 := by
    rw [hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7I
  have hONE8 : (step s7).mem.get 3 = 1 := by
    rw [hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → (step s7).mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    rw [hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha29 ha18 ha0)
  have g8 := sc_stored_code_shrink (s := s) (s' := step s7) (lo := 1551) (hi := 1554)
    (fun a ha18 ha29 _ha27 ha0 => hpres8 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have henc := sc_enc_jlez_1551 (s := step s7) hs8pc g8
  have hpc8 : (step s7).pc.toNat < 32768 := by simp [hs8pc]
  have hjlez :=
    step_JLEZ (s := step s7) (x := 18) (dest := 1563)
      hs8h hpc8 hs8Z henc.1 henc.2.1 henc.2.2 (by decide)
  have hle : ((step s7).mem.get 18 = 0 || 0x8000 ≤ (step s7).mem.get 18) = false := by
    have : le0 ((step s7).mem.get 18) = false := by
      rw [hs8T]
      exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step (step s7) = { step s7 with pc := 1554 } := by
    have hif :
        (if (step s7).mem.get 18 = 0 || 0x8000 ≤ (step s7).mem.get 18
          then (1563 : Word) else (step s7).pc + 3) = (1554 : Word) := by
      have hfall : (step s7).pc + 3 = (1554 : Word) := by simp [hs8pc]
      simp [hle, hfall]
    rw [hjlez, hif]
  have hrun9 : runN s 9 = step (step s7) := by
    have h9 : runN s 9 = runN s7 2 := runN_add_eq s 7 2 9 (by decide)
    exact h9.trans (runN_2_steps s7 hs7h (by simp [hs7pc]) hs8h (by simp [hs8pc]))
  let s9 := runN s 9
  have hs9pc : s9.pc = 1554 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 2 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hs8T
  have hs9I : s9.mem.get 29 = s.mem.get 29 + 1 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hs8I
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step (step s7) := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    have : s9 = step (step s7) := hrun9
    rw [this, hs9eq]; exact hpres8 a ha29 ha18 ha0
  have g9 := sc_stored_code_shrink (s := s) (s' := s9) (lo := 1554) (hi := 1557)
    (fun a ha18 ha29 _ha27 ha0 => hpres9 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1554 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1557 } := hdec2
  have hs10pc : (step s9).pc = 1557 := by rw [hs10eq]
  have hs10h : (step s9).halted = false := by rw [hs10eq]; exact hs9h
  have hs10Z : (step s9).mem.get 0 = 0 := by
    rw [hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : (step s9).mem.get 18 = 1 := by
    rw [hs10eq, Mem.get_set_eq]
    have : s9.mem.get 18 - s9.mem.get 3 = (2 : Word) - 1 := by rw [hs9T, hONE9]
    exact this.trans (rfl : (2 : Word) - 1 = 1)
  have hs10I : (step s9).mem.get 29 = s.mem.get 29 + 1 := by
    rw [hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9I
  have hpres10 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → (step s9).mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    rw [hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha29 ha18 ha0)
  have g10 := sc_stored_code_shrink (s := s) (s' := step s9) (lo := 1557) (hi := 1560)
    (fun a ha18 ha29 _ha27 ha0 => hpres10 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1557 (s := step s9) hs10pc g10
  have hpc10 : (step s9).pc.toNat < 32768 := by simp [hs10pc]
  have hjlez2 :=
    step_JLEZ (s := step s9) (x := 18) (dest := 1569)
      hs10h hpc10 hs10Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : ((step s9).mem.get 18 = 0 || 0x8000 ≤ (step s9).mem.get 18) = false := by
    have : le0 ((step s9).mem.get 18) = false := by
      rw [hs10T]
      exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq : step (step s9) = { step s9 with pc := 1560 } := by
    have hif :
        (if (step s9).mem.get 18 = 0 || 0x8000 ≤ (step s9).mem.get 18
          then (1569 : Word) else (step s9).pc + 3) = (1560 : Word) := by
      have hfall : (step s9).pc + 3 = (1560 : Word) := by simp [hs10pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun11 : runN s 11 = step (step s9) := by
    have h11 : runN s 11 = runN s9 2 := runN_add_eq s 9 2 11 (by decide)
    exact h11.trans (runN_2_steps s9 hs9h (by simp [hs9pc]) hs10h (by simp [hs10pc]))
  let s11 := runN s 11
  have hs11pc : s11.pc = 1560 := by have : s11 = step (step s9) := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step (step s9) := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step (step s9) := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11I : s11.mem.get 29 = s.mem.get 29 + 1 := by have : s11 = step (step s9) := hrun11; rw [this, hs11eq]; exact hs10I
  have hpres11 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    have : s11 = step (step s9) := hrun11
    rw [this, hs11eq]; exact hpres10 a ha29 ha18 ha0
  have g11 := sc_stored_code_shrink (s := s) (s' := s11) (lo := 1560) (hi := 1563)
    (fun a ha18 ha29 _ha27 ha0 => hpres11 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have hencj := sc_enc_jmp_1560 (s := s11) hs11pc g11
  have hpc11 : s11.pc.toNat < 32768 := by simp [hs11pc]
  have hjmp := step_JMP (s := s11) (dest := 1572)
    hs11h hpc11 hs11Z hencj.1 hencj.2.1 hencj.2.2
  have hrun12 : runN s 12 = step s11 := by
    have h12 : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact h12.trans (runN_one s11 hs11h hpc11)
  let s12 := runN s 12
  have hs12pc : s12.pc = 1572 := by have : s12 = step s11 := hrun12; rw [this, hjmp]
  have hs12h : s12.halted = false := by have : s12 = step s11 := hrun12; rw [this, hjmp]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by have : s12 = step s11 := hrun12; rw [this, hjmp]; exact hs11Z
  have hs12I : s12.mem.get 29 = s.mem.get 29 + 1 := by have : s12 = step s11 := hrun12; rw [this, hjmp]; exact hs11I
  have hpres12 : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    have : s12 = step s11 := hrun12
    rw [this, hjmp]; exact hpres11 a ha29 ha18 ha0
  have g12 := sc_stored_code_shrink (s := s) (s' := s12) (lo := 1572) (hi := 1575)
    (fun a ha18 ha29 _ha27 ha0 => hpres12 a ha29 ha18 ha0) hcode (by decide) (by decide)
  have hencj2 := sc_enc_jmp_1572 (s := s12) hs12pc g12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hjmp2 := step_JMP (s := s12) (dest := 1893)
    hs12h hpc12 hs12Z hencj2.1 hencj2.2.1 hencj2.2.2
  have hrun : s13 = step s12 := by
    have h13 : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    exact h13.trans (runN_one s12 hs12h hpc12)
  have hs13pc : s13.pc = 1893 := by rw [hrun, hjmp2]
  have hs13h : s13.halted = false := by rw [hrun, hjmp2]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by rw [hrun, hjmp2]; exact hs12Z
  have hs13I : s13.mem.get 29 = s.mem.get 29 + 1 := by rw [hrun, hjmp2]; exact hs12I
  have hpres : ∀ a, a ≠ 29 → a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha29 ha18 ha0
    rw [hrun, hjmp2]; exact hpres12 a ha29 ha18 ha0
  exact ⟨hs13pc, hs13h, hs13Z, hs13I, hpres⟩
/-- `IDX = 1` at `STORE_CH`: 12 steps to `STORED`, `BUF+1 = CH`. -/
theorem store_ch_idx1 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 1)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 12
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 33 = s.mem.get 30 ∧
    sN.mem.get 29 = 1 ∧
    (∀ a, a ≠ 33 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 1 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 1 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (1 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI6 : s6.mem.get 29 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = true := by
    have : le0 (s6.mem.get 18) = true := by
      rw [hs6T]; exact le0_zero
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1302 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1302 : Word) := by
      simp [hle1]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1302 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1302) (hi := 1317)
    hpres7 hcode (by decide) (by decide)
  have hs := st1_store (s := s7) hs7pc hs7h hs7Z g7
  have hrun : sN = runN s7 5 := runN_add_eq s 7 5 12 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 33 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH7
  have hsNI : sN.mem.get 29 = 1 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI7
  have hpres : ∀ a, a ≠ 33 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres7 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 2` at `STORE_CH`: 14 steps to `STORED`, `BUF+2 = CH`. -/
theorem store_ch_idx2 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 2)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 14
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 34 = s.mem.get 30 ∧
    sN.mem.get 29 = 2 ∧
    (∀ a, a ≠ 34 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 2 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 2 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 2 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 2 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (2 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI6 : s6.mem.get 29 = 2 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 2 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (1 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI8 : s8.mem.get 29 = 2 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = true := by
    have : le0 (s8.mem.get 18) = true := by
      rw [hs8T]; exact le0_zero
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1317 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1317 : Word) := by
      simp [hle2]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1317 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 2 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1317) (hi := 1332)
    hpres9 hcode (by decide) (by decide)
  have hs := st2_store (s := s9) hs9pc hs9h hs9Z g9
  have hrun : sN = runN s9 5 := runN_add_eq s 9 5 14 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 34 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH9
  have hsNI : sN.mem.get 29 = 2 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI9
  have hpres : ∀ a, a ≠ 34 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres9 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 3` at `STORE_CH`: 16 steps to `STORED`, `BUF+3 = CH`. -/
theorem store_ch_idx3 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 3)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 16
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 35 = s.mem.get 30 ∧
    sN.mem.get 29 = 3 ∧
    (∀ a, a ≠ 35 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 3 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 3 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 3 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 3 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 2 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (3 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hI6 : s6.mem.get 29 = 3 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 2 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 3 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (2 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI8 : s8.mem.get 29 = 3 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1212 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1212 : Word) := by
      have hfall : s8.pc + 3 = (1212 : Word) := by simp [hs8pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1212 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 3 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1212) (hi := 1215)
    hpres9 hcode (by decide) (by decide)
  have hdec3 := sc_dec_T_1212 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1215 } := hdec3
  have hrun10 : runN s 10 = step s9 := by
    have hS : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hS.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1215 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : s10.mem.get 18 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (1 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI10 : s10.mem.get 29 = 3 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hI9
  have hCH10 : s10.mem.get 30 = s.mem.get 30 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 30 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hCH9
  have hONE10 : s10.mem.get 3 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 3 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have g10 := sc_code_shrink (s := s) (s' := s10) (lo := 1215) (hi := 1218)
    hpres10 hcode (by decide) (by decide)
  have henc3 := sc_enc_jlez_1215 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjlez3 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1332)
      hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = true := by
    have : le0 (s10.mem.get 18) = true := by
      rw [hs10T]; exact le0_zero
    simpa [le0] using this
  have hs11eq : step s10 = { s10 with pc := 1332 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1332 : Word) else s10.pc + 3) = (1332 : Word) := by
      simp [hle3]
    rw [hjlez3, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hS : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hS.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1332 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11T : s11.mem.get 18 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10T
  have hI11 : s11.mem.get 29 = 3 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hI10
  have hCH11 : s11.mem.get 30 = s.mem.get 30 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hCH10
  have hONE11 : s11.mem.get 3 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hONE10
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq]; exact hpres10 a ha18 ha0
  have g11 := sc_code_shrink (s := s) (s' := s11) (lo := 1332) (hi := 1347)
    hpres11 hcode (by decide) (by decide)
  have hs := st3_store (s := s11) hs11pc hs11h hs11Z g11
  have hrun : sN = runN s11 5 := runN_add_eq s 11 5 16 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 35 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH11
  have hsNI : sN.mem.get 29 = 3 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI11
  have hpres : ∀ a, a ≠ 35 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres11 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 4` at `STORE_CH`: 18 steps to `STORED`, `BUF+4 = CH`. -/
theorem store_ch_idx4 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 4)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 18
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 36 = s.mem.get 30 ∧
    sN.mem.get 29 = 4 ∧
    (∀ a, a ≠ 36 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 4 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 4 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 4 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 4 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 3 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (4 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (4 : Word) - 1 = 3)
  have hI6 : s6.mem.get 29 = 4 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 3 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 4 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 2 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (3 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hI8 : s8.mem.get 29 = 4 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1212 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1212 : Word) := by
      have hfall : s8.pc + 3 = (1212 : Word) := by simp [hs8pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1212 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 2 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 4 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1212) (hi := 1215)
    hpres9 hcode (by decide) (by decide)
  have hdec3 := sc_dec_T_1212 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1215 } := hdec3
  have hrun10 : runN s 10 = step s9 := by
    have hS : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hS.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1215 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : s10.mem.get 18 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (2 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI10 : s10.mem.get 29 = 4 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hI9
  have hCH10 : s10.mem.get 30 = s.mem.get 30 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 30 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hCH9
  have hONE10 : s10.mem.get 3 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 3 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have g10 := sc_code_shrink (s := s) (s' := s10) (lo := 1215) (hi := 1218)
    hpres10 hcode (by decide) (by decide)
  have henc3 := sc_enc_jlez_1215 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjlez3 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1332)
      hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = false := by
    have : le0 (s10.mem.get 18) = false := by
      rw [hs10T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq : step s10 = { s10 with pc := 1218 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1332 : Word) else s10.pc + 3) = (1218 : Word) := by
      have hfall : s10.pc + 3 = (1218 : Word) := by simp [hs10pc]
      simp [hle3, hfall]
    rw [hjlez3, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hS : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hS.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1218 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11T : s11.mem.get 18 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10T
  have hI11 : s11.mem.get 29 = 4 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hI10
  have hCH11 : s11.mem.get 30 = s.mem.get 30 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hCH10
  have hONE11 : s11.mem.get 3 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hONE10
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq]; exact hpres10 a ha18 ha0
  have g11 := sc_code_shrink (s := s) (s' := s11) (lo := 1218) (hi := 1221)
    hpres11 hcode (by decide) (by decide)
  have hdec4 := sc_dec_T_1218 (s := s11) hs11pc hs11h g11
  have hs12eq : step s11 =
      { s11 with mem := s11.mem.set 18 (s11.mem.get 18 - s11.mem.get 3), pc := 1221 } := hdec4
  have hrun12 : runN s 12 = step s11 := by
    have hS : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hS.trans (runN_one s11 hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1221 := by have : s12 = step s11 := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step s11 := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 0 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hs11Z
  have hs12T : s12.mem.get 18 = 0 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq, Mem.get_set_eq]
    have h1 : s11.mem.get 18 - s11.mem.get 3 = (1 : Word) - 1 := by
      rw [hs11T, hONE11]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI12 : s12.mem.get 29 = 4 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 29 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hI11
  have hCH12 : s12.mem.get 30 = s.mem.get 30 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 30 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hCH11
  have hONE12 : s12.mem.get 3 = 1 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 3 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hONE11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 a (s11.mem.get 18 - s11.mem.get 3) ha18).trans
      (hpres11 a ha18 ha0)
  have g12 := sc_code_shrink (s := s) (s' := s12) (lo := 1221) (hi := 1224)
    hpres12 hcode (by decide) (by decide)
  have henc4 := sc_enc_jlez_1221 (s := s12) hs12pc g12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hjlez4 :=
    step_JLEZ (s := s12) (x := 18) (dest := 1347)
      hs12h hpc12 hs12Z henc4.1 henc4.2.1 henc4.2.2 (by decide)
  have hle4 : (s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18) = true := by
    have : le0 (s12.mem.get 18) = true := by
      rw [hs12T]; exact le0_zero
    simpa [le0] using this
  have hs13eq : step s12 = { s12 with pc := 1347 } := by
    have hif :
        (if s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18
          then (1347 : Word) else s12.pc + 3) = (1347 : Word) := by
      simp [hle4]
    rw [hjlez4, hif]
  have hrun13 : runN s 13 = step s12 := by
    have hS : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    exact hS.trans (runN_one s12 hs12h hpc12)
  let s13 := runN s 13
  have hs13pc : s13.pc = 1347 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]
  have hs13h : s13.halted = false := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12Z
  have hs13T : s13.mem.get 18 = 0 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12T
  have hI13 : s13.mem.get 29 = 4 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hI12
  have hCH13 : s13.mem.get 30 = s.mem.get 30 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hCH12
  have hONE13 : s13.mem.get 3 = 1 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hONE12
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s13 = step s12 := hrun13
    rw [this, hs13eq]; exact hpres12 a ha18 ha0
  have g13 := sc_code_shrink (s := s) (s' := s13) (lo := 1347) (hi := 1362)
    hpres13 hcode (by decide) (by decide)
  have hs := st4_store (s := s13) hs13pc hs13h hs13Z g13
  have hrun : sN = runN s13 5 := runN_add_eq s 13 5 18 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 36 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH13
  have hsNI : sN.mem.get 29 = 4 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI13
  have hpres : ∀ a, a ≠ 36 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres13 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 5` at `STORE_CH`: 20 steps to `STORED`, `BUF+5 = CH`. -/
theorem store_ch_idx5 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 5)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 20
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 37 = s.mem.get 30 ∧
    sN.mem.get 29 = 5 ∧
    (∀ a, a ≠ 37 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 5 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 5 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 5 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 5 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 4 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (5 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (5 : Word) - 1 = 4)
  have hI6 : s6.mem.get 29 = 5 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 4 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 5 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 3 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (4 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (4 : Word) - 1 = 3)
  have hI8 : s8.mem.get 29 = 5 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1212 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1212 : Word) := by
      have hfall : s8.pc + 3 = (1212 : Word) := by simp [hs8pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1212 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 3 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 5 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1212) (hi := 1215)
    hpres9 hcode (by decide) (by decide)
  have hdec3 := sc_dec_T_1212 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1215 } := hdec3
  have hrun10 : runN s 10 = step s9 := by
    have hS : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hS.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1215 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : s10.mem.get 18 = 2 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (3 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hI10 : s10.mem.get 29 = 5 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hI9
  have hCH10 : s10.mem.get 30 = s.mem.get 30 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 30 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hCH9
  have hONE10 : s10.mem.get 3 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 3 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have g10 := sc_code_shrink (s := s) (s' := s10) (lo := 1215) (hi := 1218)
    hpres10 hcode (by decide) (by decide)
  have henc3 := sc_enc_jlez_1215 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjlez3 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1332)
      hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = false := by
    have : le0 (s10.mem.get 18) = false := by
      rw [hs10T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq : step s10 = { s10 with pc := 1218 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1332 : Word) else s10.pc + 3) = (1218 : Word) := by
      have hfall : s10.pc + 3 = (1218 : Word) := by simp [hs10pc]
      simp [hle3, hfall]
    rw [hjlez3, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hS : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hS.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1218 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11T : s11.mem.get 18 = 2 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10T
  have hI11 : s11.mem.get 29 = 5 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hI10
  have hCH11 : s11.mem.get 30 = s.mem.get 30 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hCH10
  have hONE11 : s11.mem.get 3 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hONE10
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq]; exact hpres10 a ha18 ha0
  have g11 := sc_code_shrink (s := s) (s' := s11) (lo := 1218) (hi := 1221)
    hpres11 hcode (by decide) (by decide)
  have hdec4 := sc_dec_T_1218 (s := s11) hs11pc hs11h g11
  have hs12eq : step s11 =
      { s11 with mem := s11.mem.set 18 (s11.mem.get 18 - s11.mem.get 3), pc := 1221 } := hdec4
  have hrun12 : runN s 12 = step s11 := by
    have hS : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hS.trans (runN_one s11 hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1221 := by have : s12 = step s11 := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step s11 := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 0 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hs11Z
  have hs12T : s12.mem.get 18 = 1 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq, Mem.get_set_eq]
    have h1 : s11.mem.get 18 - s11.mem.get 3 = (2 : Word) - 1 := by
      rw [hs11T, hONE11]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI12 : s12.mem.get 29 = 5 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 29 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hI11
  have hCH12 : s12.mem.get 30 = s.mem.get 30 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 30 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hCH11
  have hONE12 : s12.mem.get 3 = 1 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 3 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hONE11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 a (s11.mem.get 18 - s11.mem.get 3) ha18).trans
      (hpres11 a ha18 ha0)
  have g12 := sc_code_shrink (s := s) (s' := s12) (lo := 1221) (hi := 1224)
    hpres12 hcode (by decide) (by decide)
  have henc4 := sc_enc_jlez_1221 (s := s12) hs12pc g12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hjlez4 :=
    step_JLEZ (s := s12) (x := 18) (dest := 1347)
      hs12h hpc12 hs12Z henc4.1 henc4.2.1 henc4.2.2 (by decide)
  have hle4 : (s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18) = false := by
    have : le0 (s12.mem.get 18) = false := by
      rw [hs12T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs13eq : step s12 = { s12 with pc := 1224 } := by
    have hif :
        (if s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18
          then (1347 : Word) else s12.pc + 3) = (1224 : Word) := by
      have hfall : s12.pc + 3 = (1224 : Word) := by simp [hs12pc]
      simp [hle4, hfall]
    rw [hjlez4, hif]
  have hrun13 : runN s 13 = step s12 := by
    have hS : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    exact hS.trans (runN_one s12 hs12h hpc12)
  let s13 := runN s 13
  have hs13pc : s13.pc = 1224 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]
  have hs13h : s13.halted = false := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12Z
  have hs13T : s13.mem.get 18 = 1 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12T
  have hI13 : s13.mem.get 29 = 5 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hI12
  have hCH13 : s13.mem.get 30 = s.mem.get 30 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hCH12
  have hONE13 : s13.mem.get 3 = 1 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hONE12
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s13 = step s12 := hrun13
    rw [this, hs13eq]; exact hpres12 a ha18 ha0
  have g13 := sc_code_shrink (s := s) (s' := s13) (lo := 1224) (hi := 1227)
    hpres13 hcode (by decide) (by decide)
  have hdec5 := sc_dec_T_1224 (s := s13) hs13pc hs13h g13
  have hs14eq : step s13 =
      { s13 with mem := s13.mem.set 18 (s13.mem.get 18 - s13.mem.get 3), pc := 1227 } := hdec5
  have hrun14 : runN s 14 = step s13 := by
    have hS : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hS.trans (runN_one s13 hs13h (by simp [hs13pc]))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1227 := by have : s14 = step s13 := hrun14; rw [this, hs14eq]
  have hs14h : s14.halted = false := by have : s14 = step s13 := hrun14; rw [this, hs14eq]; exact hs13h
  have hs14Z : s14.mem.get 0 = 0 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 0 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hs13Z
  have hs14T : s14.mem.get 18 = 0 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq, Mem.get_set_eq]
    have h1 : s13.mem.get 18 - s13.mem.get 3 = (1 : Word) - 1 := by
      rw [hs13T, hONE13]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI14 : s14.mem.get 29 = 5 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 29 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hI13
  have hCH14 : s14.mem.get 30 = s.mem.get 30 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 30 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hCH13
  have hONE14 : s14.mem.get 3 = 1 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 3 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hONE13
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 a (s13.mem.get 18 - s13.mem.get 3) ha18).trans
      (hpres13 a ha18 ha0)
  have g14 := sc_code_shrink (s := s) (s' := s14) (lo := 1227) (hi := 1230)
    hpres14 hcode (by decide) (by decide)
  have henc5 := sc_enc_jlez_1227 (s := s14) hs14pc g14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hjlez5 :=
    step_JLEZ (s := s14) (x := 18) (dest := 1362)
      hs14h hpc14 hs14Z henc5.1 henc5.2.1 henc5.2.2 (by decide)
  have hle5 : (s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18) = true := by
    have : le0 (s14.mem.get 18) = true := by
      rw [hs14T]; exact le0_zero
    simpa [le0] using this
  have hs15eq : step s14 = { s14 with pc := 1362 } := by
    have hif :
        (if s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18
          then (1362 : Word) else s14.pc + 3) = (1362 : Word) := by
      simp [hle5]
    rw [hjlez5, hif]
  have hrun15 : runN s 15 = step s14 := by
    have hS : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    exact hS.trans (runN_one s14 hs14h hpc14)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1362 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]
  have hs15h : s15.halted = false := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14Z
  have hs15T : s15.mem.get 18 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14T
  have hI15 : s15.mem.get 29 = 5 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hI14
  have hCH15 : s15.mem.get 30 = s.mem.get 30 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hCH14
  have hONE15 : s15.mem.get 3 = 1 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hONE14
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s15 = step s14 := hrun15
    rw [this, hs15eq]; exact hpres14 a ha18 ha0
  have g15 := sc_code_shrink (s := s) (s' := s15) (lo := 1362) (hi := 1377)
    hpres15 hcode (by decide) (by decide)
  have hs := st5_store (s := s15) hs15pc hs15h hs15Z g15
  have hrun : sN = runN s15 5 := runN_add_eq s 15 5 20 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 37 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH15
  have hsNI : sN.mem.get 29 = 5 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI15
  have hpres : ∀ a, a ≠ 37 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres15 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 6` at `STORE_CH`: 22 steps to `STORED`, `BUF+6 = CH`. -/
theorem store_ch_idx6 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 6)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 22
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 38 = s.mem.get 30 ∧
    sN.mem.get 29 = 6 ∧
    (∀ a, a ≠ 38 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 6 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 6 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 6 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 6 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 5 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (6 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (6 : Word) - 1 = 5)
  have hI6 : s6.mem.get 29 = 6 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 5 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 6 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 4 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (5 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (5 : Word) - 1 = 4)
  have hI8 : s8.mem.get 29 = 6 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1212 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1212 : Word) := by
      have hfall : s8.pc + 3 = (1212 : Word) := by simp [hs8pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1212 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 4 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 6 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1212) (hi := 1215)
    hpres9 hcode (by decide) (by decide)
  have hdec3 := sc_dec_T_1212 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1215 } := hdec3
  have hrun10 : runN s 10 = step s9 := by
    have hS : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hS.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1215 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : s10.mem.get 18 = 3 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (4 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (4 : Word) - 1 = 3)
  have hI10 : s10.mem.get 29 = 6 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hI9
  have hCH10 : s10.mem.get 30 = s.mem.get 30 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 30 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hCH9
  have hONE10 : s10.mem.get 3 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 3 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have g10 := sc_code_shrink (s := s) (s' := s10) (lo := 1215) (hi := 1218)
    hpres10 hcode (by decide) (by decide)
  have henc3 := sc_enc_jlez_1215 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjlez3 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1332)
      hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = false := by
    have : le0 (s10.mem.get 18) = false := by
      rw [hs10T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq : step s10 = { s10 with pc := 1218 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1332 : Word) else s10.pc + 3) = (1218 : Word) := by
      have hfall : s10.pc + 3 = (1218 : Word) := by simp [hs10pc]
      simp [hle3, hfall]
    rw [hjlez3, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hS : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hS.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1218 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11T : s11.mem.get 18 = 3 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10T
  have hI11 : s11.mem.get 29 = 6 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hI10
  have hCH11 : s11.mem.get 30 = s.mem.get 30 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hCH10
  have hONE11 : s11.mem.get 3 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hONE10
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq]; exact hpres10 a ha18 ha0
  have g11 := sc_code_shrink (s := s) (s' := s11) (lo := 1218) (hi := 1221)
    hpres11 hcode (by decide) (by decide)
  have hdec4 := sc_dec_T_1218 (s := s11) hs11pc hs11h g11
  have hs12eq : step s11 =
      { s11 with mem := s11.mem.set 18 (s11.mem.get 18 - s11.mem.get 3), pc := 1221 } := hdec4
  have hrun12 : runN s 12 = step s11 := by
    have hS : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hS.trans (runN_one s11 hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1221 := by have : s12 = step s11 := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step s11 := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 0 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hs11Z
  have hs12T : s12.mem.get 18 = 2 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq, Mem.get_set_eq]
    have h1 : s11.mem.get 18 - s11.mem.get 3 = (3 : Word) - 1 := by
      rw [hs11T, hONE11]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hI12 : s12.mem.get 29 = 6 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 29 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hI11
  have hCH12 : s12.mem.get 30 = s.mem.get 30 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 30 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hCH11
  have hONE12 : s12.mem.get 3 = 1 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 3 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hONE11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 a (s11.mem.get 18 - s11.mem.get 3) ha18).trans
      (hpres11 a ha18 ha0)
  have g12 := sc_code_shrink (s := s) (s' := s12) (lo := 1221) (hi := 1224)
    hpres12 hcode (by decide) (by decide)
  have henc4 := sc_enc_jlez_1221 (s := s12) hs12pc g12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hjlez4 :=
    step_JLEZ (s := s12) (x := 18) (dest := 1347)
      hs12h hpc12 hs12Z henc4.1 henc4.2.1 henc4.2.2 (by decide)
  have hle4 : (s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18) = false := by
    have : le0 (s12.mem.get 18) = false := by
      rw [hs12T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs13eq : step s12 = { s12 with pc := 1224 } := by
    have hif :
        (if s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18
          then (1347 : Word) else s12.pc + 3) = (1224 : Word) := by
      have hfall : s12.pc + 3 = (1224 : Word) := by simp [hs12pc]
      simp [hle4, hfall]
    rw [hjlez4, hif]
  have hrun13 : runN s 13 = step s12 := by
    have hS : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    exact hS.trans (runN_one s12 hs12h hpc12)
  let s13 := runN s 13
  have hs13pc : s13.pc = 1224 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]
  have hs13h : s13.halted = false := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12Z
  have hs13T : s13.mem.get 18 = 2 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12T
  have hI13 : s13.mem.get 29 = 6 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hI12
  have hCH13 : s13.mem.get 30 = s.mem.get 30 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hCH12
  have hONE13 : s13.mem.get 3 = 1 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hONE12
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s13 = step s12 := hrun13
    rw [this, hs13eq]; exact hpres12 a ha18 ha0
  have g13 := sc_code_shrink (s := s) (s' := s13) (lo := 1224) (hi := 1227)
    hpres13 hcode (by decide) (by decide)
  have hdec5 := sc_dec_T_1224 (s := s13) hs13pc hs13h g13
  have hs14eq : step s13 =
      { s13 with mem := s13.mem.set 18 (s13.mem.get 18 - s13.mem.get 3), pc := 1227 } := hdec5
  have hrun14 : runN s 14 = step s13 := by
    have hS : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hS.trans (runN_one s13 hs13h (by simp [hs13pc]))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1227 := by have : s14 = step s13 := hrun14; rw [this, hs14eq]
  have hs14h : s14.halted = false := by have : s14 = step s13 := hrun14; rw [this, hs14eq]; exact hs13h
  have hs14Z : s14.mem.get 0 = 0 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 0 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hs13Z
  have hs14T : s14.mem.get 18 = 1 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq, Mem.get_set_eq]
    have h1 : s13.mem.get 18 - s13.mem.get 3 = (2 : Word) - 1 := by
      rw [hs13T, hONE13]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI14 : s14.mem.get 29 = 6 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 29 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hI13
  have hCH14 : s14.mem.get 30 = s.mem.get 30 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 30 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hCH13
  have hONE14 : s14.mem.get 3 = 1 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 3 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hONE13
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 a (s13.mem.get 18 - s13.mem.get 3) ha18).trans
      (hpres13 a ha18 ha0)
  have g14 := sc_code_shrink (s := s) (s' := s14) (lo := 1227) (hi := 1230)
    hpres14 hcode (by decide) (by decide)
  have henc5 := sc_enc_jlez_1227 (s := s14) hs14pc g14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hjlez5 :=
    step_JLEZ (s := s14) (x := 18) (dest := 1362)
      hs14h hpc14 hs14Z henc5.1 henc5.2.1 henc5.2.2 (by decide)
  have hle5 : (s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18) = false := by
    have : le0 (s14.mem.get 18) = false := by
      rw [hs14T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs15eq : step s14 = { s14 with pc := 1230 } := by
    have hif :
        (if s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18
          then (1362 : Word) else s14.pc + 3) = (1230 : Word) := by
      have hfall : s14.pc + 3 = (1230 : Word) := by simp [hs14pc]
      simp [hle5, hfall]
    rw [hjlez5, hif]
  have hrun15 : runN s 15 = step s14 := by
    have hS : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    exact hS.trans (runN_one s14 hs14h hpc14)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1230 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]
  have hs15h : s15.halted = false := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14Z
  have hs15T : s15.mem.get 18 = 1 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14T
  have hI15 : s15.mem.get 29 = 6 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hI14
  have hCH15 : s15.mem.get 30 = s.mem.get 30 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hCH14
  have hONE15 : s15.mem.get 3 = 1 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hONE14
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s15 = step s14 := hrun15
    rw [this, hs15eq]; exact hpres14 a ha18 ha0
  have g15 := sc_code_shrink (s := s) (s' := s15) (lo := 1230) (hi := 1233)
    hpres15 hcode (by decide) (by decide)
  have hdec6 := sc_dec_T_1230 (s := s15) hs15pc hs15h g15
  have hs16eq : step s15 =
      { s15 with mem := s15.mem.set 18 (s15.mem.get 18 - s15.mem.get 3), pc := 1233 } := hdec6
  have hrun16 : runN s 16 = step s15 := by
    have hS : runN s 16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
    exact hS.trans (runN_one s15 hs15h (by simp [hs15pc]))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1233 := by have : s16 = step s15 := hrun16; rw [this, hs16eq]
  have hs16h : s16.halted = false := by have : s16 = step s15 := hrun16; rw [this, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 0 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hs15Z
  have hs16T : s16.mem.get 18 = 0 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq, Mem.get_set_eq]
    have h1 : s15.mem.get 18 - s15.mem.get 3 = (1 : Word) - 1 := by
      rw [hs15T, hONE15]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI16 : s16.mem.get 29 = 6 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 29 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hI15
  have hCH16 : s16.mem.get 30 = s.mem.get 30 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 30 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hCH15
  have hONE16 : s16.mem.get 3 = 1 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 3 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hONE15
  have hpres16 : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 a (s15.mem.get 18 - s15.mem.get 3) ha18).trans
      (hpres15 a ha18 ha0)
  have g16 := sc_code_shrink (s := s) (s' := s16) (lo := 1233) (hi := 1236)
    hpres16 hcode (by decide) (by decide)
  have henc6 := sc_enc_jlez_1233 (s := s16) hs16pc g16
  have hpc16 : s16.pc.toNat < 32768 := by simp [hs16pc]
  have hjlez6 :=
    step_JLEZ (s := s16) (x := 18) (dest := 1377)
      hs16h hpc16 hs16Z henc6.1 henc6.2.1 henc6.2.2 (by decide)
  have hle6 : (s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18) = true := by
    have : le0 (s16.mem.get 18) = true := by
      rw [hs16T]; exact le0_zero
    simpa [le0] using this
  have hs17eq : step s16 = { s16 with pc := 1377 } := by
    have hif :
        (if s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18
          then (1377 : Word) else s16.pc + 3) = (1377 : Word) := by
      simp [hle6]
    rw [hjlez6, hif]
  have hrun17 : runN s 17 = step s16 := by
    have hS : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
    exact hS.trans (runN_one s16 hs16h hpc16)
  let s17 := runN s 17
  have hs17pc : s17.pc = 1377 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]
  have hs17h : s17.halted = false := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16h
  have hs17Z : s17.mem.get 0 = 0 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16Z
  have hs17T : s17.mem.get 18 = 0 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16T
  have hI17 : s17.mem.get 29 = 6 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hI16
  have hCH17 : s17.mem.get 30 = s.mem.get 30 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hCH16
  have hONE17 : s17.mem.get 3 = 1 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hONE16
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s17 = step s16 := hrun17
    rw [this, hs17eq]; exact hpres16 a ha18 ha0
  have g17 := sc_code_shrink (s := s) (s' := s17) (lo := 1377) (hi := 1392)
    hpres17 hcode (by decide) (by decide)
  have hs := st6_store (s := s17) hs17pc hs17h hs17Z g17
  have hrun : sN = runN s17 5 := runN_add_eq s 17 5 22 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 38 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH17
  have hsNI : sN.mem.get 29 = 6 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI17
  have hpres : ∀ a, a ≠ 38 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 7` at `STORE_CH`: 24 steps to `STORED`, `BUF+7 = CH`. -/
theorem store_ch_idx7 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 7)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 24
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 39 = s.mem.get 30 ∧
    sN.mem.get 29 = 7 ∧
    (∀ a, a ≠ 39 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 7 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 7 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 7 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 7 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 6 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (7 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (7 : Word) - 1 = 6)
  have hI6 : s6.mem.get 29 = 7 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 6 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 7 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 5 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (6 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (6 : Word) - 1 = 5)
  have hI8 : s8.mem.get 29 = 7 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1212 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1212 : Word) := by
      have hfall : s8.pc + 3 = (1212 : Word) := by simp [hs8pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1212 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 5 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 7 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1212) (hi := 1215)
    hpres9 hcode (by decide) (by decide)
  have hdec3 := sc_dec_T_1212 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1215 } := hdec3
  have hrun10 : runN s 10 = step s9 := by
    have hS : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hS.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1215 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : s10.mem.get 18 = 4 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (5 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (5 : Word) - 1 = 4)
  have hI10 : s10.mem.get 29 = 7 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hI9
  have hCH10 : s10.mem.get 30 = s.mem.get 30 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 30 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hCH9
  have hONE10 : s10.mem.get 3 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 3 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have g10 := sc_code_shrink (s := s) (s' := s10) (lo := 1215) (hi := 1218)
    hpres10 hcode (by decide) (by decide)
  have henc3 := sc_enc_jlez_1215 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjlez3 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1332)
      hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = false := by
    have : le0 (s10.mem.get 18) = false := by
      rw [hs10T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq : step s10 = { s10 with pc := 1218 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1332 : Word) else s10.pc + 3) = (1218 : Word) := by
      have hfall : s10.pc + 3 = (1218 : Word) := by simp [hs10pc]
      simp [hle3, hfall]
    rw [hjlez3, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hS : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hS.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1218 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11T : s11.mem.get 18 = 4 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10T
  have hI11 : s11.mem.get 29 = 7 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hI10
  have hCH11 : s11.mem.get 30 = s.mem.get 30 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hCH10
  have hONE11 : s11.mem.get 3 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hONE10
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq]; exact hpres10 a ha18 ha0
  have g11 := sc_code_shrink (s := s) (s' := s11) (lo := 1218) (hi := 1221)
    hpres11 hcode (by decide) (by decide)
  have hdec4 := sc_dec_T_1218 (s := s11) hs11pc hs11h g11
  have hs12eq : step s11 =
      { s11 with mem := s11.mem.set 18 (s11.mem.get 18 - s11.mem.get 3), pc := 1221 } := hdec4
  have hrun12 : runN s 12 = step s11 := by
    have hS : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hS.trans (runN_one s11 hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1221 := by have : s12 = step s11 := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step s11 := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 0 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hs11Z
  have hs12T : s12.mem.get 18 = 3 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq, Mem.get_set_eq]
    have h1 : s11.mem.get 18 - s11.mem.get 3 = (4 : Word) - 1 := by
      rw [hs11T, hONE11]
    exact h1.trans (rfl : (4 : Word) - 1 = 3)
  have hI12 : s12.mem.get 29 = 7 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 29 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hI11
  have hCH12 : s12.mem.get 30 = s.mem.get 30 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 30 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hCH11
  have hONE12 : s12.mem.get 3 = 1 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 3 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hONE11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 a (s11.mem.get 18 - s11.mem.get 3) ha18).trans
      (hpres11 a ha18 ha0)
  have g12 := sc_code_shrink (s := s) (s' := s12) (lo := 1221) (hi := 1224)
    hpres12 hcode (by decide) (by decide)
  have henc4 := sc_enc_jlez_1221 (s := s12) hs12pc g12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hjlez4 :=
    step_JLEZ (s := s12) (x := 18) (dest := 1347)
      hs12h hpc12 hs12Z henc4.1 henc4.2.1 henc4.2.2 (by decide)
  have hle4 : (s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18) = false := by
    have : le0 (s12.mem.get 18) = false := by
      rw [hs12T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs13eq : step s12 = { s12 with pc := 1224 } := by
    have hif :
        (if s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18
          then (1347 : Word) else s12.pc + 3) = (1224 : Word) := by
      have hfall : s12.pc + 3 = (1224 : Word) := by simp [hs12pc]
      simp [hle4, hfall]
    rw [hjlez4, hif]
  have hrun13 : runN s 13 = step s12 := by
    have hS : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    exact hS.trans (runN_one s12 hs12h hpc12)
  let s13 := runN s 13
  have hs13pc : s13.pc = 1224 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]
  have hs13h : s13.halted = false := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12Z
  have hs13T : s13.mem.get 18 = 3 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12T
  have hI13 : s13.mem.get 29 = 7 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hI12
  have hCH13 : s13.mem.get 30 = s.mem.get 30 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hCH12
  have hONE13 : s13.mem.get 3 = 1 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hONE12
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s13 = step s12 := hrun13
    rw [this, hs13eq]; exact hpres12 a ha18 ha0
  have g13 := sc_code_shrink (s := s) (s' := s13) (lo := 1224) (hi := 1227)
    hpres13 hcode (by decide) (by decide)
  have hdec5 := sc_dec_T_1224 (s := s13) hs13pc hs13h g13
  have hs14eq : step s13 =
      { s13 with mem := s13.mem.set 18 (s13.mem.get 18 - s13.mem.get 3), pc := 1227 } := hdec5
  have hrun14 : runN s 14 = step s13 := by
    have hS : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hS.trans (runN_one s13 hs13h (by simp [hs13pc]))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1227 := by have : s14 = step s13 := hrun14; rw [this, hs14eq]
  have hs14h : s14.halted = false := by have : s14 = step s13 := hrun14; rw [this, hs14eq]; exact hs13h
  have hs14Z : s14.mem.get 0 = 0 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 0 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hs13Z
  have hs14T : s14.mem.get 18 = 2 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq, Mem.get_set_eq]
    have h1 : s13.mem.get 18 - s13.mem.get 3 = (3 : Word) - 1 := by
      rw [hs13T, hONE13]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hI14 : s14.mem.get 29 = 7 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 29 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hI13
  have hCH14 : s14.mem.get 30 = s.mem.get 30 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 30 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hCH13
  have hONE14 : s14.mem.get 3 = 1 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 3 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hONE13
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 a (s13.mem.get 18 - s13.mem.get 3) ha18).trans
      (hpres13 a ha18 ha0)
  have g14 := sc_code_shrink (s := s) (s' := s14) (lo := 1227) (hi := 1230)
    hpres14 hcode (by decide) (by decide)
  have henc5 := sc_enc_jlez_1227 (s := s14) hs14pc g14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hjlez5 :=
    step_JLEZ (s := s14) (x := 18) (dest := 1362)
      hs14h hpc14 hs14Z henc5.1 henc5.2.1 henc5.2.2 (by decide)
  have hle5 : (s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18) = false := by
    have : le0 (s14.mem.get 18) = false := by
      rw [hs14T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs15eq : step s14 = { s14 with pc := 1230 } := by
    have hif :
        (if s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18
          then (1362 : Word) else s14.pc + 3) = (1230 : Word) := by
      have hfall : s14.pc + 3 = (1230 : Word) := by simp [hs14pc]
      simp [hle5, hfall]
    rw [hjlez5, hif]
  have hrun15 : runN s 15 = step s14 := by
    have hS : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    exact hS.trans (runN_one s14 hs14h hpc14)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1230 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]
  have hs15h : s15.halted = false := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14Z
  have hs15T : s15.mem.get 18 = 2 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14T
  have hI15 : s15.mem.get 29 = 7 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hI14
  have hCH15 : s15.mem.get 30 = s.mem.get 30 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hCH14
  have hONE15 : s15.mem.get 3 = 1 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hONE14
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s15 = step s14 := hrun15
    rw [this, hs15eq]; exact hpres14 a ha18 ha0
  have g15 := sc_code_shrink (s := s) (s' := s15) (lo := 1230) (hi := 1233)
    hpres15 hcode (by decide) (by decide)
  have hdec6 := sc_dec_T_1230 (s := s15) hs15pc hs15h g15
  have hs16eq : step s15 =
      { s15 with mem := s15.mem.set 18 (s15.mem.get 18 - s15.mem.get 3), pc := 1233 } := hdec6
  have hrun16 : runN s 16 = step s15 := by
    have hS : runN s 16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
    exact hS.trans (runN_one s15 hs15h (by simp [hs15pc]))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1233 := by have : s16 = step s15 := hrun16; rw [this, hs16eq]
  have hs16h : s16.halted = false := by have : s16 = step s15 := hrun16; rw [this, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 0 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hs15Z
  have hs16T : s16.mem.get 18 = 1 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq, Mem.get_set_eq]
    have h1 : s15.mem.get 18 - s15.mem.get 3 = (2 : Word) - 1 := by
      rw [hs15T, hONE15]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI16 : s16.mem.get 29 = 7 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 29 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hI15
  have hCH16 : s16.mem.get 30 = s.mem.get 30 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 30 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hCH15
  have hONE16 : s16.mem.get 3 = 1 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 3 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hONE15
  have hpres16 : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 a (s15.mem.get 18 - s15.mem.get 3) ha18).trans
      (hpres15 a ha18 ha0)
  have g16 := sc_code_shrink (s := s) (s' := s16) (lo := 1233) (hi := 1236)
    hpres16 hcode (by decide) (by decide)
  have henc6 := sc_enc_jlez_1233 (s := s16) hs16pc g16
  have hpc16 : s16.pc.toNat < 32768 := by simp [hs16pc]
  have hjlez6 :=
    step_JLEZ (s := s16) (x := 18) (dest := 1377)
      hs16h hpc16 hs16Z henc6.1 henc6.2.1 henc6.2.2 (by decide)
  have hle6 : (s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18) = false := by
    have : le0 (s16.mem.get 18) = false := by
      rw [hs16T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs17eq : step s16 = { s16 with pc := 1236 } := by
    have hif :
        (if s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18
          then (1377 : Word) else s16.pc + 3) = (1236 : Word) := by
      have hfall : s16.pc + 3 = (1236 : Word) := by simp [hs16pc]
      simp [hle6, hfall]
    rw [hjlez6, hif]
  have hrun17 : runN s 17 = step s16 := by
    have hS : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
    exact hS.trans (runN_one s16 hs16h hpc16)
  let s17 := runN s 17
  have hs17pc : s17.pc = 1236 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]
  have hs17h : s17.halted = false := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16h
  have hs17Z : s17.mem.get 0 = 0 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16Z
  have hs17T : s17.mem.get 18 = 1 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16T
  have hI17 : s17.mem.get 29 = 7 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hI16
  have hCH17 : s17.mem.get 30 = s.mem.get 30 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hCH16
  have hONE17 : s17.mem.get 3 = 1 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hONE16
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s17 = step s16 := hrun17
    rw [this, hs17eq]; exact hpres16 a ha18 ha0
  have g17 := sc_code_shrink (s := s) (s' := s17) (lo := 1236) (hi := 1239)
    hpres17 hcode (by decide) (by decide)
  have hdec7 := sc_dec_T_1236 (s := s17) hs17pc hs17h g17
  have hs18eq : step s17 =
      { s17 with mem := s17.mem.set 18 (s17.mem.get 18 - s17.mem.get 3), pc := 1239 } := hdec7
  have hrun18 : runN s 18 = step s17 := by
    have hS : runN s 18 = runN s17 1 := runN_add_eq s 17 1 18 (by decide)
    exact hS.trans (runN_one s17 hs17h (by simp [hs17pc]))
  let s18 := runN s 18
  have hs18pc : s18.pc = 1239 := by have : s18 = step s17 := hrun18; rw [this, hs18eq]
  have hs18h : s18.halted = false := by have : s18 = step s17 := hrun18; rw [this, hs18eq]; exact hs17h
  have hs18Z : s18.mem.get 0 = 0 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 0 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hs17Z
  have hs18T : s18.mem.get 18 = 0 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq, Mem.get_set_eq]
    have h1 : s17.mem.get 18 - s17.mem.get 3 = (1 : Word) - 1 := by
      rw [hs17T, hONE17]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI18 : s18.mem.get 29 = 7 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 29 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hI17
  have hCH18 : s18.mem.get 30 = s.mem.get 30 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 30 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hCH17
  have hONE18 : s18.mem.get 3 = 1 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 3 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hONE17
  have hpres18 : ∀ a, a ≠ 18 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 a (s17.mem.get 18 - s17.mem.get 3) ha18).trans
      (hpres17 a ha18 ha0)
  have g18 := sc_code_shrink (s := s) (s' := s18) (lo := 1239) (hi := 1242)
    hpres18 hcode (by decide) (by decide)
  have henc7 := sc_enc_jlez_1239 (s := s18) hs18pc g18
  have hpc18 : s18.pc.toNat < 32768 := by simp [hs18pc]
  have hjlez7 :=
    step_JLEZ (s := s18) (x := 18) (dest := 1392)
      hs18h hpc18 hs18Z henc7.1 henc7.2.1 henc7.2.2 (by decide)
  have hle7 : (s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18) = true := by
    have : le0 (s18.mem.get 18) = true := by
      rw [hs18T]; exact le0_zero
    simpa [le0] using this
  have hs19eq : step s18 = { s18 with pc := 1392 } := by
    have hif :
        (if s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18
          then (1392 : Word) else s18.pc + 3) = (1392 : Word) := by
      simp [hle7]
    rw [hjlez7, hif]
  have hrun19 : runN s 19 = step s18 := by
    have hS : runN s 19 = runN s18 1 := runN_add_eq s 18 1 19 (by decide)
    exact hS.trans (runN_one s18 hs18h hpc18)
  let s19 := runN s 19
  have hs19pc : s19.pc = 1392 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]
  have hs19h : s19.halted = false := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18h
  have hs19Z : s19.mem.get 0 = 0 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18Z
  have hs19T : s19.mem.get 18 = 0 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18T
  have hI19 : s19.mem.get 29 = 7 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hI18
  have hCH19 : s19.mem.get 30 = s.mem.get 30 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hCH18
  have hONE19 : s19.mem.get 3 = 1 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hONE18
  have hpres19 : ∀ a, a ≠ 18 → a ≠ 0 → s19.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s19 = step s18 := hrun19
    rw [this, hs19eq]; exact hpres18 a ha18 ha0
  have g19 := sc_code_shrink (s := s) (s' := s19) (lo := 1392) (hi := 1407)
    hpres19 hcode (by decide) (by decide)
  have hs := st7_store (s := s19) hs19pc hs19h hs19Z g19
  have hrun : sN = runN s19 5 := runN_add_eq s 19 5 24 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 39 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH19
  have hsNI : sN.mem.get 29 = 7 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI19
  have hpres : ∀ a, a ≠ 39 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres19 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 8` at `STORE_CH`: 26 steps to `STORED`, `BUF+8 = CH`. -/
theorem store_ch_idx8 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 8)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 26
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 40 = s.mem.get 30 ∧
    sN.mem.get 29 = 8 ∧
    (∀ a, a ≠ 40 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 8 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 8 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 8 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 8 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 7 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (8 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (8 : Word) - 1 = 7)
  have hI6 : s6.mem.get 29 = 8 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 7 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 8 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 6 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (7 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (7 : Word) - 1 = 6)
  have hI8 : s8.mem.get 29 = 8 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1212 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1212 : Word) := by
      have hfall : s8.pc + 3 = (1212 : Word) := by simp [hs8pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1212 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 6 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 8 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1212) (hi := 1215)
    hpres9 hcode (by decide) (by decide)
  have hdec3 := sc_dec_T_1212 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1215 } := hdec3
  have hrun10 : runN s 10 = step s9 := by
    have hS : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hS.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1215 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : s10.mem.get 18 = 5 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (6 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (6 : Word) - 1 = 5)
  have hI10 : s10.mem.get 29 = 8 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hI9
  have hCH10 : s10.mem.get 30 = s.mem.get 30 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 30 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hCH9
  have hONE10 : s10.mem.get 3 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 3 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have g10 := sc_code_shrink (s := s) (s' := s10) (lo := 1215) (hi := 1218)
    hpres10 hcode (by decide) (by decide)
  have henc3 := sc_enc_jlez_1215 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjlez3 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1332)
      hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = false := by
    have : le0 (s10.mem.get 18) = false := by
      rw [hs10T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq : step s10 = { s10 with pc := 1218 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1332 : Word) else s10.pc + 3) = (1218 : Word) := by
      have hfall : s10.pc + 3 = (1218 : Word) := by simp [hs10pc]
      simp [hle3, hfall]
    rw [hjlez3, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hS : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hS.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1218 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11T : s11.mem.get 18 = 5 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10T
  have hI11 : s11.mem.get 29 = 8 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hI10
  have hCH11 : s11.mem.get 30 = s.mem.get 30 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hCH10
  have hONE11 : s11.mem.get 3 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hONE10
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq]; exact hpres10 a ha18 ha0
  have g11 := sc_code_shrink (s := s) (s' := s11) (lo := 1218) (hi := 1221)
    hpres11 hcode (by decide) (by decide)
  have hdec4 := sc_dec_T_1218 (s := s11) hs11pc hs11h g11
  have hs12eq : step s11 =
      { s11 with mem := s11.mem.set 18 (s11.mem.get 18 - s11.mem.get 3), pc := 1221 } := hdec4
  have hrun12 : runN s 12 = step s11 := by
    have hS : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hS.trans (runN_one s11 hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1221 := by have : s12 = step s11 := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step s11 := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 0 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hs11Z
  have hs12T : s12.mem.get 18 = 4 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq, Mem.get_set_eq]
    have h1 : s11.mem.get 18 - s11.mem.get 3 = (5 : Word) - 1 := by
      rw [hs11T, hONE11]
    exact h1.trans (rfl : (5 : Word) - 1 = 4)
  have hI12 : s12.mem.get 29 = 8 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 29 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hI11
  have hCH12 : s12.mem.get 30 = s.mem.get 30 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 30 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hCH11
  have hONE12 : s12.mem.get 3 = 1 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 3 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hONE11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 a (s11.mem.get 18 - s11.mem.get 3) ha18).trans
      (hpres11 a ha18 ha0)
  have g12 := sc_code_shrink (s := s) (s' := s12) (lo := 1221) (hi := 1224)
    hpres12 hcode (by decide) (by decide)
  have henc4 := sc_enc_jlez_1221 (s := s12) hs12pc g12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hjlez4 :=
    step_JLEZ (s := s12) (x := 18) (dest := 1347)
      hs12h hpc12 hs12Z henc4.1 henc4.2.1 henc4.2.2 (by decide)
  have hle4 : (s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18) = false := by
    have : le0 (s12.mem.get 18) = false := by
      rw [hs12T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs13eq : step s12 = { s12 with pc := 1224 } := by
    have hif :
        (if s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18
          then (1347 : Word) else s12.pc + 3) = (1224 : Word) := by
      have hfall : s12.pc + 3 = (1224 : Word) := by simp [hs12pc]
      simp [hle4, hfall]
    rw [hjlez4, hif]
  have hrun13 : runN s 13 = step s12 := by
    have hS : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    exact hS.trans (runN_one s12 hs12h hpc12)
  let s13 := runN s 13
  have hs13pc : s13.pc = 1224 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]
  have hs13h : s13.halted = false := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12Z
  have hs13T : s13.mem.get 18 = 4 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12T
  have hI13 : s13.mem.get 29 = 8 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hI12
  have hCH13 : s13.mem.get 30 = s.mem.get 30 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hCH12
  have hONE13 : s13.mem.get 3 = 1 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hONE12
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s13 = step s12 := hrun13
    rw [this, hs13eq]; exact hpres12 a ha18 ha0
  have g13 := sc_code_shrink (s := s) (s' := s13) (lo := 1224) (hi := 1227)
    hpres13 hcode (by decide) (by decide)
  have hdec5 := sc_dec_T_1224 (s := s13) hs13pc hs13h g13
  have hs14eq : step s13 =
      { s13 with mem := s13.mem.set 18 (s13.mem.get 18 - s13.mem.get 3), pc := 1227 } := hdec5
  have hrun14 : runN s 14 = step s13 := by
    have hS : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hS.trans (runN_one s13 hs13h (by simp [hs13pc]))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1227 := by have : s14 = step s13 := hrun14; rw [this, hs14eq]
  have hs14h : s14.halted = false := by have : s14 = step s13 := hrun14; rw [this, hs14eq]; exact hs13h
  have hs14Z : s14.mem.get 0 = 0 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 0 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hs13Z
  have hs14T : s14.mem.get 18 = 3 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq, Mem.get_set_eq]
    have h1 : s13.mem.get 18 - s13.mem.get 3 = (4 : Word) - 1 := by
      rw [hs13T, hONE13]
    exact h1.trans (rfl : (4 : Word) - 1 = 3)
  have hI14 : s14.mem.get 29 = 8 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 29 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hI13
  have hCH14 : s14.mem.get 30 = s.mem.get 30 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 30 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hCH13
  have hONE14 : s14.mem.get 3 = 1 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 3 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hONE13
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 a (s13.mem.get 18 - s13.mem.get 3) ha18).trans
      (hpres13 a ha18 ha0)
  have g14 := sc_code_shrink (s := s) (s' := s14) (lo := 1227) (hi := 1230)
    hpres14 hcode (by decide) (by decide)
  have henc5 := sc_enc_jlez_1227 (s := s14) hs14pc g14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hjlez5 :=
    step_JLEZ (s := s14) (x := 18) (dest := 1362)
      hs14h hpc14 hs14Z henc5.1 henc5.2.1 henc5.2.2 (by decide)
  have hle5 : (s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18) = false := by
    have : le0 (s14.mem.get 18) = false := by
      rw [hs14T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs15eq : step s14 = { s14 with pc := 1230 } := by
    have hif :
        (if s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18
          then (1362 : Word) else s14.pc + 3) = (1230 : Word) := by
      have hfall : s14.pc + 3 = (1230 : Word) := by simp [hs14pc]
      simp [hle5, hfall]
    rw [hjlez5, hif]
  have hrun15 : runN s 15 = step s14 := by
    have hS : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    exact hS.trans (runN_one s14 hs14h hpc14)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1230 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]
  have hs15h : s15.halted = false := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14Z
  have hs15T : s15.mem.get 18 = 3 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14T
  have hI15 : s15.mem.get 29 = 8 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hI14
  have hCH15 : s15.mem.get 30 = s.mem.get 30 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hCH14
  have hONE15 : s15.mem.get 3 = 1 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hONE14
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s15 = step s14 := hrun15
    rw [this, hs15eq]; exact hpres14 a ha18 ha0
  have g15 := sc_code_shrink (s := s) (s' := s15) (lo := 1230) (hi := 1233)
    hpres15 hcode (by decide) (by decide)
  have hdec6 := sc_dec_T_1230 (s := s15) hs15pc hs15h g15
  have hs16eq : step s15 =
      { s15 with mem := s15.mem.set 18 (s15.mem.get 18 - s15.mem.get 3), pc := 1233 } := hdec6
  have hrun16 : runN s 16 = step s15 := by
    have hS : runN s 16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
    exact hS.trans (runN_one s15 hs15h (by simp [hs15pc]))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1233 := by have : s16 = step s15 := hrun16; rw [this, hs16eq]
  have hs16h : s16.halted = false := by have : s16 = step s15 := hrun16; rw [this, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 0 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hs15Z
  have hs16T : s16.mem.get 18 = 2 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq, Mem.get_set_eq]
    have h1 : s15.mem.get 18 - s15.mem.get 3 = (3 : Word) - 1 := by
      rw [hs15T, hONE15]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hI16 : s16.mem.get 29 = 8 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 29 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hI15
  have hCH16 : s16.mem.get 30 = s.mem.get 30 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 30 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hCH15
  have hONE16 : s16.mem.get 3 = 1 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 3 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hONE15
  have hpres16 : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 a (s15.mem.get 18 - s15.mem.get 3) ha18).trans
      (hpres15 a ha18 ha0)
  have g16 := sc_code_shrink (s := s) (s' := s16) (lo := 1233) (hi := 1236)
    hpres16 hcode (by decide) (by decide)
  have henc6 := sc_enc_jlez_1233 (s := s16) hs16pc g16
  have hpc16 : s16.pc.toNat < 32768 := by simp [hs16pc]
  have hjlez6 :=
    step_JLEZ (s := s16) (x := 18) (dest := 1377)
      hs16h hpc16 hs16Z henc6.1 henc6.2.1 henc6.2.2 (by decide)
  have hle6 : (s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18) = false := by
    have : le0 (s16.mem.get 18) = false := by
      rw [hs16T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs17eq : step s16 = { s16 with pc := 1236 } := by
    have hif :
        (if s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18
          then (1377 : Word) else s16.pc + 3) = (1236 : Word) := by
      have hfall : s16.pc + 3 = (1236 : Word) := by simp [hs16pc]
      simp [hle6, hfall]
    rw [hjlez6, hif]
  have hrun17 : runN s 17 = step s16 := by
    have hS : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
    exact hS.trans (runN_one s16 hs16h hpc16)
  let s17 := runN s 17
  have hs17pc : s17.pc = 1236 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]
  have hs17h : s17.halted = false := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16h
  have hs17Z : s17.mem.get 0 = 0 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16Z
  have hs17T : s17.mem.get 18 = 2 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16T
  have hI17 : s17.mem.get 29 = 8 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hI16
  have hCH17 : s17.mem.get 30 = s.mem.get 30 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hCH16
  have hONE17 : s17.mem.get 3 = 1 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hONE16
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s17 = step s16 := hrun17
    rw [this, hs17eq]; exact hpres16 a ha18 ha0
  have g17 := sc_code_shrink (s := s) (s' := s17) (lo := 1236) (hi := 1239)
    hpres17 hcode (by decide) (by decide)
  have hdec7 := sc_dec_T_1236 (s := s17) hs17pc hs17h g17
  have hs18eq : step s17 =
      { s17 with mem := s17.mem.set 18 (s17.mem.get 18 - s17.mem.get 3), pc := 1239 } := hdec7
  have hrun18 : runN s 18 = step s17 := by
    have hS : runN s 18 = runN s17 1 := runN_add_eq s 17 1 18 (by decide)
    exact hS.trans (runN_one s17 hs17h (by simp [hs17pc]))
  let s18 := runN s 18
  have hs18pc : s18.pc = 1239 := by have : s18 = step s17 := hrun18; rw [this, hs18eq]
  have hs18h : s18.halted = false := by have : s18 = step s17 := hrun18; rw [this, hs18eq]; exact hs17h
  have hs18Z : s18.mem.get 0 = 0 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 0 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hs17Z
  have hs18T : s18.mem.get 18 = 1 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq, Mem.get_set_eq]
    have h1 : s17.mem.get 18 - s17.mem.get 3 = (2 : Word) - 1 := by
      rw [hs17T, hONE17]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI18 : s18.mem.get 29 = 8 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 29 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hI17
  have hCH18 : s18.mem.get 30 = s.mem.get 30 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 30 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hCH17
  have hONE18 : s18.mem.get 3 = 1 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 3 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hONE17
  have hpres18 : ∀ a, a ≠ 18 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 a (s17.mem.get 18 - s17.mem.get 3) ha18).trans
      (hpres17 a ha18 ha0)
  have g18 := sc_code_shrink (s := s) (s' := s18) (lo := 1239) (hi := 1242)
    hpres18 hcode (by decide) (by decide)
  have henc7 := sc_enc_jlez_1239 (s := s18) hs18pc g18
  have hpc18 : s18.pc.toNat < 32768 := by simp [hs18pc]
  have hjlez7 :=
    step_JLEZ (s := s18) (x := 18) (dest := 1392)
      hs18h hpc18 hs18Z henc7.1 henc7.2.1 henc7.2.2 (by decide)
  have hle7 : (s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18) = false := by
    have : le0 (s18.mem.get 18) = false := by
      rw [hs18T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs19eq : step s18 = { s18 with pc := 1242 } := by
    have hif :
        (if s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18
          then (1392 : Word) else s18.pc + 3) = (1242 : Word) := by
      have hfall : s18.pc + 3 = (1242 : Word) := by simp [hs18pc]
      simp [hle7, hfall]
    rw [hjlez7, hif]
  have hrun19 : runN s 19 = step s18 := by
    have hS : runN s 19 = runN s18 1 := runN_add_eq s 18 1 19 (by decide)
    exact hS.trans (runN_one s18 hs18h hpc18)
  let s19 := runN s 19
  have hs19pc : s19.pc = 1242 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]
  have hs19h : s19.halted = false := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18h
  have hs19Z : s19.mem.get 0 = 0 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18Z
  have hs19T : s19.mem.get 18 = 1 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18T
  have hI19 : s19.mem.get 29 = 8 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hI18
  have hCH19 : s19.mem.get 30 = s.mem.get 30 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hCH18
  have hONE19 : s19.mem.get 3 = 1 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hONE18
  have hpres19 : ∀ a, a ≠ 18 → a ≠ 0 → s19.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s19 = step s18 := hrun19
    rw [this, hs19eq]; exact hpres18 a ha18 ha0
  have g19 := sc_code_shrink (s := s) (s' := s19) (lo := 1242) (hi := 1245)
    hpres19 hcode (by decide) (by decide)
  have hdec8 := sc_dec_T_1242 (s := s19) hs19pc hs19h g19
  have hs20eq : step s19 =
      { s19 with mem := s19.mem.set 18 (s19.mem.get 18 - s19.mem.get 3), pc := 1245 } := hdec8
  have hrun20 : runN s 20 = step s19 := by
    have hS : runN s 20 = runN s19 1 := runN_add_eq s 19 1 20 (by decide)
    exact hS.trans (runN_one s19 hs19h (by simp [hs19pc]))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1245 := by have : s20 = step s19 := hrun20; rw [this, hs20eq]
  have hs20h : s20.halted = false := by have : s20 = step s19 := hrun20; rw [this, hs20eq]; exact hs19h
  have hs20Z : s20.mem.get 0 = 0 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 0 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hs19Z
  have hs20T : s20.mem.get 18 = 0 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq, Mem.get_set_eq]
    have h1 : s19.mem.get 18 - s19.mem.get 3 = (1 : Word) - 1 := by
      rw [hs19T, hONE19]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI20 : s20.mem.get 29 = 8 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 29 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hI19
  have hCH20 : s20.mem.get 30 = s.mem.get 30 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 30 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hCH19
  have hONE20 : s20.mem.get 3 = 1 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 3 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hONE19
  have hpres20 : ∀ a, a ≠ 18 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 a (s19.mem.get 18 - s19.mem.get 3) ha18).trans
      (hpres19 a ha18 ha0)
  have g20 := sc_code_shrink (s := s) (s' := s20) (lo := 1245) (hi := 1248)
    hpres20 hcode (by decide) (by decide)
  have henc8 := sc_enc_jlez_1245 (s := s20) hs20pc g20
  have hpc20 : s20.pc.toNat < 32768 := by simp [hs20pc]
  have hjlez8 :=
    step_JLEZ (s := s20) (x := 18) (dest := 1407)
      hs20h hpc20 hs20Z henc8.1 henc8.2.1 henc8.2.2 (by decide)
  have hle8 : (s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18) = true := by
    have : le0 (s20.mem.get 18) = true := by
      rw [hs20T]; exact le0_zero
    simpa [le0] using this
  have hs21eq : step s20 = { s20 with pc := 1407 } := by
    have hif :
        (if s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18
          then (1407 : Word) else s20.pc + 3) = (1407 : Word) := by
      simp [hle8]
    rw [hjlez8, hif]
  have hrun21 : runN s 21 = step s20 := by
    have hS : runN s 21 = runN s20 1 := runN_add_eq s 20 1 21 (by decide)
    exact hS.trans (runN_one s20 hs20h hpc20)
  let s21 := runN s 21
  have hs21pc : s21.pc = 1407 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]
  have hs21h : s21.halted = false := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20h
  have hs21Z : s21.mem.get 0 = 0 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20Z
  have hs21T : s21.mem.get 18 = 0 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20T
  have hI21 : s21.mem.get 29 = 8 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hI20
  have hCH21 : s21.mem.get 30 = s.mem.get 30 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hCH20
  have hONE21 : s21.mem.get 3 = 1 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hONE20
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s21 = step s20 := hrun21
    rw [this, hs21eq]; exact hpres20 a ha18 ha0
  have g21 := sc_code_shrink (s := s) (s' := s21) (lo := 1407) (hi := 1422)
    hpres21 hcode (by decide) (by decide)
  have hs := st8_store (s := s21) hs21pc hs21h hs21Z g21
  have hrun : sN = runN s21 5 := runN_add_eq s 21 5 26 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 40 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH21
  have hsNI : sN.mem.get 29 = 8 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI21
  have hpres : ∀ a, a ≠ 40 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres21 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 9` at `STORE_CH`: 28 steps to `STORED`, `BUF+9 = CH`. -/
theorem store_ch_idx9 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 9)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 28
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 41 = s.mem.get 30 ∧
    sN.mem.get 29 = 9 ∧
    (∀ a, a ≠ 41 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 9 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 9 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 9 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 9 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 8 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (9 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (9 : Word) - 1 = 8)
  have hI6 : s6.mem.get 29 = 9 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 8 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 9 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 7 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (8 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (8 : Word) - 1 = 7)
  have hI8 : s8.mem.get 29 = 9 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1212 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1212 : Word) := by
      have hfall : s8.pc + 3 = (1212 : Word) := by simp [hs8pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1212 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 7 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 9 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1212) (hi := 1215)
    hpres9 hcode (by decide) (by decide)
  have hdec3 := sc_dec_T_1212 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1215 } := hdec3
  have hrun10 : runN s 10 = step s9 := by
    have hS : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hS.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1215 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : s10.mem.get 18 = 6 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (7 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (7 : Word) - 1 = 6)
  have hI10 : s10.mem.get 29 = 9 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hI9
  have hCH10 : s10.mem.get 30 = s.mem.get 30 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 30 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hCH9
  have hONE10 : s10.mem.get 3 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 3 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have g10 := sc_code_shrink (s := s) (s' := s10) (lo := 1215) (hi := 1218)
    hpres10 hcode (by decide) (by decide)
  have henc3 := sc_enc_jlez_1215 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjlez3 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1332)
      hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = false := by
    have : le0 (s10.mem.get 18) = false := by
      rw [hs10T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq : step s10 = { s10 with pc := 1218 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1332 : Word) else s10.pc + 3) = (1218 : Word) := by
      have hfall : s10.pc + 3 = (1218 : Word) := by simp [hs10pc]
      simp [hle3, hfall]
    rw [hjlez3, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hS : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hS.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1218 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11T : s11.mem.get 18 = 6 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10T
  have hI11 : s11.mem.get 29 = 9 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hI10
  have hCH11 : s11.mem.get 30 = s.mem.get 30 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hCH10
  have hONE11 : s11.mem.get 3 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hONE10
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq]; exact hpres10 a ha18 ha0
  have g11 := sc_code_shrink (s := s) (s' := s11) (lo := 1218) (hi := 1221)
    hpres11 hcode (by decide) (by decide)
  have hdec4 := sc_dec_T_1218 (s := s11) hs11pc hs11h g11
  have hs12eq : step s11 =
      { s11 with mem := s11.mem.set 18 (s11.mem.get 18 - s11.mem.get 3), pc := 1221 } := hdec4
  have hrun12 : runN s 12 = step s11 := by
    have hS : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hS.trans (runN_one s11 hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1221 := by have : s12 = step s11 := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step s11 := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 0 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hs11Z
  have hs12T : s12.mem.get 18 = 5 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq, Mem.get_set_eq]
    have h1 : s11.mem.get 18 - s11.mem.get 3 = (6 : Word) - 1 := by
      rw [hs11T, hONE11]
    exact h1.trans (rfl : (6 : Word) - 1 = 5)
  have hI12 : s12.mem.get 29 = 9 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 29 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hI11
  have hCH12 : s12.mem.get 30 = s.mem.get 30 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 30 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hCH11
  have hONE12 : s12.mem.get 3 = 1 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 3 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hONE11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 a (s11.mem.get 18 - s11.mem.get 3) ha18).trans
      (hpres11 a ha18 ha0)
  have g12 := sc_code_shrink (s := s) (s' := s12) (lo := 1221) (hi := 1224)
    hpres12 hcode (by decide) (by decide)
  have henc4 := sc_enc_jlez_1221 (s := s12) hs12pc g12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hjlez4 :=
    step_JLEZ (s := s12) (x := 18) (dest := 1347)
      hs12h hpc12 hs12Z henc4.1 henc4.2.1 henc4.2.2 (by decide)
  have hle4 : (s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18) = false := by
    have : le0 (s12.mem.get 18) = false := by
      rw [hs12T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs13eq : step s12 = { s12 with pc := 1224 } := by
    have hif :
        (if s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18
          then (1347 : Word) else s12.pc + 3) = (1224 : Word) := by
      have hfall : s12.pc + 3 = (1224 : Word) := by simp [hs12pc]
      simp [hle4, hfall]
    rw [hjlez4, hif]
  have hrun13 : runN s 13 = step s12 := by
    have hS : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    exact hS.trans (runN_one s12 hs12h hpc12)
  let s13 := runN s 13
  have hs13pc : s13.pc = 1224 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]
  have hs13h : s13.halted = false := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12Z
  have hs13T : s13.mem.get 18 = 5 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12T
  have hI13 : s13.mem.get 29 = 9 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hI12
  have hCH13 : s13.mem.get 30 = s.mem.get 30 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hCH12
  have hONE13 : s13.mem.get 3 = 1 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hONE12
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s13 = step s12 := hrun13
    rw [this, hs13eq]; exact hpres12 a ha18 ha0
  have g13 := sc_code_shrink (s := s) (s' := s13) (lo := 1224) (hi := 1227)
    hpres13 hcode (by decide) (by decide)
  have hdec5 := sc_dec_T_1224 (s := s13) hs13pc hs13h g13
  have hs14eq : step s13 =
      { s13 with mem := s13.mem.set 18 (s13.mem.get 18 - s13.mem.get 3), pc := 1227 } := hdec5
  have hrun14 : runN s 14 = step s13 := by
    have hS : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hS.trans (runN_one s13 hs13h (by simp [hs13pc]))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1227 := by have : s14 = step s13 := hrun14; rw [this, hs14eq]
  have hs14h : s14.halted = false := by have : s14 = step s13 := hrun14; rw [this, hs14eq]; exact hs13h
  have hs14Z : s14.mem.get 0 = 0 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 0 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hs13Z
  have hs14T : s14.mem.get 18 = 4 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq, Mem.get_set_eq]
    have h1 : s13.mem.get 18 - s13.mem.get 3 = (5 : Word) - 1 := by
      rw [hs13T, hONE13]
    exact h1.trans (rfl : (5 : Word) - 1 = 4)
  have hI14 : s14.mem.get 29 = 9 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 29 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hI13
  have hCH14 : s14.mem.get 30 = s.mem.get 30 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 30 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hCH13
  have hONE14 : s14.mem.get 3 = 1 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 3 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hONE13
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 a (s13.mem.get 18 - s13.mem.get 3) ha18).trans
      (hpres13 a ha18 ha0)
  have g14 := sc_code_shrink (s := s) (s' := s14) (lo := 1227) (hi := 1230)
    hpres14 hcode (by decide) (by decide)
  have henc5 := sc_enc_jlez_1227 (s := s14) hs14pc g14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hjlez5 :=
    step_JLEZ (s := s14) (x := 18) (dest := 1362)
      hs14h hpc14 hs14Z henc5.1 henc5.2.1 henc5.2.2 (by decide)
  have hle5 : (s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18) = false := by
    have : le0 (s14.mem.get 18) = false := by
      rw [hs14T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs15eq : step s14 = { s14 with pc := 1230 } := by
    have hif :
        (if s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18
          then (1362 : Word) else s14.pc + 3) = (1230 : Word) := by
      have hfall : s14.pc + 3 = (1230 : Word) := by simp [hs14pc]
      simp [hle5, hfall]
    rw [hjlez5, hif]
  have hrun15 : runN s 15 = step s14 := by
    have hS : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    exact hS.trans (runN_one s14 hs14h hpc14)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1230 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]
  have hs15h : s15.halted = false := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14Z
  have hs15T : s15.mem.get 18 = 4 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14T
  have hI15 : s15.mem.get 29 = 9 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hI14
  have hCH15 : s15.mem.get 30 = s.mem.get 30 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hCH14
  have hONE15 : s15.mem.get 3 = 1 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hONE14
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s15 = step s14 := hrun15
    rw [this, hs15eq]; exact hpres14 a ha18 ha0
  have g15 := sc_code_shrink (s := s) (s' := s15) (lo := 1230) (hi := 1233)
    hpres15 hcode (by decide) (by decide)
  have hdec6 := sc_dec_T_1230 (s := s15) hs15pc hs15h g15
  have hs16eq : step s15 =
      { s15 with mem := s15.mem.set 18 (s15.mem.get 18 - s15.mem.get 3), pc := 1233 } := hdec6
  have hrun16 : runN s 16 = step s15 := by
    have hS : runN s 16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
    exact hS.trans (runN_one s15 hs15h (by simp [hs15pc]))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1233 := by have : s16 = step s15 := hrun16; rw [this, hs16eq]
  have hs16h : s16.halted = false := by have : s16 = step s15 := hrun16; rw [this, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 0 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hs15Z
  have hs16T : s16.mem.get 18 = 3 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq, Mem.get_set_eq]
    have h1 : s15.mem.get 18 - s15.mem.get 3 = (4 : Word) - 1 := by
      rw [hs15T, hONE15]
    exact h1.trans (rfl : (4 : Word) - 1 = 3)
  have hI16 : s16.mem.get 29 = 9 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 29 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hI15
  have hCH16 : s16.mem.get 30 = s.mem.get 30 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 30 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hCH15
  have hONE16 : s16.mem.get 3 = 1 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 3 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hONE15
  have hpres16 : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 a (s15.mem.get 18 - s15.mem.get 3) ha18).trans
      (hpres15 a ha18 ha0)
  have g16 := sc_code_shrink (s := s) (s' := s16) (lo := 1233) (hi := 1236)
    hpres16 hcode (by decide) (by decide)
  have henc6 := sc_enc_jlez_1233 (s := s16) hs16pc g16
  have hpc16 : s16.pc.toNat < 32768 := by simp [hs16pc]
  have hjlez6 :=
    step_JLEZ (s := s16) (x := 18) (dest := 1377)
      hs16h hpc16 hs16Z henc6.1 henc6.2.1 henc6.2.2 (by decide)
  have hle6 : (s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18) = false := by
    have : le0 (s16.mem.get 18) = false := by
      rw [hs16T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs17eq : step s16 = { s16 with pc := 1236 } := by
    have hif :
        (if s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18
          then (1377 : Word) else s16.pc + 3) = (1236 : Word) := by
      have hfall : s16.pc + 3 = (1236 : Word) := by simp [hs16pc]
      simp [hle6, hfall]
    rw [hjlez6, hif]
  have hrun17 : runN s 17 = step s16 := by
    have hS : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
    exact hS.trans (runN_one s16 hs16h hpc16)
  let s17 := runN s 17
  have hs17pc : s17.pc = 1236 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]
  have hs17h : s17.halted = false := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16h
  have hs17Z : s17.mem.get 0 = 0 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16Z
  have hs17T : s17.mem.get 18 = 3 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16T
  have hI17 : s17.mem.get 29 = 9 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hI16
  have hCH17 : s17.mem.get 30 = s.mem.get 30 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hCH16
  have hONE17 : s17.mem.get 3 = 1 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hONE16
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s17 = step s16 := hrun17
    rw [this, hs17eq]; exact hpres16 a ha18 ha0
  have g17 := sc_code_shrink (s := s) (s' := s17) (lo := 1236) (hi := 1239)
    hpres17 hcode (by decide) (by decide)
  have hdec7 := sc_dec_T_1236 (s := s17) hs17pc hs17h g17
  have hs18eq : step s17 =
      { s17 with mem := s17.mem.set 18 (s17.mem.get 18 - s17.mem.get 3), pc := 1239 } := hdec7
  have hrun18 : runN s 18 = step s17 := by
    have hS : runN s 18 = runN s17 1 := runN_add_eq s 17 1 18 (by decide)
    exact hS.trans (runN_one s17 hs17h (by simp [hs17pc]))
  let s18 := runN s 18
  have hs18pc : s18.pc = 1239 := by have : s18 = step s17 := hrun18; rw [this, hs18eq]
  have hs18h : s18.halted = false := by have : s18 = step s17 := hrun18; rw [this, hs18eq]; exact hs17h
  have hs18Z : s18.mem.get 0 = 0 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 0 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hs17Z
  have hs18T : s18.mem.get 18 = 2 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq, Mem.get_set_eq]
    have h1 : s17.mem.get 18 - s17.mem.get 3 = (3 : Word) - 1 := by
      rw [hs17T, hONE17]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hI18 : s18.mem.get 29 = 9 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 29 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hI17
  have hCH18 : s18.mem.get 30 = s.mem.get 30 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 30 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hCH17
  have hONE18 : s18.mem.get 3 = 1 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 3 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hONE17
  have hpres18 : ∀ a, a ≠ 18 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 a (s17.mem.get 18 - s17.mem.get 3) ha18).trans
      (hpres17 a ha18 ha0)
  have g18 := sc_code_shrink (s := s) (s' := s18) (lo := 1239) (hi := 1242)
    hpres18 hcode (by decide) (by decide)
  have henc7 := sc_enc_jlez_1239 (s := s18) hs18pc g18
  have hpc18 : s18.pc.toNat < 32768 := by simp [hs18pc]
  have hjlez7 :=
    step_JLEZ (s := s18) (x := 18) (dest := 1392)
      hs18h hpc18 hs18Z henc7.1 henc7.2.1 henc7.2.2 (by decide)
  have hle7 : (s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18) = false := by
    have : le0 (s18.mem.get 18) = false := by
      rw [hs18T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs19eq : step s18 = { s18 with pc := 1242 } := by
    have hif :
        (if s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18
          then (1392 : Word) else s18.pc + 3) = (1242 : Word) := by
      have hfall : s18.pc + 3 = (1242 : Word) := by simp [hs18pc]
      simp [hle7, hfall]
    rw [hjlez7, hif]
  have hrun19 : runN s 19 = step s18 := by
    have hS : runN s 19 = runN s18 1 := runN_add_eq s 18 1 19 (by decide)
    exact hS.trans (runN_one s18 hs18h hpc18)
  let s19 := runN s 19
  have hs19pc : s19.pc = 1242 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]
  have hs19h : s19.halted = false := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18h
  have hs19Z : s19.mem.get 0 = 0 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18Z
  have hs19T : s19.mem.get 18 = 2 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18T
  have hI19 : s19.mem.get 29 = 9 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hI18
  have hCH19 : s19.mem.get 30 = s.mem.get 30 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hCH18
  have hONE19 : s19.mem.get 3 = 1 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hONE18
  have hpres19 : ∀ a, a ≠ 18 → a ≠ 0 → s19.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s19 = step s18 := hrun19
    rw [this, hs19eq]; exact hpres18 a ha18 ha0
  have g19 := sc_code_shrink (s := s) (s' := s19) (lo := 1242) (hi := 1245)
    hpres19 hcode (by decide) (by decide)
  have hdec8 := sc_dec_T_1242 (s := s19) hs19pc hs19h g19
  have hs20eq : step s19 =
      { s19 with mem := s19.mem.set 18 (s19.mem.get 18 - s19.mem.get 3), pc := 1245 } := hdec8
  have hrun20 : runN s 20 = step s19 := by
    have hS : runN s 20 = runN s19 1 := runN_add_eq s 19 1 20 (by decide)
    exact hS.trans (runN_one s19 hs19h (by simp [hs19pc]))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1245 := by have : s20 = step s19 := hrun20; rw [this, hs20eq]
  have hs20h : s20.halted = false := by have : s20 = step s19 := hrun20; rw [this, hs20eq]; exact hs19h
  have hs20Z : s20.mem.get 0 = 0 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 0 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hs19Z
  have hs20T : s20.mem.get 18 = 1 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq, Mem.get_set_eq]
    have h1 : s19.mem.get 18 - s19.mem.get 3 = (2 : Word) - 1 := by
      rw [hs19T, hONE19]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI20 : s20.mem.get 29 = 9 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 29 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hI19
  have hCH20 : s20.mem.get 30 = s.mem.get 30 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 30 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hCH19
  have hONE20 : s20.mem.get 3 = 1 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 3 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hONE19
  have hpres20 : ∀ a, a ≠ 18 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 a (s19.mem.get 18 - s19.mem.get 3) ha18).trans
      (hpres19 a ha18 ha0)
  have g20 := sc_code_shrink (s := s) (s' := s20) (lo := 1245) (hi := 1248)
    hpres20 hcode (by decide) (by decide)
  have henc8 := sc_enc_jlez_1245 (s := s20) hs20pc g20
  have hpc20 : s20.pc.toNat < 32768 := by simp [hs20pc]
  have hjlez8 :=
    step_JLEZ (s := s20) (x := 18) (dest := 1407)
      hs20h hpc20 hs20Z henc8.1 henc8.2.1 henc8.2.2 (by decide)
  have hle8 : (s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18) = false := by
    have : le0 (s20.mem.get 18) = false := by
      rw [hs20T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs21eq : step s20 = { s20 with pc := 1248 } := by
    have hif :
        (if s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18
          then (1407 : Word) else s20.pc + 3) = (1248 : Word) := by
      have hfall : s20.pc + 3 = (1248 : Word) := by simp [hs20pc]
      simp [hle8, hfall]
    rw [hjlez8, hif]
  have hrun21 : runN s 21 = step s20 := by
    have hS : runN s 21 = runN s20 1 := runN_add_eq s 20 1 21 (by decide)
    exact hS.trans (runN_one s20 hs20h hpc20)
  let s21 := runN s 21
  have hs21pc : s21.pc = 1248 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]
  have hs21h : s21.halted = false := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20h
  have hs21Z : s21.mem.get 0 = 0 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20Z
  have hs21T : s21.mem.get 18 = 1 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20T
  have hI21 : s21.mem.get 29 = 9 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hI20
  have hCH21 : s21.mem.get 30 = s.mem.get 30 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hCH20
  have hONE21 : s21.mem.get 3 = 1 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hONE20
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s21 = step s20 := hrun21
    rw [this, hs21eq]; exact hpres20 a ha18 ha0
  have g21 := sc_code_shrink (s := s) (s' := s21) (lo := 1248) (hi := 1251)
    hpres21 hcode (by decide) (by decide)
  have hdec9 := sc_dec_T_1248 (s := s21) hs21pc hs21h g21
  have hs22eq : step s21 =
      { s21 with mem := s21.mem.set 18 (s21.mem.get 18 - s21.mem.get 3), pc := 1251 } := hdec9
  have hrun22 : runN s 22 = step s21 := by
    have hS : runN s 22 = runN s21 1 := runN_add_eq s 21 1 22 (by decide)
    exact hS.trans (runN_one s21 hs21h (by simp [hs21pc]))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1251 := by have : s22 = step s21 := hrun22; rw [this, hs22eq]
  have hs22h : s22.halted = false := by have : s22 = step s21 := hrun22; rw [this, hs22eq]; exact hs21h
  have hs22Z : s22.mem.get 0 = 0 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 0 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hs21Z
  have hs22T : s22.mem.get 18 = 0 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq, Mem.get_set_eq]
    have h1 : s21.mem.get 18 - s21.mem.get 3 = (1 : Word) - 1 := by
      rw [hs21T, hONE21]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI22 : s22.mem.get 29 = 9 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 29 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hI21
  have hCH22 : s22.mem.get 30 = s.mem.get 30 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 30 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hCH21
  have hONE22 : s22.mem.get 3 = 1 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 3 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hONE21
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 0 → s22.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 a (s21.mem.get 18 - s21.mem.get 3) ha18).trans
      (hpres21 a ha18 ha0)
  have g22 := sc_code_shrink (s := s) (s' := s22) (lo := 1251) (hi := 1254)
    hpres22 hcode (by decide) (by decide)
  have henc9 := sc_enc_jlez_1251 (s := s22) hs22pc g22
  have hpc22 : s22.pc.toNat < 32768 := by simp [hs22pc]
  have hjlez9 :=
    step_JLEZ (s := s22) (x := 18) (dest := 1422)
      hs22h hpc22 hs22Z henc9.1 henc9.2.1 henc9.2.2 (by decide)
  have hle9 : (s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18) = true := by
    have : le0 (s22.mem.get 18) = true := by
      rw [hs22T]; exact le0_zero
    simpa [le0] using this
  have hs23eq : step s22 = { s22 with pc := 1422 } := by
    have hif :
        (if s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18
          then (1422 : Word) else s22.pc + 3) = (1422 : Word) := by
      simp [hle9]
    rw [hjlez9, hif]
  have hrun23 : runN s 23 = step s22 := by
    have hS : runN s 23 = runN s22 1 := runN_add_eq s 22 1 23 (by decide)
    exact hS.trans (runN_one s22 hs22h hpc22)
  let s23 := runN s 23
  have hs23pc : s23.pc = 1422 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]
  have hs23h : s23.halted = false := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22h
  have hs23Z : s23.mem.get 0 = 0 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22Z
  have hs23T : s23.mem.get 18 = 0 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22T
  have hI23 : s23.mem.get 29 = 9 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hI22
  have hCH23 : s23.mem.get 30 = s.mem.get 30 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hCH22
  have hONE23 : s23.mem.get 3 = 1 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hONE22
  have hpres23 : ∀ a, a ≠ 18 → a ≠ 0 → s23.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s23 = step s22 := hrun23
    rw [this, hs23eq]; exact hpres22 a ha18 ha0
  have g23 := sc_code_shrink (s := s) (s' := s23) (lo := 1422) (hi := 1437)
    hpres23 hcode (by decide) (by decide)
  have hs := st9_store (s := s23) hs23pc hs23h hs23Z g23
  have hrun : sN = runN s23 5 := runN_add_eq s 23 5 28 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 41 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH23
  have hsNI : sN.mem.get 29 = 9 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI23
  have hpres : ∀ a, a ≠ 41 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres23 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 10` at `STORE_CH`: 30 steps to `STORED`, `BUF+10 = CH`. -/
theorem store_ch_idx10 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 10)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 30
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 42 = s.mem.get 30 ∧
    sN.mem.get 29 = 10 ∧
    (∀ a, a ≠ 42 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 10 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 10 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 10 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 10 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 9 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (10 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (10 : Word) - 1 = 9)
  have hI6 : s6.mem.get 29 = 10 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 9 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 10 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 8 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (9 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (9 : Word) - 1 = 8)
  have hI8 : s8.mem.get 29 = 10 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1212 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1212 : Word) := by
      have hfall : s8.pc + 3 = (1212 : Word) := by simp [hs8pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1212 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 8 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 10 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1212) (hi := 1215)
    hpres9 hcode (by decide) (by decide)
  have hdec3 := sc_dec_T_1212 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1215 } := hdec3
  have hrun10 : runN s 10 = step s9 := by
    have hS : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hS.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1215 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : s10.mem.get 18 = 7 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (8 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (8 : Word) - 1 = 7)
  have hI10 : s10.mem.get 29 = 10 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hI9
  have hCH10 : s10.mem.get 30 = s.mem.get 30 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 30 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hCH9
  have hONE10 : s10.mem.get 3 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 3 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have g10 := sc_code_shrink (s := s) (s' := s10) (lo := 1215) (hi := 1218)
    hpres10 hcode (by decide) (by decide)
  have henc3 := sc_enc_jlez_1215 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjlez3 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1332)
      hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = false := by
    have : le0 (s10.mem.get 18) = false := by
      rw [hs10T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq : step s10 = { s10 with pc := 1218 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1332 : Word) else s10.pc + 3) = (1218 : Word) := by
      have hfall : s10.pc + 3 = (1218 : Word) := by simp [hs10pc]
      simp [hle3, hfall]
    rw [hjlez3, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hS : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hS.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1218 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11T : s11.mem.get 18 = 7 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10T
  have hI11 : s11.mem.get 29 = 10 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hI10
  have hCH11 : s11.mem.get 30 = s.mem.get 30 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hCH10
  have hONE11 : s11.mem.get 3 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hONE10
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq]; exact hpres10 a ha18 ha0
  have g11 := sc_code_shrink (s := s) (s' := s11) (lo := 1218) (hi := 1221)
    hpres11 hcode (by decide) (by decide)
  have hdec4 := sc_dec_T_1218 (s := s11) hs11pc hs11h g11
  have hs12eq : step s11 =
      { s11 with mem := s11.mem.set 18 (s11.mem.get 18 - s11.mem.get 3), pc := 1221 } := hdec4
  have hrun12 : runN s 12 = step s11 := by
    have hS : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hS.trans (runN_one s11 hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1221 := by have : s12 = step s11 := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step s11 := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 0 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hs11Z
  have hs12T : s12.mem.get 18 = 6 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq, Mem.get_set_eq]
    have h1 : s11.mem.get 18 - s11.mem.get 3 = (7 : Word) - 1 := by
      rw [hs11T, hONE11]
    exact h1.trans (rfl : (7 : Word) - 1 = 6)
  have hI12 : s12.mem.get 29 = 10 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 29 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hI11
  have hCH12 : s12.mem.get 30 = s.mem.get 30 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 30 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hCH11
  have hONE12 : s12.mem.get 3 = 1 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 3 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hONE11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 a (s11.mem.get 18 - s11.mem.get 3) ha18).trans
      (hpres11 a ha18 ha0)
  have g12 := sc_code_shrink (s := s) (s' := s12) (lo := 1221) (hi := 1224)
    hpres12 hcode (by decide) (by decide)
  have henc4 := sc_enc_jlez_1221 (s := s12) hs12pc g12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hjlez4 :=
    step_JLEZ (s := s12) (x := 18) (dest := 1347)
      hs12h hpc12 hs12Z henc4.1 henc4.2.1 henc4.2.2 (by decide)
  have hle4 : (s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18) = false := by
    have : le0 (s12.mem.get 18) = false := by
      rw [hs12T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs13eq : step s12 = { s12 with pc := 1224 } := by
    have hif :
        (if s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18
          then (1347 : Word) else s12.pc + 3) = (1224 : Word) := by
      have hfall : s12.pc + 3 = (1224 : Word) := by simp [hs12pc]
      simp [hle4, hfall]
    rw [hjlez4, hif]
  have hrun13 : runN s 13 = step s12 := by
    have hS : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    exact hS.trans (runN_one s12 hs12h hpc12)
  let s13 := runN s 13
  have hs13pc : s13.pc = 1224 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]
  have hs13h : s13.halted = false := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12Z
  have hs13T : s13.mem.get 18 = 6 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12T
  have hI13 : s13.mem.get 29 = 10 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hI12
  have hCH13 : s13.mem.get 30 = s.mem.get 30 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hCH12
  have hONE13 : s13.mem.get 3 = 1 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hONE12
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s13 = step s12 := hrun13
    rw [this, hs13eq]; exact hpres12 a ha18 ha0
  have g13 := sc_code_shrink (s := s) (s' := s13) (lo := 1224) (hi := 1227)
    hpres13 hcode (by decide) (by decide)
  have hdec5 := sc_dec_T_1224 (s := s13) hs13pc hs13h g13
  have hs14eq : step s13 =
      { s13 with mem := s13.mem.set 18 (s13.mem.get 18 - s13.mem.get 3), pc := 1227 } := hdec5
  have hrun14 : runN s 14 = step s13 := by
    have hS : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hS.trans (runN_one s13 hs13h (by simp [hs13pc]))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1227 := by have : s14 = step s13 := hrun14; rw [this, hs14eq]
  have hs14h : s14.halted = false := by have : s14 = step s13 := hrun14; rw [this, hs14eq]; exact hs13h
  have hs14Z : s14.mem.get 0 = 0 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 0 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hs13Z
  have hs14T : s14.mem.get 18 = 5 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq, Mem.get_set_eq]
    have h1 : s13.mem.get 18 - s13.mem.get 3 = (6 : Word) - 1 := by
      rw [hs13T, hONE13]
    exact h1.trans (rfl : (6 : Word) - 1 = 5)
  have hI14 : s14.mem.get 29 = 10 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 29 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hI13
  have hCH14 : s14.mem.get 30 = s.mem.get 30 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 30 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hCH13
  have hONE14 : s14.mem.get 3 = 1 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 3 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hONE13
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 a (s13.mem.get 18 - s13.mem.get 3) ha18).trans
      (hpres13 a ha18 ha0)
  have g14 := sc_code_shrink (s := s) (s' := s14) (lo := 1227) (hi := 1230)
    hpres14 hcode (by decide) (by decide)
  have henc5 := sc_enc_jlez_1227 (s := s14) hs14pc g14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hjlez5 :=
    step_JLEZ (s := s14) (x := 18) (dest := 1362)
      hs14h hpc14 hs14Z henc5.1 henc5.2.1 henc5.2.2 (by decide)
  have hle5 : (s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18) = false := by
    have : le0 (s14.mem.get 18) = false := by
      rw [hs14T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs15eq : step s14 = { s14 with pc := 1230 } := by
    have hif :
        (if s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18
          then (1362 : Word) else s14.pc + 3) = (1230 : Word) := by
      have hfall : s14.pc + 3 = (1230 : Word) := by simp [hs14pc]
      simp [hle5, hfall]
    rw [hjlez5, hif]
  have hrun15 : runN s 15 = step s14 := by
    have hS : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    exact hS.trans (runN_one s14 hs14h hpc14)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1230 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]
  have hs15h : s15.halted = false := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14Z
  have hs15T : s15.mem.get 18 = 5 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14T
  have hI15 : s15.mem.get 29 = 10 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hI14
  have hCH15 : s15.mem.get 30 = s.mem.get 30 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hCH14
  have hONE15 : s15.mem.get 3 = 1 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hONE14
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s15 = step s14 := hrun15
    rw [this, hs15eq]; exact hpres14 a ha18 ha0
  have g15 := sc_code_shrink (s := s) (s' := s15) (lo := 1230) (hi := 1233)
    hpres15 hcode (by decide) (by decide)
  have hdec6 := sc_dec_T_1230 (s := s15) hs15pc hs15h g15
  have hs16eq : step s15 =
      { s15 with mem := s15.mem.set 18 (s15.mem.get 18 - s15.mem.get 3), pc := 1233 } := hdec6
  have hrun16 : runN s 16 = step s15 := by
    have hS : runN s 16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
    exact hS.trans (runN_one s15 hs15h (by simp [hs15pc]))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1233 := by have : s16 = step s15 := hrun16; rw [this, hs16eq]
  have hs16h : s16.halted = false := by have : s16 = step s15 := hrun16; rw [this, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 0 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hs15Z
  have hs16T : s16.mem.get 18 = 4 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq, Mem.get_set_eq]
    have h1 : s15.mem.get 18 - s15.mem.get 3 = (5 : Word) - 1 := by
      rw [hs15T, hONE15]
    exact h1.trans (rfl : (5 : Word) - 1 = 4)
  have hI16 : s16.mem.get 29 = 10 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 29 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hI15
  have hCH16 : s16.mem.get 30 = s.mem.get 30 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 30 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hCH15
  have hONE16 : s16.mem.get 3 = 1 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 3 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hONE15
  have hpres16 : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 a (s15.mem.get 18 - s15.mem.get 3) ha18).trans
      (hpres15 a ha18 ha0)
  have g16 := sc_code_shrink (s := s) (s' := s16) (lo := 1233) (hi := 1236)
    hpres16 hcode (by decide) (by decide)
  have henc6 := sc_enc_jlez_1233 (s := s16) hs16pc g16
  have hpc16 : s16.pc.toNat < 32768 := by simp [hs16pc]
  have hjlez6 :=
    step_JLEZ (s := s16) (x := 18) (dest := 1377)
      hs16h hpc16 hs16Z henc6.1 henc6.2.1 henc6.2.2 (by decide)
  have hle6 : (s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18) = false := by
    have : le0 (s16.mem.get 18) = false := by
      rw [hs16T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs17eq : step s16 = { s16 with pc := 1236 } := by
    have hif :
        (if s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18
          then (1377 : Word) else s16.pc + 3) = (1236 : Word) := by
      have hfall : s16.pc + 3 = (1236 : Word) := by simp [hs16pc]
      simp [hle6, hfall]
    rw [hjlez6, hif]
  have hrun17 : runN s 17 = step s16 := by
    have hS : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
    exact hS.trans (runN_one s16 hs16h hpc16)
  let s17 := runN s 17
  have hs17pc : s17.pc = 1236 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]
  have hs17h : s17.halted = false := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16h
  have hs17Z : s17.mem.get 0 = 0 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16Z
  have hs17T : s17.mem.get 18 = 4 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16T
  have hI17 : s17.mem.get 29 = 10 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hI16
  have hCH17 : s17.mem.get 30 = s.mem.get 30 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hCH16
  have hONE17 : s17.mem.get 3 = 1 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hONE16
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s17 = step s16 := hrun17
    rw [this, hs17eq]; exact hpres16 a ha18 ha0
  have g17 := sc_code_shrink (s := s) (s' := s17) (lo := 1236) (hi := 1239)
    hpres17 hcode (by decide) (by decide)
  have hdec7 := sc_dec_T_1236 (s := s17) hs17pc hs17h g17
  have hs18eq : step s17 =
      { s17 with mem := s17.mem.set 18 (s17.mem.get 18 - s17.mem.get 3), pc := 1239 } := hdec7
  have hrun18 : runN s 18 = step s17 := by
    have hS : runN s 18 = runN s17 1 := runN_add_eq s 17 1 18 (by decide)
    exact hS.trans (runN_one s17 hs17h (by simp [hs17pc]))
  let s18 := runN s 18
  have hs18pc : s18.pc = 1239 := by have : s18 = step s17 := hrun18; rw [this, hs18eq]
  have hs18h : s18.halted = false := by have : s18 = step s17 := hrun18; rw [this, hs18eq]; exact hs17h
  have hs18Z : s18.mem.get 0 = 0 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 0 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hs17Z
  have hs18T : s18.mem.get 18 = 3 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq, Mem.get_set_eq]
    have h1 : s17.mem.get 18 - s17.mem.get 3 = (4 : Word) - 1 := by
      rw [hs17T, hONE17]
    exact h1.trans (rfl : (4 : Word) - 1 = 3)
  have hI18 : s18.mem.get 29 = 10 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 29 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hI17
  have hCH18 : s18.mem.get 30 = s.mem.get 30 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 30 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hCH17
  have hONE18 : s18.mem.get 3 = 1 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 3 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hONE17
  have hpres18 : ∀ a, a ≠ 18 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 a (s17.mem.get 18 - s17.mem.get 3) ha18).trans
      (hpres17 a ha18 ha0)
  have g18 := sc_code_shrink (s := s) (s' := s18) (lo := 1239) (hi := 1242)
    hpres18 hcode (by decide) (by decide)
  have henc7 := sc_enc_jlez_1239 (s := s18) hs18pc g18
  have hpc18 : s18.pc.toNat < 32768 := by simp [hs18pc]
  have hjlez7 :=
    step_JLEZ (s := s18) (x := 18) (dest := 1392)
      hs18h hpc18 hs18Z henc7.1 henc7.2.1 henc7.2.2 (by decide)
  have hle7 : (s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18) = false := by
    have : le0 (s18.mem.get 18) = false := by
      rw [hs18T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs19eq : step s18 = { s18 with pc := 1242 } := by
    have hif :
        (if s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18
          then (1392 : Word) else s18.pc + 3) = (1242 : Word) := by
      have hfall : s18.pc + 3 = (1242 : Word) := by simp [hs18pc]
      simp [hle7, hfall]
    rw [hjlez7, hif]
  have hrun19 : runN s 19 = step s18 := by
    have hS : runN s 19 = runN s18 1 := runN_add_eq s 18 1 19 (by decide)
    exact hS.trans (runN_one s18 hs18h hpc18)
  let s19 := runN s 19
  have hs19pc : s19.pc = 1242 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]
  have hs19h : s19.halted = false := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18h
  have hs19Z : s19.mem.get 0 = 0 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18Z
  have hs19T : s19.mem.get 18 = 3 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18T
  have hI19 : s19.mem.get 29 = 10 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hI18
  have hCH19 : s19.mem.get 30 = s.mem.get 30 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hCH18
  have hONE19 : s19.mem.get 3 = 1 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hONE18
  have hpres19 : ∀ a, a ≠ 18 → a ≠ 0 → s19.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s19 = step s18 := hrun19
    rw [this, hs19eq]; exact hpres18 a ha18 ha0
  have g19 := sc_code_shrink (s := s) (s' := s19) (lo := 1242) (hi := 1245)
    hpres19 hcode (by decide) (by decide)
  have hdec8 := sc_dec_T_1242 (s := s19) hs19pc hs19h g19
  have hs20eq : step s19 =
      { s19 with mem := s19.mem.set 18 (s19.mem.get 18 - s19.mem.get 3), pc := 1245 } := hdec8
  have hrun20 : runN s 20 = step s19 := by
    have hS : runN s 20 = runN s19 1 := runN_add_eq s 19 1 20 (by decide)
    exact hS.trans (runN_one s19 hs19h (by simp [hs19pc]))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1245 := by have : s20 = step s19 := hrun20; rw [this, hs20eq]
  have hs20h : s20.halted = false := by have : s20 = step s19 := hrun20; rw [this, hs20eq]; exact hs19h
  have hs20Z : s20.mem.get 0 = 0 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 0 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hs19Z
  have hs20T : s20.mem.get 18 = 2 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq, Mem.get_set_eq]
    have h1 : s19.mem.get 18 - s19.mem.get 3 = (3 : Word) - 1 := by
      rw [hs19T, hONE19]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hI20 : s20.mem.get 29 = 10 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 29 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hI19
  have hCH20 : s20.mem.get 30 = s.mem.get 30 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 30 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hCH19
  have hONE20 : s20.mem.get 3 = 1 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 3 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hONE19
  have hpres20 : ∀ a, a ≠ 18 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 a (s19.mem.get 18 - s19.mem.get 3) ha18).trans
      (hpres19 a ha18 ha0)
  have g20 := sc_code_shrink (s := s) (s' := s20) (lo := 1245) (hi := 1248)
    hpres20 hcode (by decide) (by decide)
  have henc8 := sc_enc_jlez_1245 (s := s20) hs20pc g20
  have hpc20 : s20.pc.toNat < 32768 := by simp [hs20pc]
  have hjlez8 :=
    step_JLEZ (s := s20) (x := 18) (dest := 1407)
      hs20h hpc20 hs20Z henc8.1 henc8.2.1 henc8.2.2 (by decide)
  have hle8 : (s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18) = false := by
    have : le0 (s20.mem.get 18) = false := by
      rw [hs20T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs21eq : step s20 = { s20 with pc := 1248 } := by
    have hif :
        (if s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18
          then (1407 : Word) else s20.pc + 3) = (1248 : Word) := by
      have hfall : s20.pc + 3 = (1248 : Word) := by simp [hs20pc]
      simp [hle8, hfall]
    rw [hjlez8, hif]
  have hrun21 : runN s 21 = step s20 := by
    have hS : runN s 21 = runN s20 1 := runN_add_eq s 20 1 21 (by decide)
    exact hS.trans (runN_one s20 hs20h hpc20)
  let s21 := runN s 21
  have hs21pc : s21.pc = 1248 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]
  have hs21h : s21.halted = false := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20h
  have hs21Z : s21.mem.get 0 = 0 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20Z
  have hs21T : s21.mem.get 18 = 2 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20T
  have hI21 : s21.mem.get 29 = 10 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hI20
  have hCH21 : s21.mem.get 30 = s.mem.get 30 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hCH20
  have hONE21 : s21.mem.get 3 = 1 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hONE20
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s21 = step s20 := hrun21
    rw [this, hs21eq]; exact hpres20 a ha18 ha0
  have g21 := sc_code_shrink (s := s) (s' := s21) (lo := 1248) (hi := 1251)
    hpres21 hcode (by decide) (by decide)
  have hdec9 := sc_dec_T_1248 (s := s21) hs21pc hs21h g21
  have hs22eq : step s21 =
      { s21 with mem := s21.mem.set 18 (s21.mem.get 18 - s21.mem.get 3), pc := 1251 } := hdec9
  have hrun22 : runN s 22 = step s21 := by
    have hS : runN s 22 = runN s21 1 := runN_add_eq s 21 1 22 (by decide)
    exact hS.trans (runN_one s21 hs21h (by simp [hs21pc]))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1251 := by have : s22 = step s21 := hrun22; rw [this, hs22eq]
  have hs22h : s22.halted = false := by have : s22 = step s21 := hrun22; rw [this, hs22eq]; exact hs21h
  have hs22Z : s22.mem.get 0 = 0 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 0 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hs21Z
  have hs22T : s22.mem.get 18 = 1 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq, Mem.get_set_eq]
    have h1 : s21.mem.get 18 - s21.mem.get 3 = (2 : Word) - 1 := by
      rw [hs21T, hONE21]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI22 : s22.mem.get 29 = 10 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 29 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hI21
  have hCH22 : s22.mem.get 30 = s.mem.get 30 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 30 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hCH21
  have hONE22 : s22.mem.get 3 = 1 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 3 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hONE21
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 0 → s22.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 a (s21.mem.get 18 - s21.mem.get 3) ha18).trans
      (hpres21 a ha18 ha0)
  have g22 := sc_code_shrink (s := s) (s' := s22) (lo := 1251) (hi := 1254)
    hpres22 hcode (by decide) (by decide)
  have henc9 := sc_enc_jlez_1251 (s := s22) hs22pc g22
  have hpc22 : s22.pc.toNat < 32768 := by simp [hs22pc]
  have hjlez9 :=
    step_JLEZ (s := s22) (x := 18) (dest := 1422)
      hs22h hpc22 hs22Z henc9.1 henc9.2.1 henc9.2.2 (by decide)
  have hle9 : (s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18) = false := by
    have : le0 (s22.mem.get 18) = false := by
      rw [hs22T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs23eq : step s22 = { s22 with pc := 1254 } := by
    have hif :
        (if s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18
          then (1422 : Word) else s22.pc + 3) = (1254 : Word) := by
      have hfall : s22.pc + 3 = (1254 : Word) := by simp [hs22pc]
      simp [hle9, hfall]
    rw [hjlez9, hif]
  have hrun23 : runN s 23 = step s22 := by
    have hS : runN s 23 = runN s22 1 := runN_add_eq s 22 1 23 (by decide)
    exact hS.trans (runN_one s22 hs22h hpc22)
  let s23 := runN s 23
  have hs23pc : s23.pc = 1254 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]
  have hs23h : s23.halted = false := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22h
  have hs23Z : s23.mem.get 0 = 0 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22Z
  have hs23T : s23.mem.get 18 = 1 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22T
  have hI23 : s23.mem.get 29 = 10 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hI22
  have hCH23 : s23.mem.get 30 = s.mem.get 30 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hCH22
  have hONE23 : s23.mem.get 3 = 1 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hONE22
  have hpres23 : ∀ a, a ≠ 18 → a ≠ 0 → s23.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s23 = step s22 := hrun23
    rw [this, hs23eq]; exact hpres22 a ha18 ha0
  have g23 := sc_code_shrink (s := s) (s' := s23) (lo := 1254) (hi := 1257)
    hpres23 hcode (by decide) (by decide)
  have hdec10 := sc_dec_T_1254 (s := s23) hs23pc hs23h g23
  have hs24eq : step s23 =
      { s23 with mem := s23.mem.set 18 (s23.mem.get 18 - s23.mem.get 3), pc := 1257 } := hdec10
  have hrun24 : runN s 24 = step s23 := by
    have hS : runN s 24 = runN s23 1 := runN_add_eq s 23 1 24 (by decide)
    exact hS.trans (runN_one s23 hs23h (by simp [hs23pc]))
  let s24 := runN s 24
  have hs24pc : s24.pc = 1257 := by have : s24 = step s23 := hrun24; rw [this, hs24eq]
  have hs24h : s24.halted = false := by have : s24 = step s23 := hrun24; rw [this, hs24eq]; exact hs23h
  have hs24Z : s24.mem.get 0 = 0 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 0 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hs23Z
  have hs24T : s24.mem.get 18 = 0 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq, Mem.get_set_eq]
    have h1 : s23.mem.get 18 - s23.mem.get 3 = (1 : Word) - 1 := by
      rw [hs23T, hONE23]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI24 : s24.mem.get 29 = 10 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 29 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hI23
  have hCH24 : s24.mem.get 30 = s.mem.get 30 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 30 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hCH23
  have hONE24 : s24.mem.get 3 = 1 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 3 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hONE23
  have hpres24 : ∀ a, a ≠ 18 → a ≠ 0 → s24.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 a (s23.mem.get 18 - s23.mem.get 3) ha18).trans
      (hpres23 a ha18 ha0)
  have g24 := sc_code_shrink (s := s) (s' := s24) (lo := 1257) (hi := 1260)
    hpres24 hcode (by decide) (by decide)
  have henc10 := sc_enc_jlez_1257 (s := s24) hs24pc g24
  have hpc24 : s24.pc.toNat < 32768 := by simp [hs24pc]
  have hjlez10 :=
    step_JLEZ (s := s24) (x := 18) (dest := 1437)
      hs24h hpc24 hs24Z henc10.1 henc10.2.1 henc10.2.2 (by decide)
  have hle10 : (s24.mem.get 18 = 0 || 0x8000 ≤ s24.mem.get 18) = true := by
    have : le0 (s24.mem.get 18) = true := by
      rw [hs24T]; exact le0_zero
    simpa [le0] using this
  have hs25eq : step s24 = { s24 with pc := 1437 } := by
    have hif :
        (if s24.mem.get 18 = 0 || 0x8000 ≤ s24.mem.get 18
          then (1437 : Word) else s24.pc + 3) = (1437 : Word) := by
      simp [hle10]
    rw [hjlez10, hif]
  have hrun25 : runN s 25 = step s24 := by
    have hS : runN s 25 = runN s24 1 := runN_add_eq s 24 1 25 (by decide)
    exact hS.trans (runN_one s24 hs24h hpc24)
  let s25 := runN s 25
  have hs25pc : s25.pc = 1437 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]
  have hs25h : s25.halted = false := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24h
  have hs25Z : s25.mem.get 0 = 0 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24Z
  have hs25T : s25.mem.get 18 = 0 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24T
  have hI25 : s25.mem.get 29 = 10 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hI24
  have hCH25 : s25.mem.get 30 = s.mem.get 30 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hCH24
  have hONE25 : s25.mem.get 3 = 1 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hONE24
  have hpres25 : ∀ a, a ≠ 18 → a ≠ 0 → s25.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s25 = step s24 := hrun25
    rw [this, hs25eq]; exact hpres24 a ha18 ha0
  have g25 := sc_code_shrink (s := s) (s' := s25) (lo := 1437) (hi := 1452)
    hpres25 hcode (by decide) (by decide)
  have hs := st10_store (s := s25) hs25pc hs25h hs25Z g25
  have hrun : sN = runN s25 5 := runN_add_eq s 25 5 30 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 42 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH25
  have hsNI : sN.mem.get 29 = 10 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI25
  have hpres : ∀ a, a ≠ 42 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres25 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 11` at `STORE_CH`: 32 steps to `STORED`, `BUF+11 = CH`. -/
theorem store_ch_idx11 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 11)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 32
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 43 = s.mem.get 30 ∧
    sN.mem.get 29 = 11 ∧
    (∀ a, a ≠ 43 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 11 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 11 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 11 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 11 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 10 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (11 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (11 : Word) - 1 = 10)
  have hI6 : s6.mem.get 29 = 11 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 10 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 11 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 9 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (10 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (10 : Word) - 1 = 9)
  have hI8 : s8.mem.get 29 = 11 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1212 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1212 : Word) := by
      have hfall : s8.pc + 3 = (1212 : Word) := by simp [hs8pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1212 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 9 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 11 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1212) (hi := 1215)
    hpres9 hcode (by decide) (by decide)
  have hdec3 := sc_dec_T_1212 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1215 } := hdec3
  have hrun10 : runN s 10 = step s9 := by
    have hS : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hS.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1215 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : s10.mem.get 18 = 8 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (9 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (9 : Word) - 1 = 8)
  have hI10 : s10.mem.get 29 = 11 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hI9
  have hCH10 : s10.mem.get 30 = s.mem.get 30 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 30 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hCH9
  have hONE10 : s10.mem.get 3 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 3 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have g10 := sc_code_shrink (s := s) (s' := s10) (lo := 1215) (hi := 1218)
    hpres10 hcode (by decide) (by decide)
  have henc3 := sc_enc_jlez_1215 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjlez3 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1332)
      hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = false := by
    have : le0 (s10.mem.get 18) = false := by
      rw [hs10T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq : step s10 = { s10 with pc := 1218 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1332 : Word) else s10.pc + 3) = (1218 : Word) := by
      have hfall : s10.pc + 3 = (1218 : Word) := by simp [hs10pc]
      simp [hle3, hfall]
    rw [hjlez3, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hS : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hS.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1218 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11T : s11.mem.get 18 = 8 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10T
  have hI11 : s11.mem.get 29 = 11 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hI10
  have hCH11 : s11.mem.get 30 = s.mem.get 30 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hCH10
  have hONE11 : s11.mem.get 3 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hONE10
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq]; exact hpres10 a ha18 ha0
  have g11 := sc_code_shrink (s := s) (s' := s11) (lo := 1218) (hi := 1221)
    hpres11 hcode (by decide) (by decide)
  have hdec4 := sc_dec_T_1218 (s := s11) hs11pc hs11h g11
  have hs12eq : step s11 =
      { s11 with mem := s11.mem.set 18 (s11.mem.get 18 - s11.mem.get 3), pc := 1221 } := hdec4
  have hrun12 : runN s 12 = step s11 := by
    have hS : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hS.trans (runN_one s11 hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1221 := by have : s12 = step s11 := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step s11 := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 0 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hs11Z
  have hs12T : s12.mem.get 18 = 7 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq, Mem.get_set_eq]
    have h1 : s11.mem.get 18 - s11.mem.get 3 = (8 : Word) - 1 := by
      rw [hs11T, hONE11]
    exact h1.trans (rfl : (8 : Word) - 1 = 7)
  have hI12 : s12.mem.get 29 = 11 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 29 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hI11
  have hCH12 : s12.mem.get 30 = s.mem.get 30 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 30 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hCH11
  have hONE12 : s12.mem.get 3 = 1 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 3 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hONE11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 a (s11.mem.get 18 - s11.mem.get 3) ha18).trans
      (hpres11 a ha18 ha0)
  have g12 := sc_code_shrink (s := s) (s' := s12) (lo := 1221) (hi := 1224)
    hpres12 hcode (by decide) (by decide)
  have henc4 := sc_enc_jlez_1221 (s := s12) hs12pc g12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hjlez4 :=
    step_JLEZ (s := s12) (x := 18) (dest := 1347)
      hs12h hpc12 hs12Z henc4.1 henc4.2.1 henc4.2.2 (by decide)
  have hle4 : (s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18) = false := by
    have : le0 (s12.mem.get 18) = false := by
      rw [hs12T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs13eq : step s12 = { s12 with pc := 1224 } := by
    have hif :
        (if s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18
          then (1347 : Word) else s12.pc + 3) = (1224 : Word) := by
      have hfall : s12.pc + 3 = (1224 : Word) := by simp [hs12pc]
      simp [hle4, hfall]
    rw [hjlez4, hif]
  have hrun13 : runN s 13 = step s12 := by
    have hS : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    exact hS.trans (runN_one s12 hs12h hpc12)
  let s13 := runN s 13
  have hs13pc : s13.pc = 1224 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]
  have hs13h : s13.halted = false := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12Z
  have hs13T : s13.mem.get 18 = 7 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12T
  have hI13 : s13.mem.get 29 = 11 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hI12
  have hCH13 : s13.mem.get 30 = s.mem.get 30 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hCH12
  have hONE13 : s13.mem.get 3 = 1 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hONE12
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s13 = step s12 := hrun13
    rw [this, hs13eq]; exact hpres12 a ha18 ha0
  have g13 := sc_code_shrink (s := s) (s' := s13) (lo := 1224) (hi := 1227)
    hpres13 hcode (by decide) (by decide)
  have hdec5 := sc_dec_T_1224 (s := s13) hs13pc hs13h g13
  have hs14eq : step s13 =
      { s13 with mem := s13.mem.set 18 (s13.mem.get 18 - s13.mem.get 3), pc := 1227 } := hdec5
  have hrun14 : runN s 14 = step s13 := by
    have hS : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hS.trans (runN_one s13 hs13h (by simp [hs13pc]))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1227 := by have : s14 = step s13 := hrun14; rw [this, hs14eq]
  have hs14h : s14.halted = false := by have : s14 = step s13 := hrun14; rw [this, hs14eq]; exact hs13h
  have hs14Z : s14.mem.get 0 = 0 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 0 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hs13Z
  have hs14T : s14.mem.get 18 = 6 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq, Mem.get_set_eq]
    have h1 : s13.mem.get 18 - s13.mem.get 3 = (7 : Word) - 1 := by
      rw [hs13T, hONE13]
    exact h1.trans (rfl : (7 : Word) - 1 = 6)
  have hI14 : s14.mem.get 29 = 11 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 29 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hI13
  have hCH14 : s14.mem.get 30 = s.mem.get 30 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 30 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hCH13
  have hONE14 : s14.mem.get 3 = 1 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 3 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hONE13
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 a (s13.mem.get 18 - s13.mem.get 3) ha18).trans
      (hpres13 a ha18 ha0)
  have g14 := sc_code_shrink (s := s) (s' := s14) (lo := 1227) (hi := 1230)
    hpres14 hcode (by decide) (by decide)
  have henc5 := sc_enc_jlez_1227 (s := s14) hs14pc g14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hjlez5 :=
    step_JLEZ (s := s14) (x := 18) (dest := 1362)
      hs14h hpc14 hs14Z henc5.1 henc5.2.1 henc5.2.2 (by decide)
  have hle5 : (s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18) = false := by
    have : le0 (s14.mem.get 18) = false := by
      rw [hs14T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs15eq : step s14 = { s14 with pc := 1230 } := by
    have hif :
        (if s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18
          then (1362 : Word) else s14.pc + 3) = (1230 : Word) := by
      have hfall : s14.pc + 3 = (1230 : Word) := by simp [hs14pc]
      simp [hle5, hfall]
    rw [hjlez5, hif]
  have hrun15 : runN s 15 = step s14 := by
    have hS : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    exact hS.trans (runN_one s14 hs14h hpc14)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1230 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]
  have hs15h : s15.halted = false := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14Z
  have hs15T : s15.mem.get 18 = 6 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14T
  have hI15 : s15.mem.get 29 = 11 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hI14
  have hCH15 : s15.mem.get 30 = s.mem.get 30 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hCH14
  have hONE15 : s15.mem.get 3 = 1 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hONE14
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s15 = step s14 := hrun15
    rw [this, hs15eq]; exact hpres14 a ha18 ha0
  have g15 := sc_code_shrink (s := s) (s' := s15) (lo := 1230) (hi := 1233)
    hpres15 hcode (by decide) (by decide)
  have hdec6 := sc_dec_T_1230 (s := s15) hs15pc hs15h g15
  have hs16eq : step s15 =
      { s15 with mem := s15.mem.set 18 (s15.mem.get 18 - s15.mem.get 3), pc := 1233 } := hdec6
  have hrun16 : runN s 16 = step s15 := by
    have hS : runN s 16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
    exact hS.trans (runN_one s15 hs15h (by simp [hs15pc]))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1233 := by have : s16 = step s15 := hrun16; rw [this, hs16eq]
  have hs16h : s16.halted = false := by have : s16 = step s15 := hrun16; rw [this, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 0 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hs15Z
  have hs16T : s16.mem.get 18 = 5 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq, Mem.get_set_eq]
    have h1 : s15.mem.get 18 - s15.mem.get 3 = (6 : Word) - 1 := by
      rw [hs15T, hONE15]
    exact h1.trans (rfl : (6 : Word) - 1 = 5)
  have hI16 : s16.mem.get 29 = 11 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 29 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hI15
  have hCH16 : s16.mem.get 30 = s.mem.get 30 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 30 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hCH15
  have hONE16 : s16.mem.get 3 = 1 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 3 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hONE15
  have hpres16 : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 a (s15.mem.get 18 - s15.mem.get 3) ha18).trans
      (hpres15 a ha18 ha0)
  have g16 := sc_code_shrink (s := s) (s' := s16) (lo := 1233) (hi := 1236)
    hpres16 hcode (by decide) (by decide)
  have henc6 := sc_enc_jlez_1233 (s := s16) hs16pc g16
  have hpc16 : s16.pc.toNat < 32768 := by simp [hs16pc]
  have hjlez6 :=
    step_JLEZ (s := s16) (x := 18) (dest := 1377)
      hs16h hpc16 hs16Z henc6.1 henc6.2.1 henc6.2.2 (by decide)
  have hle6 : (s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18) = false := by
    have : le0 (s16.mem.get 18) = false := by
      rw [hs16T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs17eq : step s16 = { s16 with pc := 1236 } := by
    have hif :
        (if s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18
          then (1377 : Word) else s16.pc + 3) = (1236 : Word) := by
      have hfall : s16.pc + 3 = (1236 : Word) := by simp [hs16pc]
      simp [hle6, hfall]
    rw [hjlez6, hif]
  have hrun17 : runN s 17 = step s16 := by
    have hS : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
    exact hS.trans (runN_one s16 hs16h hpc16)
  let s17 := runN s 17
  have hs17pc : s17.pc = 1236 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]
  have hs17h : s17.halted = false := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16h
  have hs17Z : s17.mem.get 0 = 0 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16Z
  have hs17T : s17.mem.get 18 = 5 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16T
  have hI17 : s17.mem.get 29 = 11 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hI16
  have hCH17 : s17.mem.get 30 = s.mem.get 30 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hCH16
  have hONE17 : s17.mem.get 3 = 1 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hONE16
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s17 = step s16 := hrun17
    rw [this, hs17eq]; exact hpres16 a ha18 ha0
  have g17 := sc_code_shrink (s := s) (s' := s17) (lo := 1236) (hi := 1239)
    hpres17 hcode (by decide) (by decide)
  have hdec7 := sc_dec_T_1236 (s := s17) hs17pc hs17h g17
  have hs18eq : step s17 =
      { s17 with mem := s17.mem.set 18 (s17.mem.get 18 - s17.mem.get 3), pc := 1239 } := hdec7
  have hrun18 : runN s 18 = step s17 := by
    have hS : runN s 18 = runN s17 1 := runN_add_eq s 17 1 18 (by decide)
    exact hS.trans (runN_one s17 hs17h (by simp [hs17pc]))
  let s18 := runN s 18
  have hs18pc : s18.pc = 1239 := by have : s18 = step s17 := hrun18; rw [this, hs18eq]
  have hs18h : s18.halted = false := by have : s18 = step s17 := hrun18; rw [this, hs18eq]; exact hs17h
  have hs18Z : s18.mem.get 0 = 0 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 0 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hs17Z
  have hs18T : s18.mem.get 18 = 4 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq, Mem.get_set_eq]
    have h1 : s17.mem.get 18 - s17.mem.get 3 = (5 : Word) - 1 := by
      rw [hs17T, hONE17]
    exact h1.trans (rfl : (5 : Word) - 1 = 4)
  have hI18 : s18.mem.get 29 = 11 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 29 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hI17
  have hCH18 : s18.mem.get 30 = s.mem.get 30 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 30 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hCH17
  have hONE18 : s18.mem.get 3 = 1 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 3 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hONE17
  have hpres18 : ∀ a, a ≠ 18 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 a (s17.mem.get 18 - s17.mem.get 3) ha18).trans
      (hpres17 a ha18 ha0)
  have g18 := sc_code_shrink (s := s) (s' := s18) (lo := 1239) (hi := 1242)
    hpres18 hcode (by decide) (by decide)
  have henc7 := sc_enc_jlez_1239 (s := s18) hs18pc g18
  have hpc18 : s18.pc.toNat < 32768 := by simp [hs18pc]
  have hjlez7 :=
    step_JLEZ (s := s18) (x := 18) (dest := 1392)
      hs18h hpc18 hs18Z henc7.1 henc7.2.1 henc7.2.2 (by decide)
  have hle7 : (s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18) = false := by
    have : le0 (s18.mem.get 18) = false := by
      rw [hs18T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs19eq : step s18 = { s18 with pc := 1242 } := by
    have hif :
        (if s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18
          then (1392 : Word) else s18.pc + 3) = (1242 : Word) := by
      have hfall : s18.pc + 3 = (1242 : Word) := by simp [hs18pc]
      simp [hle7, hfall]
    rw [hjlez7, hif]
  have hrun19 : runN s 19 = step s18 := by
    have hS : runN s 19 = runN s18 1 := runN_add_eq s 18 1 19 (by decide)
    exact hS.trans (runN_one s18 hs18h hpc18)
  let s19 := runN s 19
  have hs19pc : s19.pc = 1242 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]
  have hs19h : s19.halted = false := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18h
  have hs19Z : s19.mem.get 0 = 0 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18Z
  have hs19T : s19.mem.get 18 = 4 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18T
  have hI19 : s19.mem.get 29 = 11 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hI18
  have hCH19 : s19.mem.get 30 = s.mem.get 30 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hCH18
  have hONE19 : s19.mem.get 3 = 1 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hONE18
  have hpres19 : ∀ a, a ≠ 18 → a ≠ 0 → s19.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s19 = step s18 := hrun19
    rw [this, hs19eq]; exact hpres18 a ha18 ha0
  have g19 := sc_code_shrink (s := s) (s' := s19) (lo := 1242) (hi := 1245)
    hpres19 hcode (by decide) (by decide)
  have hdec8 := sc_dec_T_1242 (s := s19) hs19pc hs19h g19
  have hs20eq : step s19 =
      { s19 with mem := s19.mem.set 18 (s19.mem.get 18 - s19.mem.get 3), pc := 1245 } := hdec8
  have hrun20 : runN s 20 = step s19 := by
    have hS : runN s 20 = runN s19 1 := runN_add_eq s 19 1 20 (by decide)
    exact hS.trans (runN_one s19 hs19h (by simp [hs19pc]))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1245 := by have : s20 = step s19 := hrun20; rw [this, hs20eq]
  have hs20h : s20.halted = false := by have : s20 = step s19 := hrun20; rw [this, hs20eq]; exact hs19h
  have hs20Z : s20.mem.get 0 = 0 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 0 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hs19Z
  have hs20T : s20.mem.get 18 = 3 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq, Mem.get_set_eq]
    have h1 : s19.mem.get 18 - s19.mem.get 3 = (4 : Word) - 1 := by
      rw [hs19T, hONE19]
    exact h1.trans (rfl : (4 : Word) - 1 = 3)
  have hI20 : s20.mem.get 29 = 11 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 29 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hI19
  have hCH20 : s20.mem.get 30 = s.mem.get 30 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 30 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hCH19
  have hONE20 : s20.mem.get 3 = 1 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 3 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hONE19
  have hpres20 : ∀ a, a ≠ 18 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 a (s19.mem.get 18 - s19.mem.get 3) ha18).trans
      (hpres19 a ha18 ha0)
  have g20 := sc_code_shrink (s := s) (s' := s20) (lo := 1245) (hi := 1248)
    hpres20 hcode (by decide) (by decide)
  have henc8 := sc_enc_jlez_1245 (s := s20) hs20pc g20
  have hpc20 : s20.pc.toNat < 32768 := by simp [hs20pc]
  have hjlez8 :=
    step_JLEZ (s := s20) (x := 18) (dest := 1407)
      hs20h hpc20 hs20Z henc8.1 henc8.2.1 henc8.2.2 (by decide)
  have hle8 : (s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18) = false := by
    have : le0 (s20.mem.get 18) = false := by
      rw [hs20T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs21eq : step s20 = { s20 with pc := 1248 } := by
    have hif :
        (if s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18
          then (1407 : Word) else s20.pc + 3) = (1248 : Word) := by
      have hfall : s20.pc + 3 = (1248 : Word) := by simp [hs20pc]
      simp [hle8, hfall]
    rw [hjlez8, hif]
  have hrun21 : runN s 21 = step s20 := by
    have hS : runN s 21 = runN s20 1 := runN_add_eq s 20 1 21 (by decide)
    exact hS.trans (runN_one s20 hs20h hpc20)
  let s21 := runN s 21
  have hs21pc : s21.pc = 1248 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]
  have hs21h : s21.halted = false := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20h
  have hs21Z : s21.mem.get 0 = 0 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20Z
  have hs21T : s21.mem.get 18 = 3 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20T
  have hI21 : s21.mem.get 29 = 11 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hI20
  have hCH21 : s21.mem.get 30 = s.mem.get 30 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hCH20
  have hONE21 : s21.mem.get 3 = 1 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hONE20
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s21 = step s20 := hrun21
    rw [this, hs21eq]; exact hpres20 a ha18 ha0
  have g21 := sc_code_shrink (s := s) (s' := s21) (lo := 1248) (hi := 1251)
    hpres21 hcode (by decide) (by decide)
  have hdec9 := sc_dec_T_1248 (s := s21) hs21pc hs21h g21
  have hs22eq : step s21 =
      { s21 with mem := s21.mem.set 18 (s21.mem.get 18 - s21.mem.get 3), pc := 1251 } := hdec9
  have hrun22 : runN s 22 = step s21 := by
    have hS : runN s 22 = runN s21 1 := runN_add_eq s 21 1 22 (by decide)
    exact hS.trans (runN_one s21 hs21h (by simp [hs21pc]))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1251 := by have : s22 = step s21 := hrun22; rw [this, hs22eq]
  have hs22h : s22.halted = false := by have : s22 = step s21 := hrun22; rw [this, hs22eq]; exact hs21h
  have hs22Z : s22.mem.get 0 = 0 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 0 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hs21Z
  have hs22T : s22.mem.get 18 = 2 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq, Mem.get_set_eq]
    have h1 : s21.mem.get 18 - s21.mem.get 3 = (3 : Word) - 1 := by
      rw [hs21T, hONE21]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hI22 : s22.mem.get 29 = 11 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 29 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hI21
  have hCH22 : s22.mem.get 30 = s.mem.get 30 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 30 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hCH21
  have hONE22 : s22.mem.get 3 = 1 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 3 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hONE21
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 0 → s22.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 a (s21.mem.get 18 - s21.mem.get 3) ha18).trans
      (hpres21 a ha18 ha0)
  have g22 := sc_code_shrink (s := s) (s' := s22) (lo := 1251) (hi := 1254)
    hpres22 hcode (by decide) (by decide)
  have henc9 := sc_enc_jlez_1251 (s := s22) hs22pc g22
  have hpc22 : s22.pc.toNat < 32768 := by simp [hs22pc]
  have hjlez9 :=
    step_JLEZ (s := s22) (x := 18) (dest := 1422)
      hs22h hpc22 hs22Z henc9.1 henc9.2.1 henc9.2.2 (by decide)
  have hle9 : (s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18) = false := by
    have : le0 (s22.mem.get 18) = false := by
      rw [hs22T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs23eq : step s22 = { s22 with pc := 1254 } := by
    have hif :
        (if s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18
          then (1422 : Word) else s22.pc + 3) = (1254 : Word) := by
      have hfall : s22.pc + 3 = (1254 : Word) := by simp [hs22pc]
      simp [hle9, hfall]
    rw [hjlez9, hif]
  have hrun23 : runN s 23 = step s22 := by
    have hS : runN s 23 = runN s22 1 := runN_add_eq s 22 1 23 (by decide)
    exact hS.trans (runN_one s22 hs22h hpc22)
  let s23 := runN s 23
  have hs23pc : s23.pc = 1254 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]
  have hs23h : s23.halted = false := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22h
  have hs23Z : s23.mem.get 0 = 0 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22Z
  have hs23T : s23.mem.get 18 = 2 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22T
  have hI23 : s23.mem.get 29 = 11 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hI22
  have hCH23 : s23.mem.get 30 = s.mem.get 30 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hCH22
  have hONE23 : s23.mem.get 3 = 1 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hONE22
  have hpres23 : ∀ a, a ≠ 18 → a ≠ 0 → s23.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s23 = step s22 := hrun23
    rw [this, hs23eq]; exact hpres22 a ha18 ha0
  have g23 := sc_code_shrink (s := s) (s' := s23) (lo := 1254) (hi := 1257)
    hpres23 hcode (by decide) (by decide)
  have hdec10 := sc_dec_T_1254 (s := s23) hs23pc hs23h g23
  have hs24eq : step s23 =
      { s23 with mem := s23.mem.set 18 (s23.mem.get 18 - s23.mem.get 3), pc := 1257 } := hdec10
  have hrun24 : runN s 24 = step s23 := by
    have hS : runN s 24 = runN s23 1 := runN_add_eq s 23 1 24 (by decide)
    exact hS.trans (runN_one s23 hs23h (by simp [hs23pc]))
  let s24 := runN s 24
  have hs24pc : s24.pc = 1257 := by have : s24 = step s23 := hrun24; rw [this, hs24eq]
  have hs24h : s24.halted = false := by have : s24 = step s23 := hrun24; rw [this, hs24eq]; exact hs23h
  have hs24Z : s24.mem.get 0 = 0 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 0 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hs23Z
  have hs24T : s24.mem.get 18 = 1 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq, Mem.get_set_eq]
    have h1 : s23.mem.get 18 - s23.mem.get 3 = (2 : Word) - 1 := by
      rw [hs23T, hONE23]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI24 : s24.mem.get 29 = 11 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 29 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hI23
  have hCH24 : s24.mem.get 30 = s.mem.get 30 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 30 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hCH23
  have hONE24 : s24.mem.get 3 = 1 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 3 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hONE23
  have hpres24 : ∀ a, a ≠ 18 → a ≠ 0 → s24.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 a (s23.mem.get 18 - s23.mem.get 3) ha18).trans
      (hpres23 a ha18 ha0)
  have g24 := sc_code_shrink (s := s) (s' := s24) (lo := 1257) (hi := 1260)
    hpres24 hcode (by decide) (by decide)
  have henc10 := sc_enc_jlez_1257 (s := s24) hs24pc g24
  have hpc24 : s24.pc.toNat < 32768 := by simp [hs24pc]
  have hjlez10 :=
    step_JLEZ (s := s24) (x := 18) (dest := 1437)
      hs24h hpc24 hs24Z henc10.1 henc10.2.1 henc10.2.2 (by decide)
  have hle10 : (s24.mem.get 18 = 0 || 0x8000 ≤ s24.mem.get 18) = false := by
    have : le0 (s24.mem.get 18) = false := by
      rw [hs24T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs25eq : step s24 = { s24 with pc := 1260 } := by
    have hif :
        (if s24.mem.get 18 = 0 || 0x8000 ≤ s24.mem.get 18
          then (1437 : Word) else s24.pc + 3) = (1260 : Word) := by
      have hfall : s24.pc + 3 = (1260 : Word) := by simp [hs24pc]
      simp [hle10, hfall]
    rw [hjlez10, hif]
  have hrun25 : runN s 25 = step s24 := by
    have hS : runN s 25 = runN s24 1 := runN_add_eq s 24 1 25 (by decide)
    exact hS.trans (runN_one s24 hs24h hpc24)
  let s25 := runN s 25
  have hs25pc : s25.pc = 1260 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]
  have hs25h : s25.halted = false := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24h
  have hs25Z : s25.mem.get 0 = 0 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24Z
  have hs25T : s25.mem.get 18 = 1 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24T
  have hI25 : s25.mem.get 29 = 11 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hI24
  have hCH25 : s25.mem.get 30 = s.mem.get 30 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hCH24
  have hONE25 : s25.mem.get 3 = 1 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hONE24
  have hpres25 : ∀ a, a ≠ 18 → a ≠ 0 → s25.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s25 = step s24 := hrun25
    rw [this, hs25eq]; exact hpres24 a ha18 ha0
  have g25 := sc_code_shrink (s := s) (s' := s25) (lo := 1260) (hi := 1263)
    hpres25 hcode (by decide) (by decide)
  have hdec11 := sc_dec_T_1260 (s := s25) hs25pc hs25h g25
  have hs26eq : step s25 =
      { s25 with mem := s25.mem.set 18 (s25.mem.get 18 - s25.mem.get 3), pc := 1263 } := hdec11
  have hrun26 : runN s 26 = step s25 := by
    have hS : runN s 26 = runN s25 1 := runN_add_eq s 25 1 26 (by decide)
    exact hS.trans (runN_one s25 hs25h (by simp [hs25pc]))
  let s26 := runN s 26
  have hs26pc : s26.pc = 1263 := by have : s26 = step s25 := hrun26; rw [this, hs26eq]
  have hs26h : s26.halted = false := by have : s26 = step s25 := hrun26; rw [this, hs26eq]; exact hs25h
  have hs26Z : s26.mem.get 0 = 0 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 0 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hs25Z
  have hs26T : s26.mem.get 18 = 0 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq, Mem.get_set_eq]
    have h1 : s25.mem.get 18 - s25.mem.get 3 = (1 : Word) - 1 := by
      rw [hs25T, hONE25]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI26 : s26.mem.get 29 = 11 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 29 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hI25
  have hCH26 : s26.mem.get 30 = s.mem.get 30 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 30 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hCH25
  have hONE26 : s26.mem.get 3 = 1 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 3 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hONE25
  have hpres26 : ∀ a, a ≠ 18 → a ≠ 0 → s26.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 a (s25.mem.get 18 - s25.mem.get 3) ha18).trans
      (hpres25 a ha18 ha0)
  have g26 := sc_code_shrink (s := s) (s' := s26) (lo := 1263) (hi := 1266)
    hpres26 hcode (by decide) (by decide)
  have henc11 := sc_enc_jlez_1263 (s := s26) hs26pc g26
  have hpc26 : s26.pc.toNat < 32768 := by simp [hs26pc]
  have hjlez11 :=
    step_JLEZ (s := s26) (x := 18) (dest := 1452)
      hs26h hpc26 hs26Z henc11.1 henc11.2.1 henc11.2.2 (by decide)
  have hle11 : (s26.mem.get 18 = 0 || 0x8000 ≤ s26.mem.get 18) = true := by
    have : le0 (s26.mem.get 18) = true := by
      rw [hs26T]; exact le0_zero
    simpa [le0] using this
  have hs27eq : step s26 = { s26 with pc := 1452 } := by
    have hif :
        (if s26.mem.get 18 = 0 || 0x8000 ≤ s26.mem.get 18
          then (1452 : Word) else s26.pc + 3) = (1452 : Word) := by
      simp [hle11]
    rw [hjlez11, hif]
  have hrun27 : runN s 27 = step s26 := by
    have hS : runN s 27 = runN s26 1 := runN_add_eq s 26 1 27 (by decide)
    exact hS.trans (runN_one s26 hs26h hpc26)
  let s27 := runN s 27
  have hs27pc : s27.pc = 1452 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]
  have hs27h : s27.halted = false := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26h
  have hs27Z : s27.mem.get 0 = 0 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26Z
  have hs27T : s27.mem.get 18 = 0 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26T
  have hI27 : s27.mem.get 29 = 11 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hI26
  have hCH27 : s27.mem.get 30 = s.mem.get 30 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hCH26
  have hONE27 : s27.mem.get 3 = 1 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hONE26
  have hpres27 : ∀ a, a ≠ 18 → a ≠ 0 → s27.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s27 = step s26 := hrun27
    rw [this, hs27eq]; exact hpres26 a ha18 ha0
  have g27 := sc_code_shrink (s := s) (s' := s27) (lo := 1452) (hi := 1467)
    hpres27 hcode (by decide) (by decide)
  have hs := st11_store (s := s27) hs27pc hs27h hs27Z g27
  have hrun : sN = runN s27 5 := runN_add_eq s 27 5 32 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 43 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH27
  have hsNI : sN.mem.get 29 = 11 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI27
  have hpres : ∀ a, a ≠ 43 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres27 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 12` at `STORE_CH`: 34 steps to `STORED`, `BUF+12 = CH`. -/
theorem store_ch_idx12 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 12)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 34
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 44 = s.mem.get 30 ∧
    sN.mem.get 29 = 12 ∧
    (∀ a, a ≠ 44 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 12 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 12 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 12 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 12 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 11 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (12 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (12 : Word) - 1 = 11)
  have hI6 : s6.mem.get 29 = 12 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 11 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 12 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 10 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (11 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (11 : Word) - 1 = 10)
  have hI8 : s8.mem.get 29 = 12 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1212 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1212 : Word) := by
      have hfall : s8.pc + 3 = (1212 : Word) := by simp [hs8pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1212 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 10 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 12 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1212) (hi := 1215)
    hpres9 hcode (by decide) (by decide)
  have hdec3 := sc_dec_T_1212 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1215 } := hdec3
  have hrun10 : runN s 10 = step s9 := by
    have hS : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hS.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1215 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : s10.mem.get 18 = 9 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (10 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (10 : Word) - 1 = 9)
  have hI10 : s10.mem.get 29 = 12 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hI9
  have hCH10 : s10.mem.get 30 = s.mem.get 30 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 30 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hCH9
  have hONE10 : s10.mem.get 3 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 3 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have g10 := sc_code_shrink (s := s) (s' := s10) (lo := 1215) (hi := 1218)
    hpres10 hcode (by decide) (by decide)
  have henc3 := sc_enc_jlez_1215 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjlez3 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1332)
      hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = false := by
    have : le0 (s10.mem.get 18) = false := by
      rw [hs10T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq : step s10 = { s10 with pc := 1218 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1332 : Word) else s10.pc + 3) = (1218 : Word) := by
      have hfall : s10.pc + 3 = (1218 : Word) := by simp [hs10pc]
      simp [hle3, hfall]
    rw [hjlez3, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hS : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hS.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1218 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11T : s11.mem.get 18 = 9 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10T
  have hI11 : s11.mem.get 29 = 12 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hI10
  have hCH11 : s11.mem.get 30 = s.mem.get 30 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hCH10
  have hONE11 : s11.mem.get 3 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hONE10
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq]; exact hpres10 a ha18 ha0
  have g11 := sc_code_shrink (s := s) (s' := s11) (lo := 1218) (hi := 1221)
    hpres11 hcode (by decide) (by decide)
  have hdec4 := sc_dec_T_1218 (s := s11) hs11pc hs11h g11
  have hs12eq : step s11 =
      { s11 with mem := s11.mem.set 18 (s11.mem.get 18 - s11.mem.get 3), pc := 1221 } := hdec4
  have hrun12 : runN s 12 = step s11 := by
    have hS : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hS.trans (runN_one s11 hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1221 := by have : s12 = step s11 := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step s11 := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 0 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hs11Z
  have hs12T : s12.mem.get 18 = 8 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq, Mem.get_set_eq]
    have h1 : s11.mem.get 18 - s11.mem.get 3 = (9 : Word) - 1 := by
      rw [hs11T, hONE11]
    exact h1.trans (rfl : (9 : Word) - 1 = 8)
  have hI12 : s12.mem.get 29 = 12 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 29 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hI11
  have hCH12 : s12.mem.get 30 = s.mem.get 30 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 30 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hCH11
  have hONE12 : s12.mem.get 3 = 1 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 3 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hONE11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 a (s11.mem.get 18 - s11.mem.get 3) ha18).trans
      (hpres11 a ha18 ha0)
  have g12 := sc_code_shrink (s := s) (s' := s12) (lo := 1221) (hi := 1224)
    hpres12 hcode (by decide) (by decide)
  have henc4 := sc_enc_jlez_1221 (s := s12) hs12pc g12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hjlez4 :=
    step_JLEZ (s := s12) (x := 18) (dest := 1347)
      hs12h hpc12 hs12Z henc4.1 henc4.2.1 henc4.2.2 (by decide)
  have hle4 : (s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18) = false := by
    have : le0 (s12.mem.get 18) = false := by
      rw [hs12T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs13eq : step s12 = { s12 with pc := 1224 } := by
    have hif :
        (if s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18
          then (1347 : Word) else s12.pc + 3) = (1224 : Word) := by
      have hfall : s12.pc + 3 = (1224 : Word) := by simp [hs12pc]
      simp [hle4, hfall]
    rw [hjlez4, hif]
  have hrun13 : runN s 13 = step s12 := by
    have hS : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    exact hS.trans (runN_one s12 hs12h hpc12)
  let s13 := runN s 13
  have hs13pc : s13.pc = 1224 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]
  have hs13h : s13.halted = false := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12Z
  have hs13T : s13.mem.get 18 = 8 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12T
  have hI13 : s13.mem.get 29 = 12 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hI12
  have hCH13 : s13.mem.get 30 = s.mem.get 30 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hCH12
  have hONE13 : s13.mem.get 3 = 1 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hONE12
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s13 = step s12 := hrun13
    rw [this, hs13eq]; exact hpres12 a ha18 ha0
  have g13 := sc_code_shrink (s := s) (s' := s13) (lo := 1224) (hi := 1227)
    hpres13 hcode (by decide) (by decide)
  have hdec5 := sc_dec_T_1224 (s := s13) hs13pc hs13h g13
  have hs14eq : step s13 =
      { s13 with mem := s13.mem.set 18 (s13.mem.get 18 - s13.mem.get 3), pc := 1227 } := hdec5
  have hrun14 : runN s 14 = step s13 := by
    have hS : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hS.trans (runN_one s13 hs13h (by simp [hs13pc]))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1227 := by have : s14 = step s13 := hrun14; rw [this, hs14eq]
  have hs14h : s14.halted = false := by have : s14 = step s13 := hrun14; rw [this, hs14eq]; exact hs13h
  have hs14Z : s14.mem.get 0 = 0 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 0 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hs13Z
  have hs14T : s14.mem.get 18 = 7 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq, Mem.get_set_eq]
    have h1 : s13.mem.get 18 - s13.mem.get 3 = (8 : Word) - 1 := by
      rw [hs13T, hONE13]
    exact h1.trans (rfl : (8 : Word) - 1 = 7)
  have hI14 : s14.mem.get 29 = 12 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 29 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hI13
  have hCH14 : s14.mem.get 30 = s.mem.get 30 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 30 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hCH13
  have hONE14 : s14.mem.get 3 = 1 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 3 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hONE13
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 a (s13.mem.get 18 - s13.mem.get 3) ha18).trans
      (hpres13 a ha18 ha0)
  have g14 := sc_code_shrink (s := s) (s' := s14) (lo := 1227) (hi := 1230)
    hpres14 hcode (by decide) (by decide)
  have henc5 := sc_enc_jlez_1227 (s := s14) hs14pc g14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hjlez5 :=
    step_JLEZ (s := s14) (x := 18) (dest := 1362)
      hs14h hpc14 hs14Z henc5.1 henc5.2.1 henc5.2.2 (by decide)
  have hle5 : (s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18) = false := by
    have : le0 (s14.mem.get 18) = false := by
      rw [hs14T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs15eq : step s14 = { s14 with pc := 1230 } := by
    have hif :
        (if s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18
          then (1362 : Word) else s14.pc + 3) = (1230 : Word) := by
      have hfall : s14.pc + 3 = (1230 : Word) := by simp [hs14pc]
      simp [hle5, hfall]
    rw [hjlez5, hif]
  have hrun15 : runN s 15 = step s14 := by
    have hS : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    exact hS.trans (runN_one s14 hs14h hpc14)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1230 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]
  have hs15h : s15.halted = false := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14Z
  have hs15T : s15.mem.get 18 = 7 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14T
  have hI15 : s15.mem.get 29 = 12 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hI14
  have hCH15 : s15.mem.get 30 = s.mem.get 30 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hCH14
  have hONE15 : s15.mem.get 3 = 1 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hONE14
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s15 = step s14 := hrun15
    rw [this, hs15eq]; exact hpres14 a ha18 ha0
  have g15 := sc_code_shrink (s := s) (s' := s15) (lo := 1230) (hi := 1233)
    hpres15 hcode (by decide) (by decide)
  have hdec6 := sc_dec_T_1230 (s := s15) hs15pc hs15h g15
  have hs16eq : step s15 =
      { s15 with mem := s15.mem.set 18 (s15.mem.get 18 - s15.mem.get 3), pc := 1233 } := hdec6
  have hrun16 : runN s 16 = step s15 := by
    have hS : runN s 16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
    exact hS.trans (runN_one s15 hs15h (by simp [hs15pc]))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1233 := by have : s16 = step s15 := hrun16; rw [this, hs16eq]
  have hs16h : s16.halted = false := by have : s16 = step s15 := hrun16; rw [this, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 0 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hs15Z
  have hs16T : s16.mem.get 18 = 6 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq, Mem.get_set_eq]
    have h1 : s15.mem.get 18 - s15.mem.get 3 = (7 : Word) - 1 := by
      rw [hs15T, hONE15]
    exact h1.trans (rfl : (7 : Word) - 1 = 6)
  have hI16 : s16.mem.get 29 = 12 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 29 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hI15
  have hCH16 : s16.mem.get 30 = s.mem.get 30 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 30 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hCH15
  have hONE16 : s16.mem.get 3 = 1 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 3 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hONE15
  have hpres16 : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 a (s15.mem.get 18 - s15.mem.get 3) ha18).trans
      (hpres15 a ha18 ha0)
  have g16 := sc_code_shrink (s := s) (s' := s16) (lo := 1233) (hi := 1236)
    hpres16 hcode (by decide) (by decide)
  have henc6 := sc_enc_jlez_1233 (s := s16) hs16pc g16
  have hpc16 : s16.pc.toNat < 32768 := by simp [hs16pc]
  have hjlez6 :=
    step_JLEZ (s := s16) (x := 18) (dest := 1377)
      hs16h hpc16 hs16Z henc6.1 henc6.2.1 henc6.2.2 (by decide)
  have hle6 : (s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18) = false := by
    have : le0 (s16.mem.get 18) = false := by
      rw [hs16T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs17eq : step s16 = { s16 with pc := 1236 } := by
    have hif :
        (if s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18
          then (1377 : Word) else s16.pc + 3) = (1236 : Word) := by
      have hfall : s16.pc + 3 = (1236 : Word) := by simp [hs16pc]
      simp [hle6, hfall]
    rw [hjlez6, hif]
  have hrun17 : runN s 17 = step s16 := by
    have hS : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
    exact hS.trans (runN_one s16 hs16h hpc16)
  let s17 := runN s 17
  have hs17pc : s17.pc = 1236 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]
  have hs17h : s17.halted = false := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16h
  have hs17Z : s17.mem.get 0 = 0 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16Z
  have hs17T : s17.mem.get 18 = 6 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16T
  have hI17 : s17.mem.get 29 = 12 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hI16
  have hCH17 : s17.mem.get 30 = s.mem.get 30 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hCH16
  have hONE17 : s17.mem.get 3 = 1 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hONE16
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s17 = step s16 := hrun17
    rw [this, hs17eq]; exact hpres16 a ha18 ha0
  have g17 := sc_code_shrink (s := s) (s' := s17) (lo := 1236) (hi := 1239)
    hpres17 hcode (by decide) (by decide)
  have hdec7 := sc_dec_T_1236 (s := s17) hs17pc hs17h g17
  have hs18eq : step s17 =
      { s17 with mem := s17.mem.set 18 (s17.mem.get 18 - s17.mem.get 3), pc := 1239 } := hdec7
  have hrun18 : runN s 18 = step s17 := by
    have hS : runN s 18 = runN s17 1 := runN_add_eq s 17 1 18 (by decide)
    exact hS.trans (runN_one s17 hs17h (by simp [hs17pc]))
  let s18 := runN s 18
  have hs18pc : s18.pc = 1239 := by have : s18 = step s17 := hrun18; rw [this, hs18eq]
  have hs18h : s18.halted = false := by have : s18 = step s17 := hrun18; rw [this, hs18eq]; exact hs17h
  have hs18Z : s18.mem.get 0 = 0 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 0 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hs17Z
  have hs18T : s18.mem.get 18 = 5 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq, Mem.get_set_eq]
    have h1 : s17.mem.get 18 - s17.mem.get 3 = (6 : Word) - 1 := by
      rw [hs17T, hONE17]
    exact h1.trans (rfl : (6 : Word) - 1 = 5)
  have hI18 : s18.mem.get 29 = 12 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 29 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hI17
  have hCH18 : s18.mem.get 30 = s.mem.get 30 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 30 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hCH17
  have hONE18 : s18.mem.get 3 = 1 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 3 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hONE17
  have hpres18 : ∀ a, a ≠ 18 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 a (s17.mem.get 18 - s17.mem.get 3) ha18).trans
      (hpres17 a ha18 ha0)
  have g18 := sc_code_shrink (s := s) (s' := s18) (lo := 1239) (hi := 1242)
    hpres18 hcode (by decide) (by decide)
  have henc7 := sc_enc_jlez_1239 (s := s18) hs18pc g18
  have hpc18 : s18.pc.toNat < 32768 := by simp [hs18pc]
  have hjlez7 :=
    step_JLEZ (s := s18) (x := 18) (dest := 1392)
      hs18h hpc18 hs18Z henc7.1 henc7.2.1 henc7.2.2 (by decide)
  have hle7 : (s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18) = false := by
    have : le0 (s18.mem.get 18) = false := by
      rw [hs18T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs19eq : step s18 = { s18 with pc := 1242 } := by
    have hif :
        (if s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18
          then (1392 : Word) else s18.pc + 3) = (1242 : Word) := by
      have hfall : s18.pc + 3 = (1242 : Word) := by simp [hs18pc]
      simp [hle7, hfall]
    rw [hjlez7, hif]
  have hrun19 : runN s 19 = step s18 := by
    have hS : runN s 19 = runN s18 1 := runN_add_eq s 18 1 19 (by decide)
    exact hS.trans (runN_one s18 hs18h hpc18)
  let s19 := runN s 19
  have hs19pc : s19.pc = 1242 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]
  have hs19h : s19.halted = false := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18h
  have hs19Z : s19.mem.get 0 = 0 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18Z
  have hs19T : s19.mem.get 18 = 5 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18T
  have hI19 : s19.mem.get 29 = 12 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hI18
  have hCH19 : s19.mem.get 30 = s.mem.get 30 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hCH18
  have hONE19 : s19.mem.get 3 = 1 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hONE18
  have hpres19 : ∀ a, a ≠ 18 → a ≠ 0 → s19.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s19 = step s18 := hrun19
    rw [this, hs19eq]; exact hpres18 a ha18 ha0
  have g19 := sc_code_shrink (s := s) (s' := s19) (lo := 1242) (hi := 1245)
    hpres19 hcode (by decide) (by decide)
  have hdec8 := sc_dec_T_1242 (s := s19) hs19pc hs19h g19
  have hs20eq : step s19 =
      { s19 with mem := s19.mem.set 18 (s19.mem.get 18 - s19.mem.get 3), pc := 1245 } := hdec8
  have hrun20 : runN s 20 = step s19 := by
    have hS : runN s 20 = runN s19 1 := runN_add_eq s 19 1 20 (by decide)
    exact hS.trans (runN_one s19 hs19h (by simp [hs19pc]))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1245 := by have : s20 = step s19 := hrun20; rw [this, hs20eq]
  have hs20h : s20.halted = false := by have : s20 = step s19 := hrun20; rw [this, hs20eq]; exact hs19h
  have hs20Z : s20.mem.get 0 = 0 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 0 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hs19Z
  have hs20T : s20.mem.get 18 = 4 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq, Mem.get_set_eq]
    have h1 : s19.mem.get 18 - s19.mem.get 3 = (5 : Word) - 1 := by
      rw [hs19T, hONE19]
    exact h1.trans (rfl : (5 : Word) - 1 = 4)
  have hI20 : s20.mem.get 29 = 12 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 29 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hI19
  have hCH20 : s20.mem.get 30 = s.mem.get 30 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 30 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hCH19
  have hONE20 : s20.mem.get 3 = 1 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 3 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hONE19
  have hpres20 : ∀ a, a ≠ 18 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 a (s19.mem.get 18 - s19.mem.get 3) ha18).trans
      (hpres19 a ha18 ha0)
  have g20 := sc_code_shrink (s := s) (s' := s20) (lo := 1245) (hi := 1248)
    hpres20 hcode (by decide) (by decide)
  have henc8 := sc_enc_jlez_1245 (s := s20) hs20pc g20
  have hpc20 : s20.pc.toNat < 32768 := by simp [hs20pc]
  have hjlez8 :=
    step_JLEZ (s := s20) (x := 18) (dest := 1407)
      hs20h hpc20 hs20Z henc8.1 henc8.2.1 henc8.2.2 (by decide)
  have hle8 : (s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18) = false := by
    have : le0 (s20.mem.get 18) = false := by
      rw [hs20T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs21eq : step s20 = { s20 with pc := 1248 } := by
    have hif :
        (if s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18
          then (1407 : Word) else s20.pc + 3) = (1248 : Word) := by
      have hfall : s20.pc + 3 = (1248 : Word) := by simp [hs20pc]
      simp [hle8, hfall]
    rw [hjlez8, hif]
  have hrun21 : runN s 21 = step s20 := by
    have hS : runN s 21 = runN s20 1 := runN_add_eq s 20 1 21 (by decide)
    exact hS.trans (runN_one s20 hs20h hpc20)
  let s21 := runN s 21
  have hs21pc : s21.pc = 1248 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]
  have hs21h : s21.halted = false := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20h
  have hs21Z : s21.mem.get 0 = 0 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20Z
  have hs21T : s21.mem.get 18 = 4 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20T
  have hI21 : s21.mem.get 29 = 12 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hI20
  have hCH21 : s21.mem.get 30 = s.mem.get 30 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hCH20
  have hONE21 : s21.mem.get 3 = 1 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hONE20
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s21 = step s20 := hrun21
    rw [this, hs21eq]; exact hpres20 a ha18 ha0
  have g21 := sc_code_shrink (s := s) (s' := s21) (lo := 1248) (hi := 1251)
    hpres21 hcode (by decide) (by decide)
  have hdec9 := sc_dec_T_1248 (s := s21) hs21pc hs21h g21
  have hs22eq : step s21 =
      { s21 with mem := s21.mem.set 18 (s21.mem.get 18 - s21.mem.get 3), pc := 1251 } := hdec9
  have hrun22 : runN s 22 = step s21 := by
    have hS : runN s 22 = runN s21 1 := runN_add_eq s 21 1 22 (by decide)
    exact hS.trans (runN_one s21 hs21h (by simp [hs21pc]))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1251 := by have : s22 = step s21 := hrun22; rw [this, hs22eq]
  have hs22h : s22.halted = false := by have : s22 = step s21 := hrun22; rw [this, hs22eq]; exact hs21h
  have hs22Z : s22.mem.get 0 = 0 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 0 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hs21Z
  have hs22T : s22.mem.get 18 = 3 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq, Mem.get_set_eq]
    have h1 : s21.mem.get 18 - s21.mem.get 3 = (4 : Word) - 1 := by
      rw [hs21T, hONE21]
    exact h1.trans (rfl : (4 : Word) - 1 = 3)
  have hI22 : s22.mem.get 29 = 12 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 29 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hI21
  have hCH22 : s22.mem.get 30 = s.mem.get 30 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 30 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hCH21
  have hONE22 : s22.mem.get 3 = 1 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 3 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hONE21
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 0 → s22.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 a (s21.mem.get 18 - s21.mem.get 3) ha18).trans
      (hpres21 a ha18 ha0)
  have g22 := sc_code_shrink (s := s) (s' := s22) (lo := 1251) (hi := 1254)
    hpres22 hcode (by decide) (by decide)
  have henc9 := sc_enc_jlez_1251 (s := s22) hs22pc g22
  have hpc22 : s22.pc.toNat < 32768 := by simp [hs22pc]
  have hjlez9 :=
    step_JLEZ (s := s22) (x := 18) (dest := 1422)
      hs22h hpc22 hs22Z henc9.1 henc9.2.1 henc9.2.2 (by decide)
  have hle9 : (s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18) = false := by
    have : le0 (s22.mem.get 18) = false := by
      rw [hs22T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs23eq : step s22 = { s22 with pc := 1254 } := by
    have hif :
        (if s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18
          then (1422 : Word) else s22.pc + 3) = (1254 : Word) := by
      have hfall : s22.pc + 3 = (1254 : Word) := by simp [hs22pc]
      simp [hle9, hfall]
    rw [hjlez9, hif]
  have hrun23 : runN s 23 = step s22 := by
    have hS : runN s 23 = runN s22 1 := runN_add_eq s 22 1 23 (by decide)
    exact hS.trans (runN_one s22 hs22h hpc22)
  let s23 := runN s 23
  have hs23pc : s23.pc = 1254 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]
  have hs23h : s23.halted = false := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22h
  have hs23Z : s23.mem.get 0 = 0 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22Z
  have hs23T : s23.mem.get 18 = 3 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22T
  have hI23 : s23.mem.get 29 = 12 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hI22
  have hCH23 : s23.mem.get 30 = s.mem.get 30 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hCH22
  have hONE23 : s23.mem.get 3 = 1 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hONE22
  have hpres23 : ∀ a, a ≠ 18 → a ≠ 0 → s23.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s23 = step s22 := hrun23
    rw [this, hs23eq]; exact hpres22 a ha18 ha0
  have g23 := sc_code_shrink (s := s) (s' := s23) (lo := 1254) (hi := 1257)
    hpres23 hcode (by decide) (by decide)
  have hdec10 := sc_dec_T_1254 (s := s23) hs23pc hs23h g23
  have hs24eq : step s23 =
      { s23 with mem := s23.mem.set 18 (s23.mem.get 18 - s23.mem.get 3), pc := 1257 } := hdec10
  have hrun24 : runN s 24 = step s23 := by
    have hS : runN s 24 = runN s23 1 := runN_add_eq s 23 1 24 (by decide)
    exact hS.trans (runN_one s23 hs23h (by simp [hs23pc]))
  let s24 := runN s 24
  have hs24pc : s24.pc = 1257 := by have : s24 = step s23 := hrun24; rw [this, hs24eq]
  have hs24h : s24.halted = false := by have : s24 = step s23 := hrun24; rw [this, hs24eq]; exact hs23h
  have hs24Z : s24.mem.get 0 = 0 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 0 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hs23Z
  have hs24T : s24.mem.get 18 = 2 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq, Mem.get_set_eq]
    have h1 : s23.mem.get 18 - s23.mem.get 3 = (3 : Word) - 1 := by
      rw [hs23T, hONE23]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hI24 : s24.mem.get 29 = 12 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 29 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hI23
  have hCH24 : s24.mem.get 30 = s.mem.get 30 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 30 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hCH23
  have hONE24 : s24.mem.get 3 = 1 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 3 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hONE23
  have hpres24 : ∀ a, a ≠ 18 → a ≠ 0 → s24.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 a (s23.mem.get 18 - s23.mem.get 3) ha18).trans
      (hpres23 a ha18 ha0)
  have g24 := sc_code_shrink (s := s) (s' := s24) (lo := 1257) (hi := 1260)
    hpres24 hcode (by decide) (by decide)
  have henc10 := sc_enc_jlez_1257 (s := s24) hs24pc g24
  have hpc24 : s24.pc.toNat < 32768 := by simp [hs24pc]
  have hjlez10 :=
    step_JLEZ (s := s24) (x := 18) (dest := 1437)
      hs24h hpc24 hs24Z henc10.1 henc10.2.1 henc10.2.2 (by decide)
  have hle10 : (s24.mem.get 18 = 0 || 0x8000 ≤ s24.mem.get 18) = false := by
    have : le0 (s24.mem.get 18) = false := by
      rw [hs24T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs25eq : step s24 = { s24 with pc := 1260 } := by
    have hif :
        (if s24.mem.get 18 = 0 || 0x8000 ≤ s24.mem.get 18
          then (1437 : Word) else s24.pc + 3) = (1260 : Word) := by
      have hfall : s24.pc + 3 = (1260 : Word) := by simp [hs24pc]
      simp [hle10, hfall]
    rw [hjlez10, hif]
  have hrun25 : runN s 25 = step s24 := by
    have hS : runN s 25 = runN s24 1 := runN_add_eq s 24 1 25 (by decide)
    exact hS.trans (runN_one s24 hs24h hpc24)
  let s25 := runN s 25
  have hs25pc : s25.pc = 1260 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]
  have hs25h : s25.halted = false := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24h
  have hs25Z : s25.mem.get 0 = 0 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24Z
  have hs25T : s25.mem.get 18 = 2 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24T
  have hI25 : s25.mem.get 29 = 12 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hI24
  have hCH25 : s25.mem.get 30 = s.mem.get 30 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hCH24
  have hONE25 : s25.mem.get 3 = 1 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hONE24
  have hpres25 : ∀ a, a ≠ 18 → a ≠ 0 → s25.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s25 = step s24 := hrun25
    rw [this, hs25eq]; exact hpres24 a ha18 ha0
  have g25 := sc_code_shrink (s := s) (s' := s25) (lo := 1260) (hi := 1263)
    hpres25 hcode (by decide) (by decide)
  have hdec11 := sc_dec_T_1260 (s := s25) hs25pc hs25h g25
  have hs26eq : step s25 =
      { s25 with mem := s25.mem.set 18 (s25.mem.get 18 - s25.mem.get 3), pc := 1263 } := hdec11
  have hrun26 : runN s 26 = step s25 := by
    have hS : runN s 26 = runN s25 1 := runN_add_eq s 25 1 26 (by decide)
    exact hS.trans (runN_one s25 hs25h (by simp [hs25pc]))
  let s26 := runN s 26
  have hs26pc : s26.pc = 1263 := by have : s26 = step s25 := hrun26; rw [this, hs26eq]
  have hs26h : s26.halted = false := by have : s26 = step s25 := hrun26; rw [this, hs26eq]; exact hs25h
  have hs26Z : s26.mem.get 0 = 0 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 0 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hs25Z
  have hs26T : s26.mem.get 18 = 1 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq, Mem.get_set_eq]
    have h1 : s25.mem.get 18 - s25.mem.get 3 = (2 : Word) - 1 := by
      rw [hs25T, hONE25]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI26 : s26.mem.get 29 = 12 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 29 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hI25
  have hCH26 : s26.mem.get 30 = s.mem.get 30 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 30 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hCH25
  have hONE26 : s26.mem.get 3 = 1 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 3 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hONE25
  have hpres26 : ∀ a, a ≠ 18 → a ≠ 0 → s26.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 a (s25.mem.get 18 - s25.mem.get 3) ha18).trans
      (hpres25 a ha18 ha0)
  have g26 := sc_code_shrink (s := s) (s' := s26) (lo := 1263) (hi := 1266)
    hpres26 hcode (by decide) (by decide)
  have henc11 := sc_enc_jlez_1263 (s := s26) hs26pc g26
  have hpc26 : s26.pc.toNat < 32768 := by simp [hs26pc]
  have hjlez11 :=
    step_JLEZ (s := s26) (x := 18) (dest := 1452)
      hs26h hpc26 hs26Z henc11.1 henc11.2.1 henc11.2.2 (by decide)
  have hle11 : (s26.mem.get 18 = 0 || 0x8000 ≤ s26.mem.get 18) = false := by
    have : le0 (s26.mem.get 18) = false := by
      rw [hs26T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs27eq : step s26 = { s26 with pc := 1266 } := by
    have hif :
        (if s26.mem.get 18 = 0 || 0x8000 ≤ s26.mem.get 18
          then (1452 : Word) else s26.pc + 3) = (1266 : Word) := by
      have hfall : s26.pc + 3 = (1266 : Word) := by simp [hs26pc]
      simp [hle11, hfall]
    rw [hjlez11, hif]
  have hrun27 : runN s 27 = step s26 := by
    have hS : runN s 27 = runN s26 1 := runN_add_eq s 26 1 27 (by decide)
    exact hS.trans (runN_one s26 hs26h hpc26)
  let s27 := runN s 27
  have hs27pc : s27.pc = 1266 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]
  have hs27h : s27.halted = false := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26h
  have hs27Z : s27.mem.get 0 = 0 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26Z
  have hs27T : s27.mem.get 18 = 1 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26T
  have hI27 : s27.mem.get 29 = 12 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hI26
  have hCH27 : s27.mem.get 30 = s.mem.get 30 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hCH26
  have hONE27 : s27.mem.get 3 = 1 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hONE26
  have hpres27 : ∀ a, a ≠ 18 → a ≠ 0 → s27.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s27 = step s26 := hrun27
    rw [this, hs27eq]; exact hpres26 a ha18 ha0
  have g27 := sc_code_shrink (s := s) (s' := s27) (lo := 1266) (hi := 1269)
    hpres27 hcode (by decide) (by decide)
  have hdec12 := sc_dec_T_1266 (s := s27) hs27pc hs27h g27
  have hs28eq : step s27 =
      { s27 with mem := s27.mem.set 18 (s27.mem.get 18 - s27.mem.get 3), pc := 1269 } := hdec12
  have hrun28 : runN s 28 = step s27 := by
    have hS : runN s 28 = runN s27 1 := runN_add_eq s 27 1 28 (by decide)
    exact hS.trans (runN_one s27 hs27h (by simp [hs27pc]))
  let s28 := runN s 28
  have hs28pc : s28.pc = 1269 := by have : s28 = step s27 := hrun28; rw [this, hs28eq]
  have hs28h : s28.halted = false := by have : s28 = step s27 := hrun28; rw [this, hs28eq]; exact hs27h
  have hs28Z : s28.mem.get 0 = 0 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 0 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hs27Z
  have hs28T : s28.mem.get 18 = 0 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq, Mem.get_set_eq]
    have h1 : s27.mem.get 18 - s27.mem.get 3 = (1 : Word) - 1 := by
      rw [hs27T, hONE27]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI28 : s28.mem.get 29 = 12 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 29 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hI27
  have hCH28 : s28.mem.get 30 = s.mem.get 30 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 30 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hCH27
  have hONE28 : s28.mem.get 3 = 1 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 3 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hONE27
  have hpres28 : ∀ a, a ≠ 18 → a ≠ 0 → s28.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 a (s27.mem.get 18 - s27.mem.get 3) ha18).trans
      (hpres27 a ha18 ha0)
  have g28 := sc_code_shrink (s := s) (s' := s28) (lo := 1269) (hi := 1272)
    hpres28 hcode (by decide) (by decide)
  have henc12 := sc_enc_jlez_1269 (s := s28) hs28pc g28
  have hpc28 : s28.pc.toNat < 32768 := by simp [hs28pc]
  have hjlez12 :=
    step_JLEZ (s := s28) (x := 18) (dest := 1467)
      hs28h hpc28 hs28Z henc12.1 henc12.2.1 henc12.2.2 (by decide)
  have hle12 : (s28.mem.get 18 = 0 || 0x8000 ≤ s28.mem.get 18) = true := by
    have : le0 (s28.mem.get 18) = true := by
      rw [hs28T]; exact le0_zero
    simpa [le0] using this
  have hs29eq : step s28 = { s28 with pc := 1467 } := by
    have hif :
        (if s28.mem.get 18 = 0 || 0x8000 ≤ s28.mem.get 18
          then (1467 : Word) else s28.pc + 3) = (1467 : Word) := by
      simp [hle12]
    rw [hjlez12, hif]
  have hrun29 : runN s 29 = step s28 := by
    have hS : runN s 29 = runN s28 1 := runN_add_eq s 28 1 29 (by decide)
    exact hS.trans (runN_one s28 hs28h hpc28)
  let s29 := runN s 29
  have hs29pc : s29.pc = 1467 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]
  have hs29h : s29.halted = false := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hs28h
  have hs29Z : s29.mem.get 0 = 0 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hs28Z
  have hs29T : s29.mem.get 18 = 0 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hs28T
  have hI29 : s29.mem.get 29 = 12 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hI28
  have hCH29 : s29.mem.get 30 = s.mem.get 30 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hCH28
  have hONE29 : s29.mem.get 3 = 1 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hONE28
  have hpres29 : ∀ a, a ≠ 18 → a ≠ 0 → s29.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s29 = step s28 := hrun29
    rw [this, hs29eq]; exact hpres28 a ha18 ha0
  have g29 := sc_code_shrink (s := s) (s' := s29) (lo := 1467) (hi := 1482)
    hpres29 hcode (by decide) (by decide)
  have hs := st12_store (s := s29) hs29pc hs29h hs29Z g29
  have hrun : sN = runN s29 5 := runN_add_eq s 29 5 34 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 44 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH29
  have hsNI : sN.mem.get 29 = 12 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI29
  have hpres : ∀ a, a ≠ 44 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres29 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 13` at `STORE_CH`: 36 steps to `STORED`, `BUF+13 = CH`. -/
theorem store_ch_idx13 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 13)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 36
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 45 = s.mem.get 30 ∧
    sN.mem.get 29 = 13 ∧
    (∀ a, a ≠ 45 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 13 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 13 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 13 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 13 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 12 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (13 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (13 : Word) - 1 = 12)
  have hI6 : s6.mem.get 29 = 13 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 12 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 13 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 11 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (12 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (12 : Word) - 1 = 11)
  have hI8 : s8.mem.get 29 = 13 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1212 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1212 : Word) := by
      have hfall : s8.pc + 3 = (1212 : Word) := by simp [hs8pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1212 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 11 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 13 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1212) (hi := 1215)
    hpres9 hcode (by decide) (by decide)
  have hdec3 := sc_dec_T_1212 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1215 } := hdec3
  have hrun10 : runN s 10 = step s9 := by
    have hS : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hS.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1215 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : s10.mem.get 18 = 10 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (11 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (11 : Word) - 1 = 10)
  have hI10 : s10.mem.get 29 = 13 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hI9
  have hCH10 : s10.mem.get 30 = s.mem.get 30 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 30 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hCH9
  have hONE10 : s10.mem.get 3 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 3 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have g10 := sc_code_shrink (s := s) (s' := s10) (lo := 1215) (hi := 1218)
    hpres10 hcode (by decide) (by decide)
  have henc3 := sc_enc_jlez_1215 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjlez3 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1332)
      hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = false := by
    have : le0 (s10.mem.get 18) = false := by
      rw [hs10T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq : step s10 = { s10 with pc := 1218 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1332 : Word) else s10.pc + 3) = (1218 : Word) := by
      have hfall : s10.pc + 3 = (1218 : Word) := by simp [hs10pc]
      simp [hle3, hfall]
    rw [hjlez3, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hS : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hS.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1218 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11T : s11.mem.get 18 = 10 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10T
  have hI11 : s11.mem.get 29 = 13 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hI10
  have hCH11 : s11.mem.get 30 = s.mem.get 30 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hCH10
  have hONE11 : s11.mem.get 3 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hONE10
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq]; exact hpres10 a ha18 ha0
  have g11 := sc_code_shrink (s := s) (s' := s11) (lo := 1218) (hi := 1221)
    hpres11 hcode (by decide) (by decide)
  have hdec4 := sc_dec_T_1218 (s := s11) hs11pc hs11h g11
  have hs12eq : step s11 =
      { s11 with mem := s11.mem.set 18 (s11.mem.get 18 - s11.mem.get 3), pc := 1221 } := hdec4
  have hrun12 : runN s 12 = step s11 := by
    have hS : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hS.trans (runN_one s11 hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1221 := by have : s12 = step s11 := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step s11 := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 0 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hs11Z
  have hs12T : s12.mem.get 18 = 9 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq, Mem.get_set_eq]
    have h1 : s11.mem.get 18 - s11.mem.get 3 = (10 : Word) - 1 := by
      rw [hs11T, hONE11]
    exact h1.trans (rfl : (10 : Word) - 1 = 9)
  have hI12 : s12.mem.get 29 = 13 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 29 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hI11
  have hCH12 : s12.mem.get 30 = s.mem.get 30 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 30 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hCH11
  have hONE12 : s12.mem.get 3 = 1 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 3 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hONE11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 a (s11.mem.get 18 - s11.mem.get 3) ha18).trans
      (hpres11 a ha18 ha0)
  have g12 := sc_code_shrink (s := s) (s' := s12) (lo := 1221) (hi := 1224)
    hpres12 hcode (by decide) (by decide)
  have henc4 := sc_enc_jlez_1221 (s := s12) hs12pc g12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hjlez4 :=
    step_JLEZ (s := s12) (x := 18) (dest := 1347)
      hs12h hpc12 hs12Z henc4.1 henc4.2.1 henc4.2.2 (by decide)
  have hle4 : (s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18) = false := by
    have : le0 (s12.mem.get 18) = false := by
      rw [hs12T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs13eq : step s12 = { s12 with pc := 1224 } := by
    have hif :
        (if s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18
          then (1347 : Word) else s12.pc + 3) = (1224 : Word) := by
      have hfall : s12.pc + 3 = (1224 : Word) := by simp [hs12pc]
      simp [hle4, hfall]
    rw [hjlez4, hif]
  have hrun13 : runN s 13 = step s12 := by
    have hS : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    exact hS.trans (runN_one s12 hs12h hpc12)
  let s13 := runN s 13
  have hs13pc : s13.pc = 1224 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]
  have hs13h : s13.halted = false := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12Z
  have hs13T : s13.mem.get 18 = 9 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12T
  have hI13 : s13.mem.get 29 = 13 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hI12
  have hCH13 : s13.mem.get 30 = s.mem.get 30 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hCH12
  have hONE13 : s13.mem.get 3 = 1 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hONE12
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s13 = step s12 := hrun13
    rw [this, hs13eq]; exact hpres12 a ha18 ha0
  have g13 := sc_code_shrink (s := s) (s' := s13) (lo := 1224) (hi := 1227)
    hpres13 hcode (by decide) (by decide)
  have hdec5 := sc_dec_T_1224 (s := s13) hs13pc hs13h g13
  have hs14eq : step s13 =
      { s13 with mem := s13.mem.set 18 (s13.mem.get 18 - s13.mem.get 3), pc := 1227 } := hdec5
  have hrun14 : runN s 14 = step s13 := by
    have hS : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hS.trans (runN_one s13 hs13h (by simp [hs13pc]))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1227 := by have : s14 = step s13 := hrun14; rw [this, hs14eq]
  have hs14h : s14.halted = false := by have : s14 = step s13 := hrun14; rw [this, hs14eq]; exact hs13h
  have hs14Z : s14.mem.get 0 = 0 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 0 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hs13Z
  have hs14T : s14.mem.get 18 = 8 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq, Mem.get_set_eq]
    have h1 : s13.mem.get 18 - s13.mem.get 3 = (9 : Word) - 1 := by
      rw [hs13T, hONE13]
    exact h1.trans (rfl : (9 : Word) - 1 = 8)
  have hI14 : s14.mem.get 29 = 13 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 29 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hI13
  have hCH14 : s14.mem.get 30 = s.mem.get 30 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 30 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hCH13
  have hONE14 : s14.mem.get 3 = 1 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 3 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hONE13
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 a (s13.mem.get 18 - s13.mem.get 3) ha18).trans
      (hpres13 a ha18 ha0)
  have g14 := sc_code_shrink (s := s) (s' := s14) (lo := 1227) (hi := 1230)
    hpres14 hcode (by decide) (by decide)
  have henc5 := sc_enc_jlez_1227 (s := s14) hs14pc g14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hjlez5 :=
    step_JLEZ (s := s14) (x := 18) (dest := 1362)
      hs14h hpc14 hs14Z henc5.1 henc5.2.1 henc5.2.2 (by decide)
  have hle5 : (s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18) = false := by
    have : le0 (s14.mem.get 18) = false := by
      rw [hs14T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs15eq : step s14 = { s14 with pc := 1230 } := by
    have hif :
        (if s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18
          then (1362 : Word) else s14.pc + 3) = (1230 : Word) := by
      have hfall : s14.pc + 3 = (1230 : Word) := by simp [hs14pc]
      simp [hle5, hfall]
    rw [hjlez5, hif]
  have hrun15 : runN s 15 = step s14 := by
    have hS : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    exact hS.trans (runN_one s14 hs14h hpc14)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1230 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]
  have hs15h : s15.halted = false := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14Z
  have hs15T : s15.mem.get 18 = 8 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14T
  have hI15 : s15.mem.get 29 = 13 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hI14
  have hCH15 : s15.mem.get 30 = s.mem.get 30 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hCH14
  have hONE15 : s15.mem.get 3 = 1 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hONE14
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s15 = step s14 := hrun15
    rw [this, hs15eq]; exact hpres14 a ha18 ha0
  have g15 := sc_code_shrink (s := s) (s' := s15) (lo := 1230) (hi := 1233)
    hpres15 hcode (by decide) (by decide)
  have hdec6 := sc_dec_T_1230 (s := s15) hs15pc hs15h g15
  have hs16eq : step s15 =
      { s15 with mem := s15.mem.set 18 (s15.mem.get 18 - s15.mem.get 3), pc := 1233 } := hdec6
  have hrun16 : runN s 16 = step s15 := by
    have hS : runN s 16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
    exact hS.trans (runN_one s15 hs15h (by simp [hs15pc]))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1233 := by have : s16 = step s15 := hrun16; rw [this, hs16eq]
  have hs16h : s16.halted = false := by have : s16 = step s15 := hrun16; rw [this, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 0 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hs15Z
  have hs16T : s16.mem.get 18 = 7 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq, Mem.get_set_eq]
    have h1 : s15.mem.get 18 - s15.mem.get 3 = (8 : Word) - 1 := by
      rw [hs15T, hONE15]
    exact h1.trans (rfl : (8 : Word) - 1 = 7)
  have hI16 : s16.mem.get 29 = 13 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 29 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hI15
  have hCH16 : s16.mem.get 30 = s.mem.get 30 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 30 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hCH15
  have hONE16 : s16.mem.get 3 = 1 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 3 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hONE15
  have hpres16 : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 a (s15.mem.get 18 - s15.mem.get 3) ha18).trans
      (hpres15 a ha18 ha0)
  have g16 := sc_code_shrink (s := s) (s' := s16) (lo := 1233) (hi := 1236)
    hpres16 hcode (by decide) (by decide)
  have henc6 := sc_enc_jlez_1233 (s := s16) hs16pc g16
  have hpc16 : s16.pc.toNat < 32768 := by simp [hs16pc]
  have hjlez6 :=
    step_JLEZ (s := s16) (x := 18) (dest := 1377)
      hs16h hpc16 hs16Z henc6.1 henc6.2.1 henc6.2.2 (by decide)
  have hle6 : (s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18) = false := by
    have : le0 (s16.mem.get 18) = false := by
      rw [hs16T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs17eq : step s16 = { s16 with pc := 1236 } := by
    have hif :
        (if s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18
          then (1377 : Word) else s16.pc + 3) = (1236 : Word) := by
      have hfall : s16.pc + 3 = (1236 : Word) := by simp [hs16pc]
      simp [hle6, hfall]
    rw [hjlez6, hif]
  have hrun17 : runN s 17 = step s16 := by
    have hS : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
    exact hS.trans (runN_one s16 hs16h hpc16)
  let s17 := runN s 17
  have hs17pc : s17.pc = 1236 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]
  have hs17h : s17.halted = false := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16h
  have hs17Z : s17.mem.get 0 = 0 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16Z
  have hs17T : s17.mem.get 18 = 7 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16T
  have hI17 : s17.mem.get 29 = 13 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hI16
  have hCH17 : s17.mem.get 30 = s.mem.get 30 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hCH16
  have hONE17 : s17.mem.get 3 = 1 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hONE16
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s17 = step s16 := hrun17
    rw [this, hs17eq]; exact hpres16 a ha18 ha0
  have g17 := sc_code_shrink (s := s) (s' := s17) (lo := 1236) (hi := 1239)
    hpres17 hcode (by decide) (by decide)
  have hdec7 := sc_dec_T_1236 (s := s17) hs17pc hs17h g17
  have hs18eq : step s17 =
      { s17 with mem := s17.mem.set 18 (s17.mem.get 18 - s17.mem.get 3), pc := 1239 } := hdec7
  have hrun18 : runN s 18 = step s17 := by
    have hS : runN s 18 = runN s17 1 := runN_add_eq s 17 1 18 (by decide)
    exact hS.trans (runN_one s17 hs17h (by simp [hs17pc]))
  let s18 := runN s 18
  have hs18pc : s18.pc = 1239 := by have : s18 = step s17 := hrun18; rw [this, hs18eq]
  have hs18h : s18.halted = false := by have : s18 = step s17 := hrun18; rw [this, hs18eq]; exact hs17h
  have hs18Z : s18.mem.get 0 = 0 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 0 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hs17Z
  have hs18T : s18.mem.get 18 = 6 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq, Mem.get_set_eq]
    have h1 : s17.mem.get 18 - s17.mem.get 3 = (7 : Word) - 1 := by
      rw [hs17T, hONE17]
    exact h1.trans (rfl : (7 : Word) - 1 = 6)
  have hI18 : s18.mem.get 29 = 13 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 29 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hI17
  have hCH18 : s18.mem.get 30 = s.mem.get 30 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 30 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hCH17
  have hONE18 : s18.mem.get 3 = 1 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 3 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hONE17
  have hpres18 : ∀ a, a ≠ 18 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 a (s17.mem.get 18 - s17.mem.get 3) ha18).trans
      (hpres17 a ha18 ha0)
  have g18 := sc_code_shrink (s := s) (s' := s18) (lo := 1239) (hi := 1242)
    hpres18 hcode (by decide) (by decide)
  have henc7 := sc_enc_jlez_1239 (s := s18) hs18pc g18
  have hpc18 : s18.pc.toNat < 32768 := by simp [hs18pc]
  have hjlez7 :=
    step_JLEZ (s := s18) (x := 18) (dest := 1392)
      hs18h hpc18 hs18Z henc7.1 henc7.2.1 henc7.2.2 (by decide)
  have hle7 : (s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18) = false := by
    have : le0 (s18.mem.get 18) = false := by
      rw [hs18T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs19eq : step s18 = { s18 with pc := 1242 } := by
    have hif :
        (if s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18
          then (1392 : Word) else s18.pc + 3) = (1242 : Word) := by
      have hfall : s18.pc + 3 = (1242 : Word) := by simp [hs18pc]
      simp [hle7, hfall]
    rw [hjlez7, hif]
  have hrun19 : runN s 19 = step s18 := by
    have hS : runN s 19 = runN s18 1 := runN_add_eq s 18 1 19 (by decide)
    exact hS.trans (runN_one s18 hs18h hpc18)
  let s19 := runN s 19
  have hs19pc : s19.pc = 1242 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]
  have hs19h : s19.halted = false := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18h
  have hs19Z : s19.mem.get 0 = 0 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18Z
  have hs19T : s19.mem.get 18 = 6 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18T
  have hI19 : s19.mem.get 29 = 13 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hI18
  have hCH19 : s19.mem.get 30 = s.mem.get 30 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hCH18
  have hONE19 : s19.mem.get 3 = 1 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hONE18
  have hpres19 : ∀ a, a ≠ 18 → a ≠ 0 → s19.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s19 = step s18 := hrun19
    rw [this, hs19eq]; exact hpres18 a ha18 ha0
  have g19 := sc_code_shrink (s := s) (s' := s19) (lo := 1242) (hi := 1245)
    hpres19 hcode (by decide) (by decide)
  have hdec8 := sc_dec_T_1242 (s := s19) hs19pc hs19h g19
  have hs20eq : step s19 =
      { s19 with mem := s19.mem.set 18 (s19.mem.get 18 - s19.mem.get 3), pc := 1245 } := hdec8
  have hrun20 : runN s 20 = step s19 := by
    have hS : runN s 20 = runN s19 1 := runN_add_eq s 19 1 20 (by decide)
    exact hS.trans (runN_one s19 hs19h (by simp [hs19pc]))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1245 := by have : s20 = step s19 := hrun20; rw [this, hs20eq]
  have hs20h : s20.halted = false := by have : s20 = step s19 := hrun20; rw [this, hs20eq]; exact hs19h
  have hs20Z : s20.mem.get 0 = 0 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 0 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hs19Z
  have hs20T : s20.mem.get 18 = 5 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq, Mem.get_set_eq]
    have h1 : s19.mem.get 18 - s19.mem.get 3 = (6 : Word) - 1 := by
      rw [hs19T, hONE19]
    exact h1.trans (rfl : (6 : Word) - 1 = 5)
  have hI20 : s20.mem.get 29 = 13 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 29 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hI19
  have hCH20 : s20.mem.get 30 = s.mem.get 30 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 30 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hCH19
  have hONE20 : s20.mem.get 3 = 1 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 3 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hONE19
  have hpres20 : ∀ a, a ≠ 18 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 a (s19.mem.get 18 - s19.mem.get 3) ha18).trans
      (hpres19 a ha18 ha0)
  have g20 := sc_code_shrink (s := s) (s' := s20) (lo := 1245) (hi := 1248)
    hpres20 hcode (by decide) (by decide)
  have henc8 := sc_enc_jlez_1245 (s := s20) hs20pc g20
  have hpc20 : s20.pc.toNat < 32768 := by simp [hs20pc]
  have hjlez8 :=
    step_JLEZ (s := s20) (x := 18) (dest := 1407)
      hs20h hpc20 hs20Z henc8.1 henc8.2.1 henc8.2.2 (by decide)
  have hle8 : (s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18) = false := by
    have : le0 (s20.mem.get 18) = false := by
      rw [hs20T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs21eq : step s20 = { s20 with pc := 1248 } := by
    have hif :
        (if s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18
          then (1407 : Word) else s20.pc + 3) = (1248 : Word) := by
      have hfall : s20.pc + 3 = (1248 : Word) := by simp [hs20pc]
      simp [hle8, hfall]
    rw [hjlez8, hif]
  have hrun21 : runN s 21 = step s20 := by
    have hS : runN s 21 = runN s20 1 := runN_add_eq s 20 1 21 (by decide)
    exact hS.trans (runN_one s20 hs20h hpc20)
  let s21 := runN s 21
  have hs21pc : s21.pc = 1248 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]
  have hs21h : s21.halted = false := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20h
  have hs21Z : s21.mem.get 0 = 0 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20Z
  have hs21T : s21.mem.get 18 = 5 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20T
  have hI21 : s21.mem.get 29 = 13 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hI20
  have hCH21 : s21.mem.get 30 = s.mem.get 30 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hCH20
  have hONE21 : s21.mem.get 3 = 1 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hONE20
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s21 = step s20 := hrun21
    rw [this, hs21eq]; exact hpres20 a ha18 ha0
  have g21 := sc_code_shrink (s := s) (s' := s21) (lo := 1248) (hi := 1251)
    hpres21 hcode (by decide) (by decide)
  have hdec9 := sc_dec_T_1248 (s := s21) hs21pc hs21h g21
  have hs22eq : step s21 =
      { s21 with mem := s21.mem.set 18 (s21.mem.get 18 - s21.mem.get 3), pc := 1251 } := hdec9
  have hrun22 : runN s 22 = step s21 := by
    have hS : runN s 22 = runN s21 1 := runN_add_eq s 21 1 22 (by decide)
    exact hS.trans (runN_one s21 hs21h (by simp [hs21pc]))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1251 := by have : s22 = step s21 := hrun22; rw [this, hs22eq]
  have hs22h : s22.halted = false := by have : s22 = step s21 := hrun22; rw [this, hs22eq]; exact hs21h
  have hs22Z : s22.mem.get 0 = 0 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 0 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hs21Z
  have hs22T : s22.mem.get 18 = 4 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq, Mem.get_set_eq]
    have h1 : s21.mem.get 18 - s21.mem.get 3 = (5 : Word) - 1 := by
      rw [hs21T, hONE21]
    exact h1.trans (rfl : (5 : Word) - 1 = 4)
  have hI22 : s22.mem.get 29 = 13 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 29 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hI21
  have hCH22 : s22.mem.get 30 = s.mem.get 30 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 30 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hCH21
  have hONE22 : s22.mem.get 3 = 1 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 3 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hONE21
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 0 → s22.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 a (s21.mem.get 18 - s21.mem.get 3) ha18).trans
      (hpres21 a ha18 ha0)
  have g22 := sc_code_shrink (s := s) (s' := s22) (lo := 1251) (hi := 1254)
    hpres22 hcode (by decide) (by decide)
  have henc9 := sc_enc_jlez_1251 (s := s22) hs22pc g22
  have hpc22 : s22.pc.toNat < 32768 := by simp [hs22pc]
  have hjlez9 :=
    step_JLEZ (s := s22) (x := 18) (dest := 1422)
      hs22h hpc22 hs22Z henc9.1 henc9.2.1 henc9.2.2 (by decide)
  have hle9 : (s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18) = false := by
    have : le0 (s22.mem.get 18) = false := by
      rw [hs22T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs23eq : step s22 = { s22 with pc := 1254 } := by
    have hif :
        (if s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18
          then (1422 : Word) else s22.pc + 3) = (1254 : Word) := by
      have hfall : s22.pc + 3 = (1254 : Word) := by simp [hs22pc]
      simp [hle9, hfall]
    rw [hjlez9, hif]
  have hrun23 : runN s 23 = step s22 := by
    have hS : runN s 23 = runN s22 1 := runN_add_eq s 22 1 23 (by decide)
    exact hS.trans (runN_one s22 hs22h hpc22)
  let s23 := runN s 23
  have hs23pc : s23.pc = 1254 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]
  have hs23h : s23.halted = false := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22h
  have hs23Z : s23.mem.get 0 = 0 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22Z
  have hs23T : s23.mem.get 18 = 4 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22T
  have hI23 : s23.mem.get 29 = 13 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hI22
  have hCH23 : s23.mem.get 30 = s.mem.get 30 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hCH22
  have hONE23 : s23.mem.get 3 = 1 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hONE22
  have hpres23 : ∀ a, a ≠ 18 → a ≠ 0 → s23.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s23 = step s22 := hrun23
    rw [this, hs23eq]; exact hpres22 a ha18 ha0
  have g23 := sc_code_shrink (s := s) (s' := s23) (lo := 1254) (hi := 1257)
    hpres23 hcode (by decide) (by decide)
  have hdec10 := sc_dec_T_1254 (s := s23) hs23pc hs23h g23
  have hs24eq : step s23 =
      { s23 with mem := s23.mem.set 18 (s23.mem.get 18 - s23.mem.get 3), pc := 1257 } := hdec10
  have hrun24 : runN s 24 = step s23 := by
    have hS : runN s 24 = runN s23 1 := runN_add_eq s 23 1 24 (by decide)
    exact hS.trans (runN_one s23 hs23h (by simp [hs23pc]))
  let s24 := runN s 24
  have hs24pc : s24.pc = 1257 := by have : s24 = step s23 := hrun24; rw [this, hs24eq]
  have hs24h : s24.halted = false := by have : s24 = step s23 := hrun24; rw [this, hs24eq]; exact hs23h
  have hs24Z : s24.mem.get 0 = 0 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 0 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hs23Z
  have hs24T : s24.mem.get 18 = 3 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq, Mem.get_set_eq]
    have h1 : s23.mem.get 18 - s23.mem.get 3 = (4 : Word) - 1 := by
      rw [hs23T, hONE23]
    exact h1.trans (rfl : (4 : Word) - 1 = 3)
  have hI24 : s24.mem.get 29 = 13 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 29 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hI23
  have hCH24 : s24.mem.get 30 = s.mem.get 30 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 30 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hCH23
  have hONE24 : s24.mem.get 3 = 1 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 3 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hONE23
  have hpres24 : ∀ a, a ≠ 18 → a ≠ 0 → s24.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 a (s23.mem.get 18 - s23.mem.get 3) ha18).trans
      (hpres23 a ha18 ha0)
  have g24 := sc_code_shrink (s := s) (s' := s24) (lo := 1257) (hi := 1260)
    hpres24 hcode (by decide) (by decide)
  have henc10 := sc_enc_jlez_1257 (s := s24) hs24pc g24
  have hpc24 : s24.pc.toNat < 32768 := by simp [hs24pc]
  have hjlez10 :=
    step_JLEZ (s := s24) (x := 18) (dest := 1437)
      hs24h hpc24 hs24Z henc10.1 henc10.2.1 henc10.2.2 (by decide)
  have hle10 : (s24.mem.get 18 = 0 || 0x8000 ≤ s24.mem.get 18) = false := by
    have : le0 (s24.mem.get 18) = false := by
      rw [hs24T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs25eq : step s24 = { s24 with pc := 1260 } := by
    have hif :
        (if s24.mem.get 18 = 0 || 0x8000 ≤ s24.mem.get 18
          then (1437 : Word) else s24.pc + 3) = (1260 : Word) := by
      have hfall : s24.pc + 3 = (1260 : Word) := by simp [hs24pc]
      simp [hle10, hfall]
    rw [hjlez10, hif]
  have hrun25 : runN s 25 = step s24 := by
    have hS : runN s 25 = runN s24 1 := runN_add_eq s 24 1 25 (by decide)
    exact hS.trans (runN_one s24 hs24h hpc24)
  let s25 := runN s 25
  have hs25pc : s25.pc = 1260 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]
  have hs25h : s25.halted = false := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24h
  have hs25Z : s25.mem.get 0 = 0 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24Z
  have hs25T : s25.mem.get 18 = 3 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24T
  have hI25 : s25.mem.get 29 = 13 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hI24
  have hCH25 : s25.mem.get 30 = s.mem.get 30 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hCH24
  have hONE25 : s25.mem.get 3 = 1 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hONE24
  have hpres25 : ∀ a, a ≠ 18 → a ≠ 0 → s25.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s25 = step s24 := hrun25
    rw [this, hs25eq]; exact hpres24 a ha18 ha0
  have g25 := sc_code_shrink (s := s) (s' := s25) (lo := 1260) (hi := 1263)
    hpres25 hcode (by decide) (by decide)
  have hdec11 := sc_dec_T_1260 (s := s25) hs25pc hs25h g25
  have hs26eq : step s25 =
      { s25 with mem := s25.mem.set 18 (s25.mem.get 18 - s25.mem.get 3), pc := 1263 } := hdec11
  have hrun26 : runN s 26 = step s25 := by
    have hS : runN s 26 = runN s25 1 := runN_add_eq s 25 1 26 (by decide)
    exact hS.trans (runN_one s25 hs25h (by simp [hs25pc]))
  let s26 := runN s 26
  have hs26pc : s26.pc = 1263 := by have : s26 = step s25 := hrun26; rw [this, hs26eq]
  have hs26h : s26.halted = false := by have : s26 = step s25 := hrun26; rw [this, hs26eq]; exact hs25h
  have hs26Z : s26.mem.get 0 = 0 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 0 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hs25Z
  have hs26T : s26.mem.get 18 = 2 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq, Mem.get_set_eq]
    have h1 : s25.mem.get 18 - s25.mem.get 3 = (3 : Word) - 1 := by
      rw [hs25T, hONE25]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hI26 : s26.mem.get 29 = 13 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 29 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hI25
  have hCH26 : s26.mem.get 30 = s.mem.get 30 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 30 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hCH25
  have hONE26 : s26.mem.get 3 = 1 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 3 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hONE25
  have hpres26 : ∀ a, a ≠ 18 → a ≠ 0 → s26.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 a (s25.mem.get 18 - s25.mem.get 3) ha18).trans
      (hpres25 a ha18 ha0)
  have g26 := sc_code_shrink (s := s) (s' := s26) (lo := 1263) (hi := 1266)
    hpres26 hcode (by decide) (by decide)
  have henc11 := sc_enc_jlez_1263 (s := s26) hs26pc g26
  have hpc26 : s26.pc.toNat < 32768 := by simp [hs26pc]
  have hjlez11 :=
    step_JLEZ (s := s26) (x := 18) (dest := 1452)
      hs26h hpc26 hs26Z henc11.1 henc11.2.1 henc11.2.2 (by decide)
  have hle11 : (s26.mem.get 18 = 0 || 0x8000 ≤ s26.mem.get 18) = false := by
    have : le0 (s26.mem.get 18) = false := by
      rw [hs26T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs27eq : step s26 = { s26 with pc := 1266 } := by
    have hif :
        (if s26.mem.get 18 = 0 || 0x8000 ≤ s26.mem.get 18
          then (1452 : Word) else s26.pc + 3) = (1266 : Word) := by
      have hfall : s26.pc + 3 = (1266 : Word) := by simp [hs26pc]
      simp [hle11, hfall]
    rw [hjlez11, hif]
  have hrun27 : runN s 27 = step s26 := by
    have hS : runN s 27 = runN s26 1 := runN_add_eq s 26 1 27 (by decide)
    exact hS.trans (runN_one s26 hs26h hpc26)
  let s27 := runN s 27
  have hs27pc : s27.pc = 1266 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]
  have hs27h : s27.halted = false := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26h
  have hs27Z : s27.mem.get 0 = 0 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26Z
  have hs27T : s27.mem.get 18 = 2 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26T
  have hI27 : s27.mem.get 29 = 13 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hI26
  have hCH27 : s27.mem.get 30 = s.mem.get 30 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hCH26
  have hONE27 : s27.mem.get 3 = 1 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hONE26
  have hpres27 : ∀ a, a ≠ 18 → a ≠ 0 → s27.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s27 = step s26 := hrun27
    rw [this, hs27eq]; exact hpres26 a ha18 ha0
  have g27 := sc_code_shrink (s := s) (s' := s27) (lo := 1266) (hi := 1269)
    hpres27 hcode (by decide) (by decide)
  have hdec12 := sc_dec_T_1266 (s := s27) hs27pc hs27h g27
  have hs28eq : step s27 =
      { s27 with mem := s27.mem.set 18 (s27.mem.get 18 - s27.mem.get 3), pc := 1269 } := hdec12
  have hrun28 : runN s 28 = step s27 := by
    have hS : runN s 28 = runN s27 1 := runN_add_eq s 27 1 28 (by decide)
    exact hS.trans (runN_one s27 hs27h (by simp [hs27pc]))
  let s28 := runN s 28
  have hs28pc : s28.pc = 1269 := by have : s28 = step s27 := hrun28; rw [this, hs28eq]
  have hs28h : s28.halted = false := by have : s28 = step s27 := hrun28; rw [this, hs28eq]; exact hs27h
  have hs28Z : s28.mem.get 0 = 0 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 0 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hs27Z
  have hs28T : s28.mem.get 18 = 1 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq, Mem.get_set_eq]
    have h1 : s27.mem.get 18 - s27.mem.get 3 = (2 : Word) - 1 := by
      rw [hs27T, hONE27]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI28 : s28.mem.get 29 = 13 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 29 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hI27
  have hCH28 : s28.mem.get 30 = s.mem.get 30 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 30 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hCH27
  have hONE28 : s28.mem.get 3 = 1 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 3 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hONE27
  have hpres28 : ∀ a, a ≠ 18 → a ≠ 0 → s28.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 a (s27.mem.get 18 - s27.mem.get 3) ha18).trans
      (hpres27 a ha18 ha0)
  have g28 := sc_code_shrink (s := s) (s' := s28) (lo := 1269) (hi := 1272)
    hpres28 hcode (by decide) (by decide)
  have henc12 := sc_enc_jlez_1269 (s := s28) hs28pc g28
  have hpc28 : s28.pc.toNat < 32768 := by simp [hs28pc]
  have hjlez12 :=
    step_JLEZ (s := s28) (x := 18) (dest := 1467)
      hs28h hpc28 hs28Z henc12.1 henc12.2.1 henc12.2.2 (by decide)
  have hle12 : (s28.mem.get 18 = 0 || 0x8000 ≤ s28.mem.get 18) = false := by
    have : le0 (s28.mem.get 18) = false := by
      rw [hs28T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs29eq : step s28 = { s28 with pc := 1272 } := by
    have hif :
        (if s28.mem.get 18 = 0 || 0x8000 ≤ s28.mem.get 18
          then (1467 : Word) else s28.pc + 3) = (1272 : Word) := by
      have hfall : s28.pc + 3 = (1272 : Word) := by simp [hs28pc]
      simp [hle12, hfall]
    rw [hjlez12, hif]
  have hrun29 : runN s 29 = step s28 := by
    have hS : runN s 29 = runN s28 1 := runN_add_eq s 28 1 29 (by decide)
    exact hS.trans (runN_one s28 hs28h hpc28)
  let s29 := runN s 29
  have hs29pc : s29.pc = 1272 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]
  have hs29h : s29.halted = false := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hs28h
  have hs29Z : s29.mem.get 0 = 0 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hs28Z
  have hs29T : s29.mem.get 18 = 1 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hs28T
  have hI29 : s29.mem.get 29 = 13 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hI28
  have hCH29 : s29.mem.get 30 = s.mem.get 30 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hCH28
  have hONE29 : s29.mem.get 3 = 1 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hONE28
  have hpres29 : ∀ a, a ≠ 18 → a ≠ 0 → s29.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s29 = step s28 := hrun29
    rw [this, hs29eq]; exact hpres28 a ha18 ha0
  have g29 := sc_code_shrink (s := s) (s' := s29) (lo := 1272) (hi := 1275)
    hpres29 hcode (by decide) (by decide)
  have hdec13 := sc_dec_T_1272 (s := s29) hs29pc hs29h g29
  have hs30eq : step s29 =
      { s29 with mem := s29.mem.set 18 (s29.mem.get 18 - s29.mem.get 3), pc := 1275 } := hdec13
  have hrun30 : runN s 30 = step s29 := by
    have hS : runN s 30 = runN s29 1 := runN_add_eq s 29 1 30 (by decide)
    exact hS.trans (runN_one s29 hs29h (by simp [hs29pc]))
  let s30 := runN s 30
  have hs30pc : s30.pc = 1275 := by have : s30 = step s29 := hrun30; rw [this, hs30eq]
  have hs30h : s30.halted = false := by have : s30 = step s29 := hrun30; rw [this, hs30eq]; exact hs29h
  have hs30Z : s30.mem.get 0 = 0 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 0 (s29.mem.get 18 - s29.mem.get 3) (by decide)).trans hs29Z
  have hs30T : s30.mem.get 18 = 0 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq, Mem.get_set_eq]
    have h1 : s29.mem.get 18 - s29.mem.get 3 = (1 : Word) - 1 := by
      rw [hs29T, hONE29]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI30 : s30.mem.get 29 = 13 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 29 (s29.mem.get 18 - s29.mem.get 3) (by decide)).trans hI29
  have hCH30 : s30.mem.get 30 = s.mem.get 30 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 30 (s29.mem.get 18 - s29.mem.get 3) (by decide)).trans hCH29
  have hONE30 : s30.mem.get 3 = 1 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 3 (s29.mem.get 18 - s29.mem.get 3) (by decide)).trans hONE29
  have hpres30 : ∀ a, a ≠ 18 → a ≠ 0 → s30.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 a (s29.mem.get 18 - s29.mem.get 3) ha18).trans
      (hpres29 a ha18 ha0)
  have g30 := sc_code_shrink (s := s) (s' := s30) (lo := 1275) (hi := 1278)
    hpres30 hcode (by decide) (by decide)
  have henc13 := sc_enc_jlez_1275 (s := s30) hs30pc g30
  have hpc30 : s30.pc.toNat < 32768 := by simp [hs30pc]
  have hjlez13 :=
    step_JLEZ (s := s30) (x := 18) (dest := 1482)
      hs30h hpc30 hs30Z henc13.1 henc13.2.1 henc13.2.2 (by decide)
  have hle13 : (s30.mem.get 18 = 0 || 0x8000 ≤ s30.mem.get 18) = true := by
    have : le0 (s30.mem.get 18) = true := by
      rw [hs30T]; exact le0_zero
    simpa [le0] using this
  have hs31eq : step s30 = { s30 with pc := 1482 } := by
    have hif :
        (if s30.mem.get 18 = 0 || 0x8000 ≤ s30.mem.get 18
          then (1482 : Word) else s30.pc + 3) = (1482 : Word) := by
      simp [hle13]
    rw [hjlez13, hif]
  have hrun31 : runN s 31 = step s30 := by
    have hS : runN s 31 = runN s30 1 := runN_add_eq s 30 1 31 (by decide)
    exact hS.trans (runN_one s30 hs30h hpc30)
  let s31 := runN s 31
  have hs31pc : s31.pc = 1482 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]
  have hs31h : s31.halted = false := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hs30h
  have hs31Z : s31.mem.get 0 = 0 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hs30Z
  have hs31T : s31.mem.get 18 = 0 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hs30T
  have hI31 : s31.mem.get 29 = 13 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hI30
  have hCH31 : s31.mem.get 30 = s.mem.get 30 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hCH30
  have hONE31 : s31.mem.get 3 = 1 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hONE30
  have hpres31 : ∀ a, a ≠ 18 → a ≠ 0 → s31.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s31 = step s30 := hrun31
    rw [this, hs31eq]; exact hpres30 a ha18 ha0
  have g31 := sc_code_shrink (s := s) (s' := s31) (lo := 1482) (hi := 1497)
    hpres31 hcode (by decide) (by decide)
  have hs := st13_store (s := s31) hs31pc hs31h hs31Z g31
  have hrun : sN = runN s31 5 := runN_add_eq s 31 5 36 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 45 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH31
  have hsNI : sN.mem.get 29 = 13 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI31
  have hpres : ∀ a, a ≠ 45 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres31 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 14` at `STORE_CH`: 38 steps to `STORED`, `BUF+14 = CH`. -/
theorem store_ch_idx14 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 14)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 38
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 46 = s.mem.get 30 ∧
    sN.mem.get 29 = 14 ∧
    (∀ a, a ≠ 46 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 14 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 14 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 14 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 14 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 13 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (14 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (14 : Word) - 1 = 13)
  have hI6 : s6.mem.get 29 = 14 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 13 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 14 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 12 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (13 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (13 : Word) - 1 = 12)
  have hI8 : s8.mem.get 29 = 14 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1212 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1212 : Word) := by
      have hfall : s8.pc + 3 = (1212 : Word) := by simp [hs8pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1212 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 12 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 14 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1212) (hi := 1215)
    hpres9 hcode (by decide) (by decide)
  have hdec3 := sc_dec_T_1212 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1215 } := hdec3
  have hrun10 : runN s 10 = step s9 := by
    have hS : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hS.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1215 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : s10.mem.get 18 = 11 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (12 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (12 : Word) - 1 = 11)
  have hI10 : s10.mem.get 29 = 14 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hI9
  have hCH10 : s10.mem.get 30 = s.mem.get 30 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 30 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hCH9
  have hONE10 : s10.mem.get 3 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 3 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have g10 := sc_code_shrink (s := s) (s' := s10) (lo := 1215) (hi := 1218)
    hpres10 hcode (by decide) (by decide)
  have henc3 := sc_enc_jlez_1215 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjlez3 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1332)
      hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = false := by
    have : le0 (s10.mem.get 18) = false := by
      rw [hs10T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq : step s10 = { s10 with pc := 1218 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1332 : Word) else s10.pc + 3) = (1218 : Word) := by
      have hfall : s10.pc + 3 = (1218 : Word) := by simp [hs10pc]
      simp [hle3, hfall]
    rw [hjlez3, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hS : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hS.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1218 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11T : s11.mem.get 18 = 11 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10T
  have hI11 : s11.mem.get 29 = 14 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hI10
  have hCH11 : s11.mem.get 30 = s.mem.get 30 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hCH10
  have hONE11 : s11.mem.get 3 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hONE10
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq]; exact hpres10 a ha18 ha0
  have g11 := sc_code_shrink (s := s) (s' := s11) (lo := 1218) (hi := 1221)
    hpres11 hcode (by decide) (by decide)
  have hdec4 := sc_dec_T_1218 (s := s11) hs11pc hs11h g11
  have hs12eq : step s11 =
      { s11 with mem := s11.mem.set 18 (s11.mem.get 18 - s11.mem.get 3), pc := 1221 } := hdec4
  have hrun12 : runN s 12 = step s11 := by
    have hS : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hS.trans (runN_one s11 hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1221 := by have : s12 = step s11 := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step s11 := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 0 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hs11Z
  have hs12T : s12.mem.get 18 = 10 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq, Mem.get_set_eq]
    have h1 : s11.mem.get 18 - s11.mem.get 3 = (11 : Word) - 1 := by
      rw [hs11T, hONE11]
    exact h1.trans (rfl : (11 : Word) - 1 = 10)
  have hI12 : s12.mem.get 29 = 14 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 29 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hI11
  have hCH12 : s12.mem.get 30 = s.mem.get 30 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 30 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hCH11
  have hONE12 : s12.mem.get 3 = 1 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 3 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hONE11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 a (s11.mem.get 18 - s11.mem.get 3) ha18).trans
      (hpres11 a ha18 ha0)
  have g12 := sc_code_shrink (s := s) (s' := s12) (lo := 1221) (hi := 1224)
    hpres12 hcode (by decide) (by decide)
  have henc4 := sc_enc_jlez_1221 (s := s12) hs12pc g12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hjlez4 :=
    step_JLEZ (s := s12) (x := 18) (dest := 1347)
      hs12h hpc12 hs12Z henc4.1 henc4.2.1 henc4.2.2 (by decide)
  have hle4 : (s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18) = false := by
    have : le0 (s12.mem.get 18) = false := by
      rw [hs12T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs13eq : step s12 = { s12 with pc := 1224 } := by
    have hif :
        (if s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18
          then (1347 : Word) else s12.pc + 3) = (1224 : Word) := by
      have hfall : s12.pc + 3 = (1224 : Word) := by simp [hs12pc]
      simp [hle4, hfall]
    rw [hjlez4, hif]
  have hrun13 : runN s 13 = step s12 := by
    have hS : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    exact hS.trans (runN_one s12 hs12h hpc12)
  let s13 := runN s 13
  have hs13pc : s13.pc = 1224 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]
  have hs13h : s13.halted = false := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12Z
  have hs13T : s13.mem.get 18 = 10 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12T
  have hI13 : s13.mem.get 29 = 14 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hI12
  have hCH13 : s13.mem.get 30 = s.mem.get 30 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hCH12
  have hONE13 : s13.mem.get 3 = 1 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hONE12
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s13 = step s12 := hrun13
    rw [this, hs13eq]; exact hpres12 a ha18 ha0
  have g13 := sc_code_shrink (s := s) (s' := s13) (lo := 1224) (hi := 1227)
    hpres13 hcode (by decide) (by decide)
  have hdec5 := sc_dec_T_1224 (s := s13) hs13pc hs13h g13
  have hs14eq : step s13 =
      { s13 with mem := s13.mem.set 18 (s13.mem.get 18 - s13.mem.get 3), pc := 1227 } := hdec5
  have hrun14 : runN s 14 = step s13 := by
    have hS : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hS.trans (runN_one s13 hs13h (by simp [hs13pc]))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1227 := by have : s14 = step s13 := hrun14; rw [this, hs14eq]
  have hs14h : s14.halted = false := by have : s14 = step s13 := hrun14; rw [this, hs14eq]; exact hs13h
  have hs14Z : s14.mem.get 0 = 0 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 0 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hs13Z
  have hs14T : s14.mem.get 18 = 9 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq, Mem.get_set_eq]
    have h1 : s13.mem.get 18 - s13.mem.get 3 = (10 : Word) - 1 := by
      rw [hs13T, hONE13]
    exact h1.trans (rfl : (10 : Word) - 1 = 9)
  have hI14 : s14.mem.get 29 = 14 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 29 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hI13
  have hCH14 : s14.mem.get 30 = s.mem.get 30 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 30 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hCH13
  have hONE14 : s14.mem.get 3 = 1 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 3 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hONE13
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 a (s13.mem.get 18 - s13.mem.get 3) ha18).trans
      (hpres13 a ha18 ha0)
  have g14 := sc_code_shrink (s := s) (s' := s14) (lo := 1227) (hi := 1230)
    hpres14 hcode (by decide) (by decide)
  have henc5 := sc_enc_jlez_1227 (s := s14) hs14pc g14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hjlez5 :=
    step_JLEZ (s := s14) (x := 18) (dest := 1362)
      hs14h hpc14 hs14Z henc5.1 henc5.2.1 henc5.2.2 (by decide)
  have hle5 : (s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18) = false := by
    have : le0 (s14.mem.get 18) = false := by
      rw [hs14T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs15eq : step s14 = { s14 with pc := 1230 } := by
    have hif :
        (if s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18
          then (1362 : Word) else s14.pc + 3) = (1230 : Word) := by
      have hfall : s14.pc + 3 = (1230 : Word) := by simp [hs14pc]
      simp [hle5, hfall]
    rw [hjlez5, hif]
  have hrun15 : runN s 15 = step s14 := by
    have hS : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    exact hS.trans (runN_one s14 hs14h hpc14)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1230 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]
  have hs15h : s15.halted = false := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14Z
  have hs15T : s15.mem.get 18 = 9 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14T
  have hI15 : s15.mem.get 29 = 14 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hI14
  have hCH15 : s15.mem.get 30 = s.mem.get 30 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hCH14
  have hONE15 : s15.mem.get 3 = 1 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hONE14
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s15 = step s14 := hrun15
    rw [this, hs15eq]; exact hpres14 a ha18 ha0
  have g15 := sc_code_shrink (s := s) (s' := s15) (lo := 1230) (hi := 1233)
    hpres15 hcode (by decide) (by decide)
  have hdec6 := sc_dec_T_1230 (s := s15) hs15pc hs15h g15
  have hs16eq : step s15 =
      { s15 with mem := s15.mem.set 18 (s15.mem.get 18 - s15.mem.get 3), pc := 1233 } := hdec6
  have hrun16 : runN s 16 = step s15 := by
    have hS : runN s 16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
    exact hS.trans (runN_one s15 hs15h (by simp [hs15pc]))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1233 := by have : s16 = step s15 := hrun16; rw [this, hs16eq]
  have hs16h : s16.halted = false := by have : s16 = step s15 := hrun16; rw [this, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 0 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hs15Z
  have hs16T : s16.mem.get 18 = 8 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq, Mem.get_set_eq]
    have h1 : s15.mem.get 18 - s15.mem.get 3 = (9 : Word) - 1 := by
      rw [hs15T, hONE15]
    exact h1.trans (rfl : (9 : Word) - 1 = 8)
  have hI16 : s16.mem.get 29 = 14 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 29 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hI15
  have hCH16 : s16.mem.get 30 = s.mem.get 30 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 30 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hCH15
  have hONE16 : s16.mem.get 3 = 1 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 3 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hONE15
  have hpres16 : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 a (s15.mem.get 18 - s15.mem.get 3) ha18).trans
      (hpres15 a ha18 ha0)
  have g16 := sc_code_shrink (s := s) (s' := s16) (lo := 1233) (hi := 1236)
    hpres16 hcode (by decide) (by decide)
  have henc6 := sc_enc_jlez_1233 (s := s16) hs16pc g16
  have hpc16 : s16.pc.toNat < 32768 := by simp [hs16pc]
  have hjlez6 :=
    step_JLEZ (s := s16) (x := 18) (dest := 1377)
      hs16h hpc16 hs16Z henc6.1 henc6.2.1 henc6.2.2 (by decide)
  have hle6 : (s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18) = false := by
    have : le0 (s16.mem.get 18) = false := by
      rw [hs16T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs17eq : step s16 = { s16 with pc := 1236 } := by
    have hif :
        (if s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18
          then (1377 : Word) else s16.pc + 3) = (1236 : Word) := by
      have hfall : s16.pc + 3 = (1236 : Word) := by simp [hs16pc]
      simp [hle6, hfall]
    rw [hjlez6, hif]
  have hrun17 : runN s 17 = step s16 := by
    have hS : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
    exact hS.trans (runN_one s16 hs16h hpc16)
  let s17 := runN s 17
  have hs17pc : s17.pc = 1236 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]
  have hs17h : s17.halted = false := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16h
  have hs17Z : s17.mem.get 0 = 0 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16Z
  have hs17T : s17.mem.get 18 = 8 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16T
  have hI17 : s17.mem.get 29 = 14 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hI16
  have hCH17 : s17.mem.get 30 = s.mem.get 30 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hCH16
  have hONE17 : s17.mem.get 3 = 1 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hONE16
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s17 = step s16 := hrun17
    rw [this, hs17eq]; exact hpres16 a ha18 ha0
  have g17 := sc_code_shrink (s := s) (s' := s17) (lo := 1236) (hi := 1239)
    hpres17 hcode (by decide) (by decide)
  have hdec7 := sc_dec_T_1236 (s := s17) hs17pc hs17h g17
  have hs18eq : step s17 =
      { s17 with mem := s17.mem.set 18 (s17.mem.get 18 - s17.mem.get 3), pc := 1239 } := hdec7
  have hrun18 : runN s 18 = step s17 := by
    have hS : runN s 18 = runN s17 1 := runN_add_eq s 17 1 18 (by decide)
    exact hS.trans (runN_one s17 hs17h (by simp [hs17pc]))
  let s18 := runN s 18
  have hs18pc : s18.pc = 1239 := by have : s18 = step s17 := hrun18; rw [this, hs18eq]
  have hs18h : s18.halted = false := by have : s18 = step s17 := hrun18; rw [this, hs18eq]; exact hs17h
  have hs18Z : s18.mem.get 0 = 0 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 0 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hs17Z
  have hs18T : s18.mem.get 18 = 7 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq, Mem.get_set_eq]
    have h1 : s17.mem.get 18 - s17.mem.get 3 = (8 : Word) - 1 := by
      rw [hs17T, hONE17]
    exact h1.trans (rfl : (8 : Word) - 1 = 7)
  have hI18 : s18.mem.get 29 = 14 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 29 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hI17
  have hCH18 : s18.mem.get 30 = s.mem.get 30 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 30 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hCH17
  have hONE18 : s18.mem.get 3 = 1 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 3 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hONE17
  have hpres18 : ∀ a, a ≠ 18 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 a (s17.mem.get 18 - s17.mem.get 3) ha18).trans
      (hpres17 a ha18 ha0)
  have g18 := sc_code_shrink (s := s) (s' := s18) (lo := 1239) (hi := 1242)
    hpres18 hcode (by decide) (by decide)
  have henc7 := sc_enc_jlez_1239 (s := s18) hs18pc g18
  have hpc18 : s18.pc.toNat < 32768 := by simp [hs18pc]
  have hjlez7 :=
    step_JLEZ (s := s18) (x := 18) (dest := 1392)
      hs18h hpc18 hs18Z henc7.1 henc7.2.1 henc7.2.2 (by decide)
  have hle7 : (s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18) = false := by
    have : le0 (s18.mem.get 18) = false := by
      rw [hs18T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs19eq : step s18 = { s18 with pc := 1242 } := by
    have hif :
        (if s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18
          then (1392 : Word) else s18.pc + 3) = (1242 : Word) := by
      have hfall : s18.pc + 3 = (1242 : Word) := by simp [hs18pc]
      simp [hle7, hfall]
    rw [hjlez7, hif]
  have hrun19 : runN s 19 = step s18 := by
    have hS : runN s 19 = runN s18 1 := runN_add_eq s 18 1 19 (by decide)
    exact hS.trans (runN_one s18 hs18h hpc18)
  let s19 := runN s 19
  have hs19pc : s19.pc = 1242 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]
  have hs19h : s19.halted = false := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18h
  have hs19Z : s19.mem.get 0 = 0 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18Z
  have hs19T : s19.mem.get 18 = 7 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18T
  have hI19 : s19.mem.get 29 = 14 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hI18
  have hCH19 : s19.mem.get 30 = s.mem.get 30 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hCH18
  have hONE19 : s19.mem.get 3 = 1 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hONE18
  have hpres19 : ∀ a, a ≠ 18 → a ≠ 0 → s19.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s19 = step s18 := hrun19
    rw [this, hs19eq]; exact hpres18 a ha18 ha0
  have g19 := sc_code_shrink (s := s) (s' := s19) (lo := 1242) (hi := 1245)
    hpres19 hcode (by decide) (by decide)
  have hdec8 := sc_dec_T_1242 (s := s19) hs19pc hs19h g19
  have hs20eq : step s19 =
      { s19 with mem := s19.mem.set 18 (s19.mem.get 18 - s19.mem.get 3), pc := 1245 } := hdec8
  have hrun20 : runN s 20 = step s19 := by
    have hS : runN s 20 = runN s19 1 := runN_add_eq s 19 1 20 (by decide)
    exact hS.trans (runN_one s19 hs19h (by simp [hs19pc]))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1245 := by have : s20 = step s19 := hrun20; rw [this, hs20eq]
  have hs20h : s20.halted = false := by have : s20 = step s19 := hrun20; rw [this, hs20eq]; exact hs19h
  have hs20Z : s20.mem.get 0 = 0 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 0 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hs19Z
  have hs20T : s20.mem.get 18 = 6 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq, Mem.get_set_eq]
    have h1 : s19.mem.get 18 - s19.mem.get 3 = (7 : Word) - 1 := by
      rw [hs19T, hONE19]
    exact h1.trans (rfl : (7 : Word) - 1 = 6)
  have hI20 : s20.mem.get 29 = 14 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 29 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hI19
  have hCH20 : s20.mem.get 30 = s.mem.get 30 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 30 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hCH19
  have hONE20 : s20.mem.get 3 = 1 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 3 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hONE19
  have hpres20 : ∀ a, a ≠ 18 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 a (s19.mem.get 18 - s19.mem.get 3) ha18).trans
      (hpres19 a ha18 ha0)
  have g20 := sc_code_shrink (s := s) (s' := s20) (lo := 1245) (hi := 1248)
    hpres20 hcode (by decide) (by decide)
  have henc8 := sc_enc_jlez_1245 (s := s20) hs20pc g20
  have hpc20 : s20.pc.toNat < 32768 := by simp [hs20pc]
  have hjlez8 :=
    step_JLEZ (s := s20) (x := 18) (dest := 1407)
      hs20h hpc20 hs20Z henc8.1 henc8.2.1 henc8.2.2 (by decide)
  have hle8 : (s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18) = false := by
    have : le0 (s20.mem.get 18) = false := by
      rw [hs20T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs21eq : step s20 = { s20 with pc := 1248 } := by
    have hif :
        (if s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18
          then (1407 : Word) else s20.pc + 3) = (1248 : Word) := by
      have hfall : s20.pc + 3 = (1248 : Word) := by simp [hs20pc]
      simp [hle8, hfall]
    rw [hjlez8, hif]
  have hrun21 : runN s 21 = step s20 := by
    have hS : runN s 21 = runN s20 1 := runN_add_eq s 20 1 21 (by decide)
    exact hS.trans (runN_one s20 hs20h hpc20)
  let s21 := runN s 21
  have hs21pc : s21.pc = 1248 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]
  have hs21h : s21.halted = false := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20h
  have hs21Z : s21.mem.get 0 = 0 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20Z
  have hs21T : s21.mem.get 18 = 6 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20T
  have hI21 : s21.mem.get 29 = 14 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hI20
  have hCH21 : s21.mem.get 30 = s.mem.get 30 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hCH20
  have hONE21 : s21.mem.get 3 = 1 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hONE20
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s21 = step s20 := hrun21
    rw [this, hs21eq]; exact hpres20 a ha18 ha0
  have g21 := sc_code_shrink (s := s) (s' := s21) (lo := 1248) (hi := 1251)
    hpres21 hcode (by decide) (by decide)
  have hdec9 := sc_dec_T_1248 (s := s21) hs21pc hs21h g21
  have hs22eq : step s21 =
      { s21 with mem := s21.mem.set 18 (s21.mem.get 18 - s21.mem.get 3), pc := 1251 } := hdec9
  have hrun22 : runN s 22 = step s21 := by
    have hS : runN s 22 = runN s21 1 := runN_add_eq s 21 1 22 (by decide)
    exact hS.trans (runN_one s21 hs21h (by simp [hs21pc]))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1251 := by have : s22 = step s21 := hrun22; rw [this, hs22eq]
  have hs22h : s22.halted = false := by have : s22 = step s21 := hrun22; rw [this, hs22eq]; exact hs21h
  have hs22Z : s22.mem.get 0 = 0 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 0 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hs21Z
  have hs22T : s22.mem.get 18 = 5 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq, Mem.get_set_eq]
    have h1 : s21.mem.get 18 - s21.mem.get 3 = (6 : Word) - 1 := by
      rw [hs21T, hONE21]
    exact h1.trans (rfl : (6 : Word) - 1 = 5)
  have hI22 : s22.mem.get 29 = 14 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 29 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hI21
  have hCH22 : s22.mem.get 30 = s.mem.get 30 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 30 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hCH21
  have hONE22 : s22.mem.get 3 = 1 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 3 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hONE21
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 0 → s22.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 a (s21.mem.get 18 - s21.mem.get 3) ha18).trans
      (hpres21 a ha18 ha0)
  have g22 := sc_code_shrink (s := s) (s' := s22) (lo := 1251) (hi := 1254)
    hpres22 hcode (by decide) (by decide)
  have henc9 := sc_enc_jlez_1251 (s := s22) hs22pc g22
  have hpc22 : s22.pc.toNat < 32768 := by simp [hs22pc]
  have hjlez9 :=
    step_JLEZ (s := s22) (x := 18) (dest := 1422)
      hs22h hpc22 hs22Z henc9.1 henc9.2.1 henc9.2.2 (by decide)
  have hle9 : (s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18) = false := by
    have : le0 (s22.mem.get 18) = false := by
      rw [hs22T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs23eq : step s22 = { s22 with pc := 1254 } := by
    have hif :
        (if s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18
          then (1422 : Word) else s22.pc + 3) = (1254 : Word) := by
      have hfall : s22.pc + 3 = (1254 : Word) := by simp [hs22pc]
      simp [hle9, hfall]
    rw [hjlez9, hif]
  have hrun23 : runN s 23 = step s22 := by
    have hS : runN s 23 = runN s22 1 := runN_add_eq s 22 1 23 (by decide)
    exact hS.trans (runN_one s22 hs22h hpc22)
  let s23 := runN s 23
  have hs23pc : s23.pc = 1254 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]
  have hs23h : s23.halted = false := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22h
  have hs23Z : s23.mem.get 0 = 0 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22Z
  have hs23T : s23.mem.get 18 = 5 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22T
  have hI23 : s23.mem.get 29 = 14 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hI22
  have hCH23 : s23.mem.get 30 = s.mem.get 30 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hCH22
  have hONE23 : s23.mem.get 3 = 1 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hONE22
  have hpres23 : ∀ a, a ≠ 18 → a ≠ 0 → s23.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s23 = step s22 := hrun23
    rw [this, hs23eq]; exact hpres22 a ha18 ha0
  have g23 := sc_code_shrink (s := s) (s' := s23) (lo := 1254) (hi := 1257)
    hpres23 hcode (by decide) (by decide)
  have hdec10 := sc_dec_T_1254 (s := s23) hs23pc hs23h g23
  have hs24eq : step s23 =
      { s23 with mem := s23.mem.set 18 (s23.mem.get 18 - s23.mem.get 3), pc := 1257 } := hdec10
  have hrun24 : runN s 24 = step s23 := by
    have hS : runN s 24 = runN s23 1 := runN_add_eq s 23 1 24 (by decide)
    exact hS.trans (runN_one s23 hs23h (by simp [hs23pc]))
  let s24 := runN s 24
  have hs24pc : s24.pc = 1257 := by have : s24 = step s23 := hrun24; rw [this, hs24eq]
  have hs24h : s24.halted = false := by have : s24 = step s23 := hrun24; rw [this, hs24eq]; exact hs23h
  have hs24Z : s24.mem.get 0 = 0 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 0 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hs23Z
  have hs24T : s24.mem.get 18 = 4 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq, Mem.get_set_eq]
    have h1 : s23.mem.get 18 - s23.mem.get 3 = (5 : Word) - 1 := by
      rw [hs23T, hONE23]
    exact h1.trans (rfl : (5 : Word) - 1 = 4)
  have hI24 : s24.mem.get 29 = 14 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 29 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hI23
  have hCH24 : s24.mem.get 30 = s.mem.get 30 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 30 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hCH23
  have hONE24 : s24.mem.get 3 = 1 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 3 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hONE23
  have hpres24 : ∀ a, a ≠ 18 → a ≠ 0 → s24.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 a (s23.mem.get 18 - s23.mem.get 3) ha18).trans
      (hpres23 a ha18 ha0)
  have g24 := sc_code_shrink (s := s) (s' := s24) (lo := 1257) (hi := 1260)
    hpres24 hcode (by decide) (by decide)
  have henc10 := sc_enc_jlez_1257 (s := s24) hs24pc g24
  have hpc24 : s24.pc.toNat < 32768 := by simp [hs24pc]
  have hjlez10 :=
    step_JLEZ (s := s24) (x := 18) (dest := 1437)
      hs24h hpc24 hs24Z henc10.1 henc10.2.1 henc10.2.2 (by decide)
  have hle10 : (s24.mem.get 18 = 0 || 0x8000 ≤ s24.mem.get 18) = false := by
    have : le0 (s24.mem.get 18) = false := by
      rw [hs24T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs25eq : step s24 = { s24 with pc := 1260 } := by
    have hif :
        (if s24.mem.get 18 = 0 || 0x8000 ≤ s24.mem.get 18
          then (1437 : Word) else s24.pc + 3) = (1260 : Word) := by
      have hfall : s24.pc + 3 = (1260 : Word) := by simp [hs24pc]
      simp [hle10, hfall]
    rw [hjlez10, hif]
  have hrun25 : runN s 25 = step s24 := by
    have hS : runN s 25 = runN s24 1 := runN_add_eq s 24 1 25 (by decide)
    exact hS.trans (runN_one s24 hs24h hpc24)
  let s25 := runN s 25
  have hs25pc : s25.pc = 1260 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]
  have hs25h : s25.halted = false := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24h
  have hs25Z : s25.mem.get 0 = 0 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24Z
  have hs25T : s25.mem.get 18 = 4 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24T
  have hI25 : s25.mem.get 29 = 14 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hI24
  have hCH25 : s25.mem.get 30 = s.mem.get 30 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hCH24
  have hONE25 : s25.mem.get 3 = 1 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hONE24
  have hpres25 : ∀ a, a ≠ 18 → a ≠ 0 → s25.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s25 = step s24 := hrun25
    rw [this, hs25eq]; exact hpres24 a ha18 ha0
  have g25 := sc_code_shrink (s := s) (s' := s25) (lo := 1260) (hi := 1263)
    hpres25 hcode (by decide) (by decide)
  have hdec11 := sc_dec_T_1260 (s := s25) hs25pc hs25h g25
  have hs26eq : step s25 =
      { s25 with mem := s25.mem.set 18 (s25.mem.get 18 - s25.mem.get 3), pc := 1263 } := hdec11
  have hrun26 : runN s 26 = step s25 := by
    have hS : runN s 26 = runN s25 1 := runN_add_eq s 25 1 26 (by decide)
    exact hS.trans (runN_one s25 hs25h (by simp [hs25pc]))
  let s26 := runN s 26
  have hs26pc : s26.pc = 1263 := by have : s26 = step s25 := hrun26; rw [this, hs26eq]
  have hs26h : s26.halted = false := by have : s26 = step s25 := hrun26; rw [this, hs26eq]; exact hs25h
  have hs26Z : s26.mem.get 0 = 0 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 0 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hs25Z
  have hs26T : s26.mem.get 18 = 3 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq, Mem.get_set_eq]
    have h1 : s25.mem.get 18 - s25.mem.get 3 = (4 : Word) - 1 := by
      rw [hs25T, hONE25]
    exact h1.trans (rfl : (4 : Word) - 1 = 3)
  have hI26 : s26.mem.get 29 = 14 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 29 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hI25
  have hCH26 : s26.mem.get 30 = s.mem.get 30 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 30 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hCH25
  have hONE26 : s26.mem.get 3 = 1 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 3 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hONE25
  have hpres26 : ∀ a, a ≠ 18 → a ≠ 0 → s26.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 a (s25.mem.get 18 - s25.mem.get 3) ha18).trans
      (hpres25 a ha18 ha0)
  have g26 := sc_code_shrink (s := s) (s' := s26) (lo := 1263) (hi := 1266)
    hpres26 hcode (by decide) (by decide)
  have henc11 := sc_enc_jlez_1263 (s := s26) hs26pc g26
  have hpc26 : s26.pc.toNat < 32768 := by simp [hs26pc]
  have hjlez11 :=
    step_JLEZ (s := s26) (x := 18) (dest := 1452)
      hs26h hpc26 hs26Z henc11.1 henc11.2.1 henc11.2.2 (by decide)
  have hle11 : (s26.mem.get 18 = 0 || 0x8000 ≤ s26.mem.get 18) = false := by
    have : le0 (s26.mem.get 18) = false := by
      rw [hs26T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs27eq : step s26 = { s26 with pc := 1266 } := by
    have hif :
        (if s26.mem.get 18 = 0 || 0x8000 ≤ s26.mem.get 18
          then (1452 : Word) else s26.pc + 3) = (1266 : Word) := by
      have hfall : s26.pc + 3 = (1266 : Word) := by simp [hs26pc]
      simp [hle11, hfall]
    rw [hjlez11, hif]
  have hrun27 : runN s 27 = step s26 := by
    have hS : runN s 27 = runN s26 1 := runN_add_eq s 26 1 27 (by decide)
    exact hS.trans (runN_one s26 hs26h hpc26)
  let s27 := runN s 27
  have hs27pc : s27.pc = 1266 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]
  have hs27h : s27.halted = false := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26h
  have hs27Z : s27.mem.get 0 = 0 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26Z
  have hs27T : s27.mem.get 18 = 3 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26T
  have hI27 : s27.mem.get 29 = 14 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hI26
  have hCH27 : s27.mem.get 30 = s.mem.get 30 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hCH26
  have hONE27 : s27.mem.get 3 = 1 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hONE26
  have hpres27 : ∀ a, a ≠ 18 → a ≠ 0 → s27.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s27 = step s26 := hrun27
    rw [this, hs27eq]; exact hpres26 a ha18 ha0
  have g27 := sc_code_shrink (s := s) (s' := s27) (lo := 1266) (hi := 1269)
    hpres27 hcode (by decide) (by decide)
  have hdec12 := sc_dec_T_1266 (s := s27) hs27pc hs27h g27
  have hs28eq : step s27 =
      { s27 with mem := s27.mem.set 18 (s27.mem.get 18 - s27.mem.get 3), pc := 1269 } := hdec12
  have hrun28 : runN s 28 = step s27 := by
    have hS : runN s 28 = runN s27 1 := runN_add_eq s 27 1 28 (by decide)
    exact hS.trans (runN_one s27 hs27h (by simp [hs27pc]))
  let s28 := runN s 28
  have hs28pc : s28.pc = 1269 := by have : s28 = step s27 := hrun28; rw [this, hs28eq]
  have hs28h : s28.halted = false := by have : s28 = step s27 := hrun28; rw [this, hs28eq]; exact hs27h
  have hs28Z : s28.mem.get 0 = 0 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 0 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hs27Z
  have hs28T : s28.mem.get 18 = 2 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq, Mem.get_set_eq]
    have h1 : s27.mem.get 18 - s27.mem.get 3 = (3 : Word) - 1 := by
      rw [hs27T, hONE27]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hI28 : s28.mem.get 29 = 14 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 29 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hI27
  have hCH28 : s28.mem.get 30 = s.mem.get 30 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 30 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hCH27
  have hONE28 : s28.mem.get 3 = 1 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 3 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hONE27
  have hpres28 : ∀ a, a ≠ 18 → a ≠ 0 → s28.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 a (s27.mem.get 18 - s27.mem.get 3) ha18).trans
      (hpres27 a ha18 ha0)
  have g28 := sc_code_shrink (s := s) (s' := s28) (lo := 1269) (hi := 1272)
    hpres28 hcode (by decide) (by decide)
  have henc12 := sc_enc_jlez_1269 (s := s28) hs28pc g28
  have hpc28 : s28.pc.toNat < 32768 := by simp [hs28pc]
  have hjlez12 :=
    step_JLEZ (s := s28) (x := 18) (dest := 1467)
      hs28h hpc28 hs28Z henc12.1 henc12.2.1 henc12.2.2 (by decide)
  have hle12 : (s28.mem.get 18 = 0 || 0x8000 ≤ s28.mem.get 18) = false := by
    have : le0 (s28.mem.get 18) = false := by
      rw [hs28T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs29eq : step s28 = { s28 with pc := 1272 } := by
    have hif :
        (if s28.mem.get 18 = 0 || 0x8000 ≤ s28.mem.get 18
          then (1467 : Word) else s28.pc + 3) = (1272 : Word) := by
      have hfall : s28.pc + 3 = (1272 : Word) := by simp [hs28pc]
      simp [hle12, hfall]
    rw [hjlez12, hif]
  have hrun29 : runN s 29 = step s28 := by
    have hS : runN s 29 = runN s28 1 := runN_add_eq s 28 1 29 (by decide)
    exact hS.trans (runN_one s28 hs28h hpc28)
  let s29 := runN s 29
  have hs29pc : s29.pc = 1272 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]
  have hs29h : s29.halted = false := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hs28h
  have hs29Z : s29.mem.get 0 = 0 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hs28Z
  have hs29T : s29.mem.get 18 = 2 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hs28T
  have hI29 : s29.mem.get 29 = 14 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hI28
  have hCH29 : s29.mem.get 30 = s.mem.get 30 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hCH28
  have hONE29 : s29.mem.get 3 = 1 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hONE28
  have hpres29 : ∀ a, a ≠ 18 → a ≠ 0 → s29.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s29 = step s28 := hrun29
    rw [this, hs29eq]; exact hpres28 a ha18 ha0
  have g29 := sc_code_shrink (s := s) (s' := s29) (lo := 1272) (hi := 1275)
    hpres29 hcode (by decide) (by decide)
  have hdec13 := sc_dec_T_1272 (s := s29) hs29pc hs29h g29
  have hs30eq : step s29 =
      { s29 with mem := s29.mem.set 18 (s29.mem.get 18 - s29.mem.get 3), pc := 1275 } := hdec13
  have hrun30 : runN s 30 = step s29 := by
    have hS : runN s 30 = runN s29 1 := runN_add_eq s 29 1 30 (by decide)
    exact hS.trans (runN_one s29 hs29h (by simp [hs29pc]))
  let s30 := runN s 30
  have hs30pc : s30.pc = 1275 := by have : s30 = step s29 := hrun30; rw [this, hs30eq]
  have hs30h : s30.halted = false := by have : s30 = step s29 := hrun30; rw [this, hs30eq]; exact hs29h
  have hs30Z : s30.mem.get 0 = 0 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 0 (s29.mem.get 18 - s29.mem.get 3) (by decide)).trans hs29Z
  have hs30T : s30.mem.get 18 = 1 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq, Mem.get_set_eq]
    have h1 : s29.mem.get 18 - s29.mem.get 3 = (2 : Word) - 1 := by
      rw [hs29T, hONE29]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI30 : s30.mem.get 29 = 14 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 29 (s29.mem.get 18 - s29.mem.get 3) (by decide)).trans hI29
  have hCH30 : s30.mem.get 30 = s.mem.get 30 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 30 (s29.mem.get 18 - s29.mem.get 3) (by decide)).trans hCH29
  have hONE30 : s30.mem.get 3 = 1 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 3 (s29.mem.get 18 - s29.mem.get 3) (by decide)).trans hONE29
  have hpres30 : ∀ a, a ≠ 18 → a ≠ 0 → s30.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 a (s29.mem.get 18 - s29.mem.get 3) ha18).trans
      (hpres29 a ha18 ha0)
  have g30 := sc_code_shrink (s := s) (s' := s30) (lo := 1275) (hi := 1278)
    hpres30 hcode (by decide) (by decide)
  have henc13 := sc_enc_jlez_1275 (s := s30) hs30pc g30
  have hpc30 : s30.pc.toNat < 32768 := by simp [hs30pc]
  have hjlez13 :=
    step_JLEZ (s := s30) (x := 18) (dest := 1482)
      hs30h hpc30 hs30Z henc13.1 henc13.2.1 henc13.2.2 (by decide)
  have hle13 : (s30.mem.get 18 = 0 || 0x8000 ≤ s30.mem.get 18) = false := by
    have : le0 (s30.mem.get 18) = false := by
      rw [hs30T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs31eq : step s30 = { s30 with pc := 1278 } := by
    have hif :
        (if s30.mem.get 18 = 0 || 0x8000 ≤ s30.mem.get 18
          then (1482 : Word) else s30.pc + 3) = (1278 : Word) := by
      have hfall : s30.pc + 3 = (1278 : Word) := by simp [hs30pc]
      simp [hle13, hfall]
    rw [hjlez13, hif]
  have hrun31 : runN s 31 = step s30 := by
    have hS : runN s 31 = runN s30 1 := runN_add_eq s 30 1 31 (by decide)
    exact hS.trans (runN_one s30 hs30h hpc30)
  let s31 := runN s 31
  have hs31pc : s31.pc = 1278 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]
  have hs31h : s31.halted = false := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hs30h
  have hs31Z : s31.mem.get 0 = 0 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hs30Z
  have hs31T : s31.mem.get 18 = 1 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hs30T
  have hI31 : s31.mem.get 29 = 14 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hI30
  have hCH31 : s31.mem.get 30 = s.mem.get 30 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hCH30
  have hONE31 : s31.mem.get 3 = 1 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hONE30
  have hpres31 : ∀ a, a ≠ 18 → a ≠ 0 → s31.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s31 = step s30 := hrun31
    rw [this, hs31eq]; exact hpres30 a ha18 ha0
  have g31 := sc_code_shrink (s := s) (s' := s31) (lo := 1278) (hi := 1281)
    hpres31 hcode (by decide) (by decide)
  have hdec14 := sc_dec_T_1278 (s := s31) hs31pc hs31h g31
  have hs32eq : step s31 =
      { s31 with mem := s31.mem.set 18 (s31.mem.get 18 - s31.mem.get 3), pc := 1281 } := hdec14
  have hrun32 : runN s 32 = step s31 := by
    have hS : runN s 32 = runN s31 1 := runN_add_eq s 31 1 32 (by decide)
    exact hS.trans (runN_one s31 hs31h (by simp [hs31pc]))
  let s32 := runN s 32
  have hs32pc : s32.pc = 1281 := by have : s32 = step s31 := hrun32; rw [this, hs32eq]
  have hs32h : s32.halted = false := by have : s32 = step s31 := hrun32; rw [this, hs32eq]; exact hs31h
  have hs32Z : s32.mem.get 0 = 0 := by
    have : s32 = step s31 := hrun32
    rw [this, hs32eq]
    exact (Mem.get_set_ne s31.mem 18 0 (s31.mem.get 18 - s31.mem.get 3) (by decide)).trans hs31Z
  have hs32T : s32.mem.get 18 = 0 := by
    have : s32 = step s31 := hrun32
    rw [this, hs32eq, Mem.get_set_eq]
    have h1 : s31.mem.get 18 - s31.mem.get 3 = (1 : Word) - 1 := by
      rw [hs31T, hONE31]
    exact h1.trans (rfl : (1 : Word) - 1 = 0)
  have hI32 : s32.mem.get 29 = 14 := by
    have : s32 = step s31 := hrun32
    rw [this, hs32eq]
    exact (Mem.get_set_ne s31.mem 18 29 (s31.mem.get 18 - s31.mem.get 3) (by decide)).trans hI31
  have hCH32 : s32.mem.get 30 = s.mem.get 30 := by
    have : s32 = step s31 := hrun32
    rw [this, hs32eq]
    exact (Mem.get_set_ne s31.mem 18 30 (s31.mem.get 18 - s31.mem.get 3) (by decide)).trans hCH31
  have hONE32 : s32.mem.get 3 = 1 := by
    have : s32 = step s31 := hrun32
    rw [this, hs32eq]
    exact (Mem.get_set_ne s31.mem 18 3 (s31.mem.get 18 - s31.mem.get 3) (by decide)).trans hONE31
  have hpres32 : ∀ a, a ≠ 18 → a ≠ 0 → s32.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s32 = step s31 := hrun32
    rw [this, hs32eq]
    exact (Mem.get_set_ne s31.mem 18 a (s31.mem.get 18 - s31.mem.get 3) ha18).trans
      (hpres31 a ha18 ha0)
  have g32 := sc_code_shrink (s := s) (s' := s32) (lo := 1281) (hi := 1284)
    hpres32 hcode (by decide) (by decide)
  have henc14 := sc_enc_jlez_1281 (s := s32) hs32pc g32
  have hpc32 : s32.pc.toNat < 32768 := by simp [hs32pc]
  have hjlez14 :=
    step_JLEZ (s := s32) (x := 18) (dest := 1497)
      hs32h hpc32 hs32Z henc14.1 henc14.2.1 henc14.2.2 (by decide)
  have hle14 : (s32.mem.get 18 = 0 || 0x8000 ≤ s32.mem.get 18) = true := by
    have : le0 (s32.mem.get 18) = true := by
      rw [hs32T]; exact le0_zero
    simpa [le0] using this
  have hs33eq : step s32 = { s32 with pc := 1497 } := by
    have hif :
        (if s32.mem.get 18 = 0 || 0x8000 ≤ s32.mem.get 18
          then (1497 : Word) else s32.pc + 3) = (1497 : Word) := by
      simp [hle14]
    rw [hjlez14, hif]
  have hrun33 : runN s 33 = step s32 := by
    have hS : runN s 33 = runN s32 1 := runN_add_eq s 32 1 33 (by decide)
    exact hS.trans (runN_one s32 hs32h hpc32)
  let s33 := runN s 33
  have hs33pc : s33.pc = 1497 := by have : s33 = step s32 := hrun33; rw [this, hs33eq]
  have hs33h : s33.halted = false := by have : s33 = step s32 := hrun33; rw [this, hs33eq]; exact hs32h
  have hs33Z : s33.mem.get 0 = 0 := by have : s33 = step s32 := hrun33; rw [this, hs33eq]; exact hs32Z
  have hs33T : s33.mem.get 18 = 0 := by have : s33 = step s32 := hrun33; rw [this, hs33eq]; exact hs32T
  have hI33 : s33.mem.get 29 = 14 := by have : s33 = step s32 := hrun33; rw [this, hs33eq]; exact hI32
  have hCH33 : s33.mem.get 30 = s.mem.get 30 := by have : s33 = step s32 := hrun33; rw [this, hs33eq]; exact hCH32
  have hONE33 : s33.mem.get 3 = 1 := by have : s33 = step s32 := hrun33; rw [this, hs33eq]; exact hONE32
  have hpres33 : ∀ a, a ≠ 18 → a ≠ 0 → s33.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s33 = step s32 := hrun33
    rw [this, hs33eq]; exact hpres32 a ha18 ha0
  have g33 := sc_code_shrink (s := s) (s' := s33) (lo := 1497) (hi := 1512)
    hpres33 hcode (by decide) (by decide)
  have hs := st14_store (s := s33) hs33pc hs33h hs33Z g33
  have hrun : sN = runN s33 5 := runN_add_eq s 33 5 38 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 46 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH33
  have hsNI : sN.mem.get 29 = 14 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI33
  have hpres : ∀ a, a ≠ 46 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres33 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

/-- `IDX = 15` at `STORE_CH`: 39 steps to `STORED`, `BUF+15 = CH`. -/
theorem store_ch_idx15 {s : Machine}
    (hpc : s.pc = 1185)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hI : s.mem.get 29 = 15)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sN := runN s 39
    sN.pc = 1527 ∧
    sN.halted = false ∧
    sN.mem.get 0 = 0 ∧
    sN.mem.get 47 = s.mem.get 30 ∧
    sN.mem.get 29 = 15 ∧
    (∀ a, a ≠ 47 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a) := by
  intro sN
  have hm := sc_mov_IDX_T (s := s) hpc hh hZ
    (fun k h1 h2 => hcode k h1 (by omega))
  let s4 := runN s 4
  have hs4pc : s4.pc = 1197 := hm.1
  have hs4h : s4.halted = false := hm.2.1
  have hs4T : s4.mem.get 18 = 15 := hm.2.2.1.trans hI
  have hs4Z : s4.mem.get 0 = 0 := hm.2.2.2.1
  have hpres4 := hm.2.2.2.2.2
  have hI4 : s4.mem.get 29 = 15 := (hpres4 29 (by decide) (by decide)).trans hI
  have hCH4 : s4.mem.get 30 = s.mem.get 30 := hpres4 30 (by decide) (by decide)
  have hONE4 : s4.mem.get 3 = 1 := (hpres4 3 (by decide) (by decide)).trans hONE
  have g4 := sc_code_shrink (s := s) (s' := s4) (lo := 1197) (hi := 1200)
    hpres4 hcode (by decide) (by decide)
  have henc0 := sc_enc_jlez_1197 (s := s4) hs4pc g4
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez0 :=
    step_JLEZ (s := s4) (x := 18) (dest := 1287)
      hs4h hpc4 hs4Z henc0.1 henc0.2.1 henc0.2.2 (by decide)
  have hle0 : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hs4T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 1200 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then (1287 : Word) else s4.pc + 3) = (1200 : Word) := by
      have hfall : s4.pc + 3 = (1200 : Word) := by simp [hs4pc]
      simp [hle0, hfall]
    rw [hjlez0, hif]
  have hrun5 : runN s 5 = step s4 := by
    have h5 : runN s 5 = runN s4 1 := runN_add_eq s 4 1 5 (by decide)
    exact h5.trans (runN_one s4 hs4h hpc4)
  let s5 := runN s 5
  have hs5pc : s5.pc = 1200 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]
  have hs5h : s5.halted = false := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4Z
  have hs5T : s5.mem.get 18 = 15 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hs4T
  have hI5 : s5.mem.get 29 = 15 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hI4
  have hCH5 : s5.mem.get 30 = s.mem.get 30 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hCH4
  have hONE5 : s5.mem.get 3 = 1 := by have : s5 = step s4 := hrun5; rw [this, hs5eq]; exact hONE4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → s5.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s5 = step s4 := hrun5
    rw [this, hs5eq]; exact hpres4 a ha18 ha0
  have g5 := sc_code_shrink (s := s) (s' := s5) (lo := 1200) (hi := 1203)
    hpres5 hcode (by decide) (by decide)
  have hdec1 := sc_dec_T_1200 (s := s5) hs5pc hs5h g5
  have hs6eq : step s5 =
      { s5 with mem := s5.mem.set 18 (s5.mem.get 18 - s5.mem.get 3), pc := 1203 } := hdec1
  have hrun6 : runN s 6 = step s5 := by
    have hS : runN s 6 = runN s5 1 := runN_add_eq s 5 1 6 (by decide)
    exact hS.trans (runN_one s5 hs5h (by simp [hs5pc]))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1203 := by have : s6 = step s5 := hrun6; rw [this, hs6eq]
  have hs6h : s6.halted = false := by have : s6 = step s5 := hrun6; rw [this, hs6eq]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 0 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hs5Z
  have hs6T : s6.mem.get 18 = 14 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq, Mem.get_set_eq]
    have h1 : s5.mem.get 18 - s5.mem.get 3 = (15 : Word) - 1 := by
      rw [hs5T, hONE5]
    exact h1.trans (rfl : (15 : Word) - 1 = 14)
  have hI6 : s6.mem.get 29 = 15 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 29 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hI5
  have hCH6 : s6.mem.get 30 = s.mem.get 30 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 30 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hCH5
  have hONE6 : s6.mem.get 3 = 1 := by
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 3 (s5.mem.get 18 - s5.mem.get 3) (by decide)).trans hONE5
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s6 = step s5 := hrun6
    rw [this, hs6eq]
    exact (Mem.get_set_ne s5.mem 18 a (s5.mem.get 18 - s5.mem.get 3) ha18).trans
      (hpres5 a ha18 ha0)
  have g6 := sc_code_shrink (s := s) (s' := s6) (lo := 1203) (hi := 1206)
    hpres6 hcode (by decide) (by decide)
  have henc1 := sc_enc_jlez_1203 (s := s6) hs6pc g6
  have hpc6 : s6.pc.toNat < 32768 := by simp [hs6pc]
  have hjlez1 :=
    step_JLEZ (s := s6) (x := 18) (dest := 1302)
      hs6h hpc6 hs6Z henc1.1 henc1.2.1 henc1.2.2 (by decide)
  have hle1 : (s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18) = false := by
    have : le0 (s6.mem.get 18) = false := by
      rw [hs6T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs7eq : step s6 = { s6 with pc := 1206 } := by
    have hif :
        (if s6.mem.get 18 = 0 || 0x8000 ≤ s6.mem.get 18
          then (1302 : Word) else s6.pc + 3) = (1206 : Word) := by
      have hfall : s6.pc + 3 = (1206 : Word) := by simp [hs6pc]
      simp [hle1, hfall]
    rw [hjlez1, hif]
  have hrun7 : runN s 7 = step s6 := by
    have hS : runN s 7 = runN s6 1 := runN_add_eq s 6 1 7 (by decide)
    exact hS.trans (runN_one s6 hs6h hpc6)
  let s7 := runN s 7
  have hs7pc : s7.pc = 1206 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]
  have hs7h : s7.halted = false := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6h
  have hs7Z : s7.mem.get 0 = 0 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6Z
  have hs7T : s7.mem.get 18 = 14 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hs6T
  have hI7 : s7.mem.get 29 = 15 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hI6
  have hCH7 : s7.mem.get 30 = s.mem.get 30 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hCH6
  have hONE7 : s7.mem.get 3 = 1 := by have : s7 = step s6 := hrun7; rw [this, hs7eq]; exact hONE6
  have hpres7 : ∀ a, a ≠ 18 → a ≠ 0 → s7.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s7 = step s6 := hrun7
    rw [this, hs7eq]; exact hpres6 a ha18 ha0
  have g7 := sc_code_shrink (s := s) (s' := s7) (lo := 1206) (hi := 1209)
    hpres7 hcode (by decide) (by decide)
  have hdec2 := sc_dec_T_1206 (s := s7) hs7pc hs7h g7
  have hs8eq : step s7 =
      { s7 with mem := s7.mem.set 18 (s7.mem.get 18 - s7.mem.get 3), pc := 1209 } := hdec2
  have hrun8 : runN s 8 = step s7 := by
    have hS : runN s 8 = runN s7 1 := runN_add_eq s 7 1 8 (by decide)
    exact hS.trans (runN_one s7 hs7h (by simp [hs7pc]))
  let s8 := runN s 8
  have hs8pc : s8.pc = 1209 := by have : s8 = step s7 := hrun8; rw [this, hs8eq]
  have hs8h : s8.halted = false := by have : s8 = step s7 := hrun8; rw [this, hs8eq]; exact hs7h
  have hs8Z : s8.mem.get 0 = 0 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 0 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hs7Z
  have hs8T : s8.mem.get 18 = 13 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq, Mem.get_set_eq]
    have h1 : s7.mem.get 18 - s7.mem.get 3 = (14 : Word) - 1 := by
      rw [hs7T, hONE7]
    exact h1.trans (rfl : (14 : Word) - 1 = 13)
  have hI8 : s8.mem.get 29 = 15 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 29 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hI7
  have hCH8 : s8.mem.get 30 = s.mem.get 30 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 30 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hCH7
  have hONE8 : s8.mem.get 3 = 1 := by
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 3 (s7.mem.get 18 - s7.mem.get 3) (by decide)).trans hONE7
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s8 = step s7 := hrun8
    rw [this, hs8eq]
    exact (Mem.get_set_ne s7.mem 18 a (s7.mem.get 18 - s7.mem.get 3) ha18).trans
      (hpres7 a ha18 ha0)
  have g8 := sc_code_shrink (s := s) (s' := s8) (lo := 1209) (hi := 1212)
    hpres8 hcode (by decide) (by decide)
  have henc2 := sc_enc_jlez_1209 (s := s8) hs8pc g8
  have hpc8 : s8.pc.toNat < 32768 := by simp [hs8pc]
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := 1317)
      hs8h hpc8 hs8Z henc2.1 henc2.2.1 henc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hs8T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := 1212 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then (1317 : Word) else s8.pc + 3) = (1212 : Word) := by
      have hfall : s8.pc + 3 = (1212 : Word) := by simp [hs8pc]
      simp [hle2, hfall]
    rw [hjlez2, hif]
  have hrun9 : runN s 9 = step s8 := by
    have hS : runN s 9 = runN s8 1 := runN_add_eq s 8 1 9 (by decide)
    exact hS.trans (runN_one s8 hs8h hpc8)
  let s9 := runN s 9
  have hs9pc : s9.pc = 1212 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]
  have hs9h : s9.halted = false := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8Z
  have hs9T : s9.mem.get 18 = 13 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hs8T
  have hI9 : s9.mem.get 29 = 15 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hI8
  have hCH9 : s9.mem.get 30 = s.mem.get 30 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hCH8
  have hONE9 : s9.mem.get 3 = 1 := by have : s9 = step s8 := hrun9; rw [this, hs9eq]; exact hONE8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s9 = step s8 := hrun9
    rw [this, hs9eq]; exact hpres8 a ha18 ha0
  have g9 := sc_code_shrink (s := s) (s' := s9) (lo := 1212) (hi := 1215)
    hpres9 hcode (by decide) (by decide)
  have hdec3 := sc_dec_T_1212 (s := s9) hs9pc hs9h g9
  have hs10eq : step s9 =
      { s9 with mem := s9.mem.set 18 (s9.mem.get 18 - s9.mem.get 3), pc := 1215 } := hdec3
  have hrun10 : runN s 10 = step s9 := by
    have hS : runN s 10 = runN s9 1 := runN_add_eq s 9 1 10 (by decide)
    exact hS.trans (runN_one s9 hs9h (by simp [hs9pc]))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1215 := by have : s10 = step s9 := hrun10; rw [this, hs10eq]
  have hs10h : s10.halted = false := by have : s10 = step s9 := hrun10; rw [this, hs10eq]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 0 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hs9Z
  have hs10T : s10.mem.get 18 = 12 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq, Mem.get_set_eq]
    have h1 : s9.mem.get 18 - s9.mem.get 3 = (13 : Word) - 1 := by
      rw [hs9T, hONE9]
    exact h1.trans (rfl : (13 : Word) - 1 = 12)
  have hI10 : s10.mem.get 29 = 15 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 29 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hI9
  have hCH10 : s10.mem.get 30 = s.mem.get 30 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 30 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hCH9
  have hONE10 : s10.mem.get 3 = 1 := by
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 3 (s9.mem.get 18 - s9.mem.get 3) (by decide)).trans hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s10 = step s9 := hrun10
    rw [this, hs10eq]
    exact (Mem.get_set_ne s9.mem 18 a (s9.mem.get 18 - s9.mem.get 3) ha18).trans
      (hpres9 a ha18 ha0)
  have g10 := sc_code_shrink (s := s) (s' := s10) (lo := 1215) (hi := 1218)
    hpres10 hcode (by decide) (by decide)
  have henc3 := sc_enc_jlez_1215 (s := s10) hs10pc g10
  have hpc10 : s10.pc.toNat < 32768 := by simp [hs10pc]
  have hjlez3 :=
    step_JLEZ (s := s10) (x := 18) (dest := 1332)
      hs10h hpc10 hs10Z henc3.1 henc3.2.1 henc3.2.2 (by decide)
  have hle3 : (s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18) = false := by
    have : le0 (s10.mem.get 18) = false := by
      rw [hs10T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs11eq : step s10 = { s10 with pc := 1218 } := by
    have hif :
        (if s10.mem.get 18 = 0 || 0x8000 ≤ s10.mem.get 18
          then (1332 : Word) else s10.pc + 3) = (1218 : Word) := by
      have hfall : s10.pc + 3 = (1218 : Word) := by simp [hs10pc]
      simp [hle3, hfall]
    rw [hjlez3, hif]
  have hrun11 : runN s 11 = step s10 := by
    have hS : runN s 11 = runN s10 1 := runN_add_eq s 10 1 11 (by decide)
    exact hS.trans (runN_one s10 hs10h hpc10)
  let s11 := runN s 11
  have hs11pc : s11.pc = 1218 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]
  have hs11h : s11.halted = false := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10Z
  have hs11T : s11.mem.get 18 = 12 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hs10T
  have hI11 : s11.mem.get 29 = 15 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hI10
  have hCH11 : s11.mem.get 30 = s.mem.get 30 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hCH10
  have hONE11 : s11.mem.get 3 = 1 := by have : s11 = step s10 := hrun11; rw [this, hs11eq]; exact hONE10
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s11 = step s10 := hrun11
    rw [this, hs11eq]; exact hpres10 a ha18 ha0
  have g11 := sc_code_shrink (s := s) (s' := s11) (lo := 1218) (hi := 1221)
    hpres11 hcode (by decide) (by decide)
  have hdec4 := sc_dec_T_1218 (s := s11) hs11pc hs11h g11
  have hs12eq : step s11 =
      { s11 with mem := s11.mem.set 18 (s11.mem.get 18 - s11.mem.get 3), pc := 1221 } := hdec4
  have hrun12 : runN s 12 = step s11 := by
    have hS : runN s 12 = runN s11 1 := runN_add_eq s 11 1 12 (by decide)
    exact hS.trans (runN_one s11 hs11h (by simp [hs11pc]))
  let s12 := runN s 12
  have hs12pc : s12.pc = 1221 := by have : s12 = step s11 := hrun12; rw [this, hs12eq]
  have hs12h : s12.halted = false := by have : s12 = step s11 := hrun12; rw [this, hs12eq]; exact hs11h
  have hs12Z : s12.mem.get 0 = 0 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 0 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hs11Z
  have hs12T : s12.mem.get 18 = 11 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq, Mem.get_set_eq]
    have h1 : s11.mem.get 18 - s11.mem.get 3 = (12 : Word) - 1 := by
      rw [hs11T, hONE11]
    exact h1.trans (rfl : (12 : Word) - 1 = 11)
  have hI12 : s12.mem.get 29 = 15 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 29 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hI11
  have hCH12 : s12.mem.get 30 = s.mem.get 30 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 30 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hCH11
  have hONE12 : s12.mem.get 3 = 1 := by
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 3 (s11.mem.get 18 - s11.mem.get 3) (by decide)).trans hONE11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → s12.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s12 = step s11 := hrun12
    rw [this, hs12eq]
    exact (Mem.get_set_ne s11.mem 18 a (s11.mem.get 18 - s11.mem.get 3) ha18).trans
      (hpres11 a ha18 ha0)
  have g12 := sc_code_shrink (s := s) (s' := s12) (lo := 1221) (hi := 1224)
    hpres12 hcode (by decide) (by decide)
  have henc4 := sc_enc_jlez_1221 (s := s12) hs12pc g12
  have hpc12 : s12.pc.toNat < 32768 := by simp [hs12pc]
  have hjlez4 :=
    step_JLEZ (s := s12) (x := 18) (dest := 1347)
      hs12h hpc12 hs12Z henc4.1 henc4.2.1 henc4.2.2 (by decide)
  have hle4 : (s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18) = false := by
    have : le0 (s12.mem.get 18) = false := by
      rw [hs12T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs13eq : step s12 = { s12 with pc := 1224 } := by
    have hif :
        (if s12.mem.get 18 = 0 || 0x8000 ≤ s12.mem.get 18
          then (1347 : Word) else s12.pc + 3) = (1224 : Word) := by
      have hfall : s12.pc + 3 = (1224 : Word) := by simp [hs12pc]
      simp [hle4, hfall]
    rw [hjlez4, hif]
  have hrun13 : runN s 13 = step s12 := by
    have hS : runN s 13 = runN s12 1 := runN_add_eq s 12 1 13 (by decide)
    exact hS.trans (runN_one s12 hs12h hpc12)
  let s13 := runN s 13
  have hs13pc : s13.pc = 1224 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]
  have hs13h : s13.halted = false := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12Z
  have hs13T : s13.mem.get 18 = 11 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hs12T
  have hI13 : s13.mem.get 29 = 15 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hI12
  have hCH13 : s13.mem.get 30 = s.mem.get 30 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hCH12
  have hONE13 : s13.mem.get 3 = 1 := by have : s13 = step s12 := hrun13; rw [this, hs13eq]; exact hONE12
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s13 = step s12 := hrun13
    rw [this, hs13eq]; exact hpres12 a ha18 ha0
  have g13 := sc_code_shrink (s := s) (s' := s13) (lo := 1224) (hi := 1227)
    hpres13 hcode (by decide) (by decide)
  have hdec5 := sc_dec_T_1224 (s := s13) hs13pc hs13h g13
  have hs14eq : step s13 =
      { s13 with mem := s13.mem.set 18 (s13.mem.get 18 - s13.mem.get 3), pc := 1227 } := hdec5
  have hrun14 : runN s 14 = step s13 := by
    have hS : runN s 14 = runN s13 1 := runN_add_eq s 13 1 14 (by decide)
    exact hS.trans (runN_one s13 hs13h (by simp [hs13pc]))
  let s14 := runN s 14
  have hs14pc : s14.pc = 1227 := by have : s14 = step s13 := hrun14; rw [this, hs14eq]
  have hs14h : s14.halted = false := by have : s14 = step s13 := hrun14; rw [this, hs14eq]; exact hs13h
  have hs14Z : s14.mem.get 0 = 0 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 0 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hs13Z
  have hs14T : s14.mem.get 18 = 10 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq, Mem.get_set_eq]
    have h1 : s13.mem.get 18 - s13.mem.get 3 = (11 : Word) - 1 := by
      rw [hs13T, hONE13]
    exact h1.trans (rfl : (11 : Word) - 1 = 10)
  have hI14 : s14.mem.get 29 = 15 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 29 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hI13
  have hCH14 : s14.mem.get 30 = s.mem.get 30 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 30 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hCH13
  have hONE14 : s14.mem.get 3 = 1 := by
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 3 (s13.mem.get 18 - s13.mem.get 3) (by decide)).trans hONE13
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s14 = step s13 := hrun14
    rw [this, hs14eq]
    exact (Mem.get_set_ne s13.mem 18 a (s13.mem.get 18 - s13.mem.get 3) ha18).trans
      (hpres13 a ha18 ha0)
  have g14 := sc_code_shrink (s := s) (s' := s14) (lo := 1227) (hi := 1230)
    hpres14 hcode (by decide) (by decide)
  have henc5 := sc_enc_jlez_1227 (s := s14) hs14pc g14
  have hpc14 : s14.pc.toNat < 32768 := by simp [hs14pc]
  have hjlez5 :=
    step_JLEZ (s := s14) (x := 18) (dest := 1362)
      hs14h hpc14 hs14Z henc5.1 henc5.2.1 henc5.2.2 (by decide)
  have hle5 : (s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18) = false := by
    have : le0 (s14.mem.get 18) = false := by
      rw [hs14T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs15eq : step s14 = { s14 with pc := 1230 } := by
    have hif :
        (if s14.mem.get 18 = 0 || 0x8000 ≤ s14.mem.get 18
          then (1362 : Word) else s14.pc + 3) = (1230 : Word) := by
      have hfall : s14.pc + 3 = (1230 : Word) := by simp [hs14pc]
      simp [hle5, hfall]
    rw [hjlez5, hif]
  have hrun15 : runN s 15 = step s14 := by
    have hS : runN s 15 = runN s14 1 := runN_add_eq s 14 1 15 (by decide)
    exact hS.trans (runN_one s14 hs14h hpc14)
  let s15 := runN s 15
  have hs15pc : s15.pc = 1230 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]
  have hs15h : s15.halted = false := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14Z
  have hs15T : s15.mem.get 18 = 10 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hs14T
  have hI15 : s15.mem.get 29 = 15 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hI14
  have hCH15 : s15.mem.get 30 = s.mem.get 30 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hCH14
  have hONE15 : s15.mem.get 3 = 1 := by have : s15 = step s14 := hrun15; rw [this, hs15eq]; exact hONE14
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s15 = step s14 := hrun15
    rw [this, hs15eq]; exact hpres14 a ha18 ha0
  have g15 := sc_code_shrink (s := s) (s' := s15) (lo := 1230) (hi := 1233)
    hpres15 hcode (by decide) (by decide)
  have hdec6 := sc_dec_T_1230 (s := s15) hs15pc hs15h g15
  have hs16eq : step s15 =
      { s15 with mem := s15.mem.set 18 (s15.mem.get 18 - s15.mem.get 3), pc := 1233 } := hdec6
  have hrun16 : runN s 16 = step s15 := by
    have hS : runN s 16 = runN s15 1 := runN_add_eq s 15 1 16 (by decide)
    exact hS.trans (runN_one s15 hs15h (by simp [hs15pc]))
  let s16 := runN s 16
  have hs16pc : s16.pc = 1233 := by have : s16 = step s15 := hrun16; rw [this, hs16eq]
  have hs16h : s16.halted = false := by have : s16 = step s15 := hrun16; rw [this, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 0 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hs15Z
  have hs16T : s16.mem.get 18 = 9 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq, Mem.get_set_eq]
    have h1 : s15.mem.get 18 - s15.mem.get 3 = (10 : Word) - 1 := by
      rw [hs15T, hONE15]
    exact h1.trans (rfl : (10 : Word) - 1 = 9)
  have hI16 : s16.mem.get 29 = 15 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 29 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hI15
  have hCH16 : s16.mem.get 30 = s.mem.get 30 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 30 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hCH15
  have hONE16 : s16.mem.get 3 = 1 := by
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 3 (s15.mem.get 18 - s15.mem.get 3) (by decide)).trans hONE15
  have hpres16 : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s16 = step s15 := hrun16
    rw [this, hs16eq]
    exact (Mem.get_set_ne s15.mem 18 a (s15.mem.get 18 - s15.mem.get 3) ha18).trans
      (hpres15 a ha18 ha0)
  have g16 := sc_code_shrink (s := s) (s' := s16) (lo := 1233) (hi := 1236)
    hpres16 hcode (by decide) (by decide)
  have henc6 := sc_enc_jlez_1233 (s := s16) hs16pc g16
  have hpc16 : s16.pc.toNat < 32768 := by simp [hs16pc]
  have hjlez6 :=
    step_JLEZ (s := s16) (x := 18) (dest := 1377)
      hs16h hpc16 hs16Z henc6.1 henc6.2.1 henc6.2.2 (by decide)
  have hle6 : (s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18) = false := by
    have : le0 (s16.mem.get 18) = false := by
      rw [hs16T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs17eq : step s16 = { s16 with pc := 1236 } := by
    have hif :
        (if s16.mem.get 18 = 0 || 0x8000 ≤ s16.mem.get 18
          then (1377 : Word) else s16.pc + 3) = (1236 : Word) := by
      have hfall : s16.pc + 3 = (1236 : Word) := by simp [hs16pc]
      simp [hle6, hfall]
    rw [hjlez6, hif]
  have hrun17 : runN s 17 = step s16 := by
    have hS : runN s 17 = runN s16 1 := runN_add_eq s 16 1 17 (by decide)
    exact hS.trans (runN_one s16 hs16h hpc16)
  let s17 := runN s 17
  have hs17pc : s17.pc = 1236 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]
  have hs17h : s17.halted = false := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16h
  have hs17Z : s17.mem.get 0 = 0 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16Z
  have hs17T : s17.mem.get 18 = 9 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hs16T
  have hI17 : s17.mem.get 29 = 15 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hI16
  have hCH17 : s17.mem.get 30 = s.mem.get 30 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hCH16
  have hONE17 : s17.mem.get 3 = 1 := by have : s17 = step s16 := hrun17; rw [this, hs17eq]; exact hONE16
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s17 = step s16 := hrun17
    rw [this, hs17eq]; exact hpres16 a ha18 ha0
  have g17 := sc_code_shrink (s := s) (s' := s17) (lo := 1236) (hi := 1239)
    hpres17 hcode (by decide) (by decide)
  have hdec7 := sc_dec_T_1236 (s := s17) hs17pc hs17h g17
  have hs18eq : step s17 =
      { s17 with mem := s17.mem.set 18 (s17.mem.get 18 - s17.mem.get 3), pc := 1239 } := hdec7
  have hrun18 : runN s 18 = step s17 := by
    have hS : runN s 18 = runN s17 1 := runN_add_eq s 17 1 18 (by decide)
    exact hS.trans (runN_one s17 hs17h (by simp [hs17pc]))
  let s18 := runN s 18
  have hs18pc : s18.pc = 1239 := by have : s18 = step s17 := hrun18; rw [this, hs18eq]
  have hs18h : s18.halted = false := by have : s18 = step s17 := hrun18; rw [this, hs18eq]; exact hs17h
  have hs18Z : s18.mem.get 0 = 0 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 0 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hs17Z
  have hs18T : s18.mem.get 18 = 8 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq, Mem.get_set_eq]
    have h1 : s17.mem.get 18 - s17.mem.get 3 = (9 : Word) - 1 := by
      rw [hs17T, hONE17]
    exact h1.trans (rfl : (9 : Word) - 1 = 8)
  have hI18 : s18.mem.get 29 = 15 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 29 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hI17
  have hCH18 : s18.mem.get 30 = s.mem.get 30 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 30 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hCH17
  have hONE18 : s18.mem.get 3 = 1 := by
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 3 (s17.mem.get 18 - s17.mem.get 3) (by decide)).trans hONE17
  have hpres18 : ∀ a, a ≠ 18 → a ≠ 0 → s18.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s18 = step s17 := hrun18
    rw [this, hs18eq]
    exact (Mem.get_set_ne s17.mem 18 a (s17.mem.get 18 - s17.mem.get 3) ha18).trans
      (hpres17 a ha18 ha0)
  have g18 := sc_code_shrink (s := s) (s' := s18) (lo := 1239) (hi := 1242)
    hpres18 hcode (by decide) (by decide)
  have henc7 := sc_enc_jlez_1239 (s := s18) hs18pc g18
  have hpc18 : s18.pc.toNat < 32768 := by simp [hs18pc]
  have hjlez7 :=
    step_JLEZ (s := s18) (x := 18) (dest := 1392)
      hs18h hpc18 hs18Z henc7.1 henc7.2.1 henc7.2.2 (by decide)
  have hle7 : (s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18) = false := by
    have : le0 (s18.mem.get 18) = false := by
      rw [hs18T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs19eq : step s18 = { s18 with pc := 1242 } := by
    have hif :
        (if s18.mem.get 18 = 0 || 0x8000 ≤ s18.mem.get 18
          then (1392 : Word) else s18.pc + 3) = (1242 : Word) := by
      have hfall : s18.pc + 3 = (1242 : Word) := by simp [hs18pc]
      simp [hle7, hfall]
    rw [hjlez7, hif]
  have hrun19 : runN s 19 = step s18 := by
    have hS : runN s 19 = runN s18 1 := runN_add_eq s 18 1 19 (by decide)
    exact hS.trans (runN_one s18 hs18h hpc18)
  let s19 := runN s 19
  have hs19pc : s19.pc = 1242 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]
  have hs19h : s19.halted = false := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18h
  have hs19Z : s19.mem.get 0 = 0 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18Z
  have hs19T : s19.mem.get 18 = 8 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hs18T
  have hI19 : s19.mem.get 29 = 15 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hI18
  have hCH19 : s19.mem.get 30 = s.mem.get 30 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hCH18
  have hONE19 : s19.mem.get 3 = 1 := by have : s19 = step s18 := hrun19; rw [this, hs19eq]; exact hONE18
  have hpres19 : ∀ a, a ≠ 18 → a ≠ 0 → s19.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s19 = step s18 := hrun19
    rw [this, hs19eq]; exact hpres18 a ha18 ha0
  have g19 := sc_code_shrink (s := s) (s' := s19) (lo := 1242) (hi := 1245)
    hpres19 hcode (by decide) (by decide)
  have hdec8 := sc_dec_T_1242 (s := s19) hs19pc hs19h g19
  have hs20eq : step s19 =
      { s19 with mem := s19.mem.set 18 (s19.mem.get 18 - s19.mem.get 3), pc := 1245 } := hdec8
  have hrun20 : runN s 20 = step s19 := by
    have hS : runN s 20 = runN s19 1 := runN_add_eq s 19 1 20 (by decide)
    exact hS.trans (runN_one s19 hs19h (by simp [hs19pc]))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1245 := by have : s20 = step s19 := hrun20; rw [this, hs20eq]
  have hs20h : s20.halted = false := by have : s20 = step s19 := hrun20; rw [this, hs20eq]; exact hs19h
  have hs20Z : s20.mem.get 0 = 0 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 0 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hs19Z
  have hs20T : s20.mem.get 18 = 7 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq, Mem.get_set_eq]
    have h1 : s19.mem.get 18 - s19.mem.get 3 = (8 : Word) - 1 := by
      rw [hs19T, hONE19]
    exact h1.trans (rfl : (8 : Word) - 1 = 7)
  have hI20 : s20.mem.get 29 = 15 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 29 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hI19
  have hCH20 : s20.mem.get 30 = s.mem.get 30 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 30 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hCH19
  have hONE20 : s20.mem.get 3 = 1 := by
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 3 (s19.mem.get 18 - s19.mem.get 3) (by decide)).trans hONE19
  have hpres20 : ∀ a, a ≠ 18 → a ≠ 0 → s20.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s20 = step s19 := hrun20
    rw [this, hs20eq]
    exact (Mem.get_set_ne s19.mem 18 a (s19.mem.get 18 - s19.mem.get 3) ha18).trans
      (hpres19 a ha18 ha0)
  have g20 := sc_code_shrink (s := s) (s' := s20) (lo := 1245) (hi := 1248)
    hpres20 hcode (by decide) (by decide)
  have henc8 := sc_enc_jlez_1245 (s := s20) hs20pc g20
  have hpc20 : s20.pc.toNat < 32768 := by simp [hs20pc]
  have hjlez8 :=
    step_JLEZ (s := s20) (x := 18) (dest := 1407)
      hs20h hpc20 hs20Z henc8.1 henc8.2.1 henc8.2.2 (by decide)
  have hle8 : (s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18) = false := by
    have : le0 (s20.mem.get 18) = false := by
      rw [hs20T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs21eq : step s20 = { s20 with pc := 1248 } := by
    have hif :
        (if s20.mem.get 18 = 0 || 0x8000 ≤ s20.mem.get 18
          then (1407 : Word) else s20.pc + 3) = (1248 : Word) := by
      have hfall : s20.pc + 3 = (1248 : Word) := by simp [hs20pc]
      simp [hle8, hfall]
    rw [hjlez8, hif]
  have hrun21 : runN s 21 = step s20 := by
    have hS : runN s 21 = runN s20 1 := runN_add_eq s 20 1 21 (by decide)
    exact hS.trans (runN_one s20 hs20h hpc20)
  let s21 := runN s 21
  have hs21pc : s21.pc = 1248 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]
  have hs21h : s21.halted = false := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20h
  have hs21Z : s21.mem.get 0 = 0 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20Z
  have hs21T : s21.mem.get 18 = 7 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hs20T
  have hI21 : s21.mem.get 29 = 15 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hI20
  have hCH21 : s21.mem.get 30 = s.mem.get 30 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hCH20
  have hONE21 : s21.mem.get 3 = 1 := by have : s21 = step s20 := hrun21; rw [this, hs21eq]; exact hONE20
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s21 = step s20 := hrun21
    rw [this, hs21eq]; exact hpres20 a ha18 ha0
  have g21 := sc_code_shrink (s := s) (s' := s21) (lo := 1248) (hi := 1251)
    hpres21 hcode (by decide) (by decide)
  have hdec9 := sc_dec_T_1248 (s := s21) hs21pc hs21h g21
  have hs22eq : step s21 =
      { s21 with mem := s21.mem.set 18 (s21.mem.get 18 - s21.mem.get 3), pc := 1251 } := hdec9
  have hrun22 : runN s 22 = step s21 := by
    have hS : runN s 22 = runN s21 1 := runN_add_eq s 21 1 22 (by decide)
    exact hS.trans (runN_one s21 hs21h (by simp [hs21pc]))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1251 := by have : s22 = step s21 := hrun22; rw [this, hs22eq]
  have hs22h : s22.halted = false := by have : s22 = step s21 := hrun22; rw [this, hs22eq]; exact hs21h
  have hs22Z : s22.mem.get 0 = 0 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 0 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hs21Z
  have hs22T : s22.mem.get 18 = 6 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq, Mem.get_set_eq]
    have h1 : s21.mem.get 18 - s21.mem.get 3 = (7 : Word) - 1 := by
      rw [hs21T, hONE21]
    exact h1.trans (rfl : (7 : Word) - 1 = 6)
  have hI22 : s22.mem.get 29 = 15 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 29 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hI21
  have hCH22 : s22.mem.get 30 = s.mem.get 30 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 30 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hCH21
  have hONE22 : s22.mem.get 3 = 1 := by
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 3 (s21.mem.get 18 - s21.mem.get 3) (by decide)).trans hONE21
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 0 → s22.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s22 = step s21 := hrun22
    rw [this, hs22eq]
    exact (Mem.get_set_ne s21.mem 18 a (s21.mem.get 18 - s21.mem.get 3) ha18).trans
      (hpres21 a ha18 ha0)
  have g22 := sc_code_shrink (s := s) (s' := s22) (lo := 1251) (hi := 1254)
    hpres22 hcode (by decide) (by decide)
  have henc9 := sc_enc_jlez_1251 (s := s22) hs22pc g22
  have hpc22 : s22.pc.toNat < 32768 := by simp [hs22pc]
  have hjlez9 :=
    step_JLEZ (s := s22) (x := 18) (dest := 1422)
      hs22h hpc22 hs22Z henc9.1 henc9.2.1 henc9.2.2 (by decide)
  have hle9 : (s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18) = false := by
    have : le0 (s22.mem.get 18) = false := by
      rw [hs22T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs23eq : step s22 = { s22 with pc := 1254 } := by
    have hif :
        (if s22.mem.get 18 = 0 || 0x8000 ≤ s22.mem.get 18
          then (1422 : Word) else s22.pc + 3) = (1254 : Word) := by
      have hfall : s22.pc + 3 = (1254 : Word) := by simp [hs22pc]
      simp [hle9, hfall]
    rw [hjlez9, hif]
  have hrun23 : runN s 23 = step s22 := by
    have hS : runN s 23 = runN s22 1 := runN_add_eq s 22 1 23 (by decide)
    exact hS.trans (runN_one s22 hs22h hpc22)
  let s23 := runN s 23
  have hs23pc : s23.pc = 1254 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]
  have hs23h : s23.halted = false := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22h
  have hs23Z : s23.mem.get 0 = 0 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22Z
  have hs23T : s23.mem.get 18 = 6 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hs22T
  have hI23 : s23.mem.get 29 = 15 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hI22
  have hCH23 : s23.mem.get 30 = s.mem.get 30 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hCH22
  have hONE23 : s23.mem.get 3 = 1 := by have : s23 = step s22 := hrun23; rw [this, hs23eq]; exact hONE22
  have hpres23 : ∀ a, a ≠ 18 → a ≠ 0 → s23.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s23 = step s22 := hrun23
    rw [this, hs23eq]; exact hpres22 a ha18 ha0
  have g23 := sc_code_shrink (s := s) (s' := s23) (lo := 1254) (hi := 1257)
    hpres23 hcode (by decide) (by decide)
  have hdec10 := sc_dec_T_1254 (s := s23) hs23pc hs23h g23
  have hs24eq : step s23 =
      { s23 with mem := s23.mem.set 18 (s23.mem.get 18 - s23.mem.get 3), pc := 1257 } := hdec10
  have hrun24 : runN s 24 = step s23 := by
    have hS : runN s 24 = runN s23 1 := runN_add_eq s 23 1 24 (by decide)
    exact hS.trans (runN_one s23 hs23h (by simp [hs23pc]))
  let s24 := runN s 24
  have hs24pc : s24.pc = 1257 := by have : s24 = step s23 := hrun24; rw [this, hs24eq]
  have hs24h : s24.halted = false := by have : s24 = step s23 := hrun24; rw [this, hs24eq]; exact hs23h
  have hs24Z : s24.mem.get 0 = 0 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 0 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hs23Z
  have hs24T : s24.mem.get 18 = 5 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq, Mem.get_set_eq]
    have h1 : s23.mem.get 18 - s23.mem.get 3 = (6 : Word) - 1 := by
      rw [hs23T, hONE23]
    exact h1.trans (rfl : (6 : Word) - 1 = 5)
  have hI24 : s24.mem.get 29 = 15 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 29 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hI23
  have hCH24 : s24.mem.get 30 = s.mem.get 30 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 30 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hCH23
  have hONE24 : s24.mem.get 3 = 1 := by
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 3 (s23.mem.get 18 - s23.mem.get 3) (by decide)).trans hONE23
  have hpres24 : ∀ a, a ≠ 18 → a ≠ 0 → s24.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s24 = step s23 := hrun24
    rw [this, hs24eq]
    exact (Mem.get_set_ne s23.mem 18 a (s23.mem.get 18 - s23.mem.get 3) ha18).trans
      (hpres23 a ha18 ha0)
  have g24 := sc_code_shrink (s := s) (s' := s24) (lo := 1257) (hi := 1260)
    hpres24 hcode (by decide) (by decide)
  have henc10 := sc_enc_jlez_1257 (s := s24) hs24pc g24
  have hpc24 : s24.pc.toNat < 32768 := by simp [hs24pc]
  have hjlez10 :=
    step_JLEZ (s := s24) (x := 18) (dest := 1437)
      hs24h hpc24 hs24Z henc10.1 henc10.2.1 henc10.2.2 (by decide)
  have hle10 : (s24.mem.get 18 = 0 || 0x8000 ≤ s24.mem.get 18) = false := by
    have : le0 (s24.mem.get 18) = false := by
      rw [hs24T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs25eq : step s24 = { s24 with pc := 1260 } := by
    have hif :
        (if s24.mem.get 18 = 0 || 0x8000 ≤ s24.mem.get 18
          then (1437 : Word) else s24.pc + 3) = (1260 : Word) := by
      have hfall : s24.pc + 3 = (1260 : Word) := by simp [hs24pc]
      simp [hle10, hfall]
    rw [hjlez10, hif]
  have hrun25 : runN s 25 = step s24 := by
    have hS : runN s 25 = runN s24 1 := runN_add_eq s 24 1 25 (by decide)
    exact hS.trans (runN_one s24 hs24h hpc24)
  let s25 := runN s 25
  have hs25pc : s25.pc = 1260 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]
  have hs25h : s25.halted = false := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24h
  have hs25Z : s25.mem.get 0 = 0 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24Z
  have hs25T : s25.mem.get 18 = 5 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hs24T
  have hI25 : s25.mem.get 29 = 15 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hI24
  have hCH25 : s25.mem.get 30 = s.mem.get 30 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hCH24
  have hONE25 : s25.mem.get 3 = 1 := by have : s25 = step s24 := hrun25; rw [this, hs25eq]; exact hONE24
  have hpres25 : ∀ a, a ≠ 18 → a ≠ 0 → s25.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s25 = step s24 := hrun25
    rw [this, hs25eq]; exact hpres24 a ha18 ha0
  have g25 := sc_code_shrink (s := s) (s' := s25) (lo := 1260) (hi := 1263)
    hpres25 hcode (by decide) (by decide)
  have hdec11 := sc_dec_T_1260 (s := s25) hs25pc hs25h g25
  have hs26eq : step s25 =
      { s25 with mem := s25.mem.set 18 (s25.mem.get 18 - s25.mem.get 3), pc := 1263 } := hdec11
  have hrun26 : runN s 26 = step s25 := by
    have hS : runN s 26 = runN s25 1 := runN_add_eq s 25 1 26 (by decide)
    exact hS.trans (runN_one s25 hs25h (by simp [hs25pc]))
  let s26 := runN s 26
  have hs26pc : s26.pc = 1263 := by have : s26 = step s25 := hrun26; rw [this, hs26eq]
  have hs26h : s26.halted = false := by have : s26 = step s25 := hrun26; rw [this, hs26eq]; exact hs25h
  have hs26Z : s26.mem.get 0 = 0 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 0 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hs25Z
  have hs26T : s26.mem.get 18 = 4 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq, Mem.get_set_eq]
    have h1 : s25.mem.get 18 - s25.mem.get 3 = (5 : Word) - 1 := by
      rw [hs25T, hONE25]
    exact h1.trans (rfl : (5 : Word) - 1 = 4)
  have hI26 : s26.mem.get 29 = 15 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 29 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hI25
  have hCH26 : s26.mem.get 30 = s.mem.get 30 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 30 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hCH25
  have hONE26 : s26.mem.get 3 = 1 := by
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 3 (s25.mem.get 18 - s25.mem.get 3) (by decide)).trans hONE25
  have hpres26 : ∀ a, a ≠ 18 → a ≠ 0 → s26.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s26 = step s25 := hrun26
    rw [this, hs26eq]
    exact (Mem.get_set_ne s25.mem 18 a (s25.mem.get 18 - s25.mem.get 3) ha18).trans
      (hpres25 a ha18 ha0)
  have g26 := sc_code_shrink (s := s) (s' := s26) (lo := 1263) (hi := 1266)
    hpres26 hcode (by decide) (by decide)
  have henc11 := sc_enc_jlez_1263 (s := s26) hs26pc g26
  have hpc26 : s26.pc.toNat < 32768 := by simp [hs26pc]
  have hjlez11 :=
    step_JLEZ (s := s26) (x := 18) (dest := 1452)
      hs26h hpc26 hs26Z henc11.1 henc11.2.1 henc11.2.2 (by decide)
  have hle11 : (s26.mem.get 18 = 0 || 0x8000 ≤ s26.mem.get 18) = false := by
    have : le0 (s26.mem.get 18) = false := by
      rw [hs26T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs27eq : step s26 = { s26 with pc := 1266 } := by
    have hif :
        (if s26.mem.get 18 = 0 || 0x8000 ≤ s26.mem.get 18
          then (1452 : Word) else s26.pc + 3) = (1266 : Word) := by
      have hfall : s26.pc + 3 = (1266 : Word) := by simp [hs26pc]
      simp [hle11, hfall]
    rw [hjlez11, hif]
  have hrun27 : runN s 27 = step s26 := by
    have hS : runN s 27 = runN s26 1 := runN_add_eq s 26 1 27 (by decide)
    exact hS.trans (runN_one s26 hs26h hpc26)
  let s27 := runN s 27
  have hs27pc : s27.pc = 1266 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]
  have hs27h : s27.halted = false := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26h
  have hs27Z : s27.mem.get 0 = 0 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26Z
  have hs27T : s27.mem.get 18 = 4 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hs26T
  have hI27 : s27.mem.get 29 = 15 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hI26
  have hCH27 : s27.mem.get 30 = s.mem.get 30 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hCH26
  have hONE27 : s27.mem.get 3 = 1 := by have : s27 = step s26 := hrun27; rw [this, hs27eq]; exact hONE26
  have hpres27 : ∀ a, a ≠ 18 → a ≠ 0 → s27.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s27 = step s26 := hrun27
    rw [this, hs27eq]; exact hpres26 a ha18 ha0
  have g27 := sc_code_shrink (s := s) (s' := s27) (lo := 1266) (hi := 1269)
    hpres27 hcode (by decide) (by decide)
  have hdec12 := sc_dec_T_1266 (s := s27) hs27pc hs27h g27
  have hs28eq : step s27 =
      { s27 with mem := s27.mem.set 18 (s27.mem.get 18 - s27.mem.get 3), pc := 1269 } := hdec12
  have hrun28 : runN s 28 = step s27 := by
    have hS : runN s 28 = runN s27 1 := runN_add_eq s 27 1 28 (by decide)
    exact hS.trans (runN_one s27 hs27h (by simp [hs27pc]))
  let s28 := runN s 28
  have hs28pc : s28.pc = 1269 := by have : s28 = step s27 := hrun28; rw [this, hs28eq]
  have hs28h : s28.halted = false := by have : s28 = step s27 := hrun28; rw [this, hs28eq]; exact hs27h
  have hs28Z : s28.mem.get 0 = 0 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 0 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hs27Z
  have hs28T : s28.mem.get 18 = 3 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq, Mem.get_set_eq]
    have h1 : s27.mem.get 18 - s27.mem.get 3 = (4 : Word) - 1 := by
      rw [hs27T, hONE27]
    exact h1.trans (rfl : (4 : Word) - 1 = 3)
  have hI28 : s28.mem.get 29 = 15 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 29 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hI27
  have hCH28 : s28.mem.get 30 = s.mem.get 30 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 30 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hCH27
  have hONE28 : s28.mem.get 3 = 1 := by
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 3 (s27.mem.get 18 - s27.mem.get 3) (by decide)).trans hONE27
  have hpres28 : ∀ a, a ≠ 18 → a ≠ 0 → s28.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s28 = step s27 := hrun28
    rw [this, hs28eq]
    exact (Mem.get_set_ne s27.mem 18 a (s27.mem.get 18 - s27.mem.get 3) ha18).trans
      (hpres27 a ha18 ha0)
  have g28 := sc_code_shrink (s := s) (s' := s28) (lo := 1269) (hi := 1272)
    hpres28 hcode (by decide) (by decide)
  have henc12 := sc_enc_jlez_1269 (s := s28) hs28pc g28
  have hpc28 : s28.pc.toNat < 32768 := by simp [hs28pc]
  have hjlez12 :=
    step_JLEZ (s := s28) (x := 18) (dest := 1467)
      hs28h hpc28 hs28Z henc12.1 henc12.2.1 henc12.2.2 (by decide)
  have hle12 : (s28.mem.get 18 = 0 || 0x8000 ≤ s28.mem.get 18) = false := by
    have : le0 (s28.mem.get 18) = false := by
      rw [hs28T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs29eq : step s28 = { s28 with pc := 1272 } := by
    have hif :
        (if s28.mem.get 18 = 0 || 0x8000 ≤ s28.mem.get 18
          then (1467 : Word) else s28.pc + 3) = (1272 : Word) := by
      have hfall : s28.pc + 3 = (1272 : Word) := by simp [hs28pc]
      simp [hle12, hfall]
    rw [hjlez12, hif]
  have hrun29 : runN s 29 = step s28 := by
    have hS : runN s 29 = runN s28 1 := runN_add_eq s 28 1 29 (by decide)
    exact hS.trans (runN_one s28 hs28h hpc28)
  let s29 := runN s 29
  have hs29pc : s29.pc = 1272 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]
  have hs29h : s29.halted = false := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hs28h
  have hs29Z : s29.mem.get 0 = 0 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hs28Z
  have hs29T : s29.mem.get 18 = 3 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hs28T
  have hI29 : s29.mem.get 29 = 15 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hI28
  have hCH29 : s29.mem.get 30 = s.mem.get 30 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hCH28
  have hONE29 : s29.mem.get 3 = 1 := by have : s29 = step s28 := hrun29; rw [this, hs29eq]; exact hONE28
  have hpres29 : ∀ a, a ≠ 18 → a ≠ 0 → s29.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s29 = step s28 := hrun29
    rw [this, hs29eq]; exact hpres28 a ha18 ha0
  have g29 := sc_code_shrink (s := s) (s' := s29) (lo := 1272) (hi := 1275)
    hpres29 hcode (by decide) (by decide)
  have hdec13 := sc_dec_T_1272 (s := s29) hs29pc hs29h g29
  have hs30eq : step s29 =
      { s29 with mem := s29.mem.set 18 (s29.mem.get 18 - s29.mem.get 3), pc := 1275 } := hdec13
  have hrun30 : runN s 30 = step s29 := by
    have hS : runN s 30 = runN s29 1 := runN_add_eq s 29 1 30 (by decide)
    exact hS.trans (runN_one s29 hs29h (by simp [hs29pc]))
  let s30 := runN s 30
  have hs30pc : s30.pc = 1275 := by have : s30 = step s29 := hrun30; rw [this, hs30eq]
  have hs30h : s30.halted = false := by have : s30 = step s29 := hrun30; rw [this, hs30eq]; exact hs29h
  have hs30Z : s30.mem.get 0 = 0 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 0 (s29.mem.get 18 - s29.mem.get 3) (by decide)).trans hs29Z
  have hs30T : s30.mem.get 18 = 2 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq, Mem.get_set_eq]
    have h1 : s29.mem.get 18 - s29.mem.get 3 = (3 : Word) - 1 := by
      rw [hs29T, hONE29]
    exact h1.trans (rfl : (3 : Word) - 1 = 2)
  have hI30 : s30.mem.get 29 = 15 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 29 (s29.mem.get 18 - s29.mem.get 3) (by decide)).trans hI29
  have hCH30 : s30.mem.get 30 = s.mem.get 30 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 30 (s29.mem.get 18 - s29.mem.get 3) (by decide)).trans hCH29
  have hONE30 : s30.mem.get 3 = 1 := by
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 3 (s29.mem.get 18 - s29.mem.get 3) (by decide)).trans hONE29
  have hpres30 : ∀ a, a ≠ 18 → a ≠ 0 → s30.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s30 = step s29 := hrun30
    rw [this, hs30eq]
    exact (Mem.get_set_ne s29.mem 18 a (s29.mem.get 18 - s29.mem.get 3) ha18).trans
      (hpres29 a ha18 ha0)
  have g30 := sc_code_shrink (s := s) (s' := s30) (lo := 1275) (hi := 1278)
    hpres30 hcode (by decide) (by decide)
  have henc13 := sc_enc_jlez_1275 (s := s30) hs30pc g30
  have hpc30 : s30.pc.toNat < 32768 := by simp [hs30pc]
  have hjlez13 :=
    step_JLEZ (s := s30) (x := 18) (dest := 1482)
      hs30h hpc30 hs30Z henc13.1 henc13.2.1 henc13.2.2 (by decide)
  have hle13 : (s30.mem.get 18 = 0 || 0x8000 ≤ s30.mem.get 18) = false := by
    have : le0 (s30.mem.get 18) = false := by
      rw [hs30T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs31eq : step s30 = { s30 with pc := 1278 } := by
    have hif :
        (if s30.mem.get 18 = 0 || 0x8000 ≤ s30.mem.get 18
          then (1482 : Word) else s30.pc + 3) = (1278 : Word) := by
      have hfall : s30.pc + 3 = (1278 : Word) := by simp [hs30pc]
      simp [hle13, hfall]
    rw [hjlez13, hif]
  have hrun31 : runN s 31 = step s30 := by
    have hS : runN s 31 = runN s30 1 := runN_add_eq s 30 1 31 (by decide)
    exact hS.trans (runN_one s30 hs30h hpc30)
  let s31 := runN s 31
  have hs31pc : s31.pc = 1278 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]
  have hs31h : s31.halted = false := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hs30h
  have hs31Z : s31.mem.get 0 = 0 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hs30Z
  have hs31T : s31.mem.get 18 = 2 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hs30T
  have hI31 : s31.mem.get 29 = 15 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hI30
  have hCH31 : s31.mem.get 30 = s.mem.get 30 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hCH30
  have hONE31 : s31.mem.get 3 = 1 := by have : s31 = step s30 := hrun31; rw [this, hs31eq]; exact hONE30
  have hpres31 : ∀ a, a ≠ 18 → a ≠ 0 → s31.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s31 = step s30 := hrun31
    rw [this, hs31eq]; exact hpres30 a ha18 ha0
  have g31 := sc_code_shrink (s := s) (s' := s31) (lo := 1278) (hi := 1281)
    hpres31 hcode (by decide) (by decide)
  have hdec14 := sc_dec_T_1278 (s := s31) hs31pc hs31h g31
  have hs32eq : step s31 =
      { s31 with mem := s31.mem.set 18 (s31.mem.get 18 - s31.mem.get 3), pc := 1281 } := hdec14
  have hrun32 : runN s 32 = step s31 := by
    have hS : runN s 32 = runN s31 1 := runN_add_eq s 31 1 32 (by decide)
    exact hS.trans (runN_one s31 hs31h (by simp [hs31pc]))
  let s32 := runN s 32
  have hs32pc : s32.pc = 1281 := by have : s32 = step s31 := hrun32; rw [this, hs32eq]
  have hs32h : s32.halted = false := by have : s32 = step s31 := hrun32; rw [this, hs32eq]; exact hs31h
  have hs32Z : s32.mem.get 0 = 0 := by
    have : s32 = step s31 := hrun32
    rw [this, hs32eq]
    exact (Mem.get_set_ne s31.mem 18 0 (s31.mem.get 18 - s31.mem.get 3) (by decide)).trans hs31Z
  have hs32T : s32.mem.get 18 = 1 := by
    have : s32 = step s31 := hrun32
    rw [this, hs32eq, Mem.get_set_eq]
    have h1 : s31.mem.get 18 - s31.mem.get 3 = (2 : Word) - 1 := by
      rw [hs31T, hONE31]
    exact h1.trans (rfl : (2 : Word) - 1 = 1)
  have hI32 : s32.mem.get 29 = 15 := by
    have : s32 = step s31 := hrun32
    rw [this, hs32eq]
    exact (Mem.get_set_ne s31.mem 18 29 (s31.mem.get 18 - s31.mem.get 3) (by decide)).trans hI31
  have hCH32 : s32.mem.get 30 = s.mem.get 30 := by
    have : s32 = step s31 := hrun32
    rw [this, hs32eq]
    exact (Mem.get_set_ne s31.mem 18 30 (s31.mem.get 18 - s31.mem.get 3) (by decide)).trans hCH31
  have hONE32 : s32.mem.get 3 = 1 := by
    have : s32 = step s31 := hrun32
    rw [this, hs32eq]
    exact (Mem.get_set_ne s31.mem 18 3 (s31.mem.get 18 - s31.mem.get 3) (by decide)).trans hONE31
  have hpres32 : ∀ a, a ≠ 18 → a ≠ 0 → s32.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s32 = step s31 := hrun32
    rw [this, hs32eq]
    exact (Mem.get_set_ne s31.mem 18 a (s31.mem.get 18 - s31.mem.get 3) ha18).trans
      (hpres31 a ha18 ha0)
  have g32 := sc_code_shrink (s := s) (s' := s32) (lo := 1281) (hi := 1284)
    hpres32 hcode (by decide) (by decide)
  have henc14 := sc_enc_jlez_1281 (s := s32) hs32pc g32
  have hpc32 : s32.pc.toNat < 32768 := by simp [hs32pc]
  have hjlez14 :=
    step_JLEZ (s := s32) (x := 18) (dest := 1497)
      hs32h hpc32 hs32Z henc14.1 henc14.2.1 henc14.2.2 (by decide)
  have hle14 : (s32.mem.get 18 = 0 || 0x8000 ≤ s32.mem.get 18) = false := by
    have : le0 (s32.mem.get 18) = false := by
      rw [hs32T]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs33eq : step s32 = { s32 with pc := 1284 } := by
    have hif :
        (if s32.mem.get 18 = 0 || 0x8000 ≤ s32.mem.get 18
          then (1497 : Word) else s32.pc + 3) = (1284 : Word) := by
      have hfall : s32.pc + 3 = (1284 : Word) := by simp [hs32pc]
      simp [hle14, hfall]
    rw [hjlez14, hif]
  have hrun33 : runN s 33 = step s32 := by
    have hS : runN s 33 = runN s32 1 := runN_add_eq s 32 1 33 (by decide)
    exact hS.trans (runN_one s32 hs32h hpc32)
  let s33 := runN s 33
  have hs33pc : s33.pc = 1284 := by have : s33 = step s32 := hrun33; rw [this, hs33eq]
  have hs33h : s33.halted = false := by have : s33 = step s32 := hrun33; rw [this, hs33eq]; exact hs32h
  have hs33Z : s33.mem.get 0 = 0 := by have : s33 = step s32 := hrun33; rw [this, hs33eq]; exact hs32Z
  have hs33T : s33.mem.get 18 = 1 := by have : s33 = step s32 := hrun33; rw [this, hs33eq]; exact hs32T
  have hI33 : s33.mem.get 29 = 15 := by have : s33 = step s32 := hrun33; rw [this, hs33eq]; exact hI32
  have hCH33 : s33.mem.get 30 = s.mem.get 30 := by have : s33 = step s32 := hrun33; rw [this, hs33eq]; exact hCH32
  have hONE33 : s33.mem.get 3 = 1 := by have : s33 = step s32 := hrun33; rw [this, hs33eq]; exact hONE32
  have hpres33 : ∀ a, a ≠ 18 → a ≠ 0 → s33.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s33 = step s32 := hrun33
    rw [this, hs33eq]; exact hpres32 a ha18 ha0
  have g33 := sc_code_shrink (s := s) (s' := s33) (lo := 1284) (hi := 1287)
    hpres33 hcode (by decide) (by decide)
  have hencJ := sc_enc_jmp_1284 (s := s33) hs33pc g33
  have hpc33 : s33.pc.toNat < 32768 := by simp [hs33pc]
  have hjmp15 := step_JMP (s := s33) (dest := 1512)
    hs33h hpc33 hs33Z hencJ.1 hencJ.2.1 hencJ.2.2
  have hrun34 : runN s 34 = step s33 := by
    have hS : runN s 34 = runN s33 1 := runN_add_eq s 33 1 34 (by decide)
    exact hS.trans (runN_one s33 hs33h hpc33)
  let s34 := runN s 34
  have hs34pc : s34.pc = 1512 := by have : s34 = step s33 := hrun34; rw [this, hjmp15]
  have hs34h : s34.halted = false := by have : s34 = step s33 := hrun34; rw [this, hjmp15]; exact hs33h
  have hs34Z : s34.mem.get 0 = 0 := by have : s34 = step s33 := hrun34; rw [this, hjmp15]; exact hs33Z
  have hI34 : s34.mem.get 29 = 15 := by have : s34 = step s33 := hrun34; rw [this, hjmp15]; exact hI33
  have hCH34 : s34.mem.get 30 = s.mem.get 30 := by have : s34 = step s33 := hrun34; rw [this, hjmp15]; exact hCH33
  have hpres34 : ∀ a, a ≠ 18 → a ≠ 0 → s34.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have : s34 = step s33 := hrun34
    rw [this, hjmp15]; exact hpres33 a ha18 ha0
  have g34 := sc_code_shrink (s := s) (s' := s34) (lo := 1512) (hi := 1527)
    hpres34 hcode (by decide) (by decide)
  have hs := st15_store (s := s34) hs34pc hs34h hs34Z g34
  have hrun : sN = runN s34 5 := runN_add_eq s 34 5 39 (by decide)
  have hsNpc : sN.pc = 1527 := by rw [hrun]; exact hs.1
  have hsNh : sN.halted = false := by rw [hrun]; exact hs.2.1
  have hsNZ : sN.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hsNB : sN.mem.get 47 = s.mem.get 30 := by
    rw [hrun]; exact hs.2.2.2.1.trans hCH34
  have hsNI : sN.mem.get 29 = 15 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hI34
  have hpres : ∀ a, a ≠ 47 → a ≠ 18 → a ≠ 0 → sN.mem.get a = s.mem.get a := by
    intro a haD ha18 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a haD ha0).trans (hpres34 a ha18 ha0)
  exact ⟨hsNpc, hsNh, hsNZ, hsNB, hsNI, hpres⟩

end IntFmt
