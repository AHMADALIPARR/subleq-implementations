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

end IntFmt
