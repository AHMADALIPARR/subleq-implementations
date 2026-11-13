/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Parametric place-value loop (the P0/P1/P2/P3 81-cell diamond).
Block lemmas, not end-to-end correctness.
-/

import IntFmt.PlaceCore
import IntFmt.DecChunksA

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

private theorem cell256 (off : Nat) (h : off < 16) :
    intfmtImage[256 + off]! = decChunk016[off]! :=
  extract_chunk 256 decChunk016 image_chunk016 off h (by decide)


private theorem cell272 (off : Nat) (h : off < 16) :
    intfmtImage[272 + off]! = decChunk017[off]! :=
  extract_chunk 272 decChunk017 image_chunk017 off h (by decide)


private theorem cell288 (off : Nat) (h : off < 16) :
    intfmtImage[288 + off]! = decChunk018[off]! :=
  extract_chunk 288 decChunk018 image_chunk018 off h (by decide)


private theorem cell304 (off : Nat) (h : off < 16) :
    intfmtImage[304 + off]! = decChunk019[off]! :=
  extract_chunk 304 decChunk019 image_chunk019 off h (by decide)


private theorem cell320 (off : Nat) (h : off < 16) :
    intfmtImage[320 + off]! = decChunk020[off]! :=
  extract_chunk 320 decChunk020 image_chunk020 off h (by decide)


private theorem cell336 (off : Nat) (h : off < 16) :
    intfmtImage[336 + off]! = decChunk021[off]! :=
  extract_chunk 336 decChunk021 image_chunk021 off h (by decide)


private theorem cell352 (off : Nat) (h : off < 16) :
    intfmtImage[352 + off]! = decChunk022[off]! :=
  extract_chunk 352 decChunk022 image_chunk022 off h (by decide)


private theorem cell368 (off : Nat) (h : off < 16) :
    intfmtImage[368 + off]! = decChunk023[off]! :=
  extract_chunk 368 decChunk023 image_chunk023 off h (by decide)


private theorem cell384 (off : Nat) (h : off < 16) :
    intfmtImage[384 + off]! = decChunk024[off]! :=
  extract_chunk 384 decChunk024 image_chunk024 off h (by decide)


private theorem cell400 (off : Nat) (h : off < 16) :
    intfmtImage[400 + off]! = decChunk025[off]! :=
  extract_chunk 400 decChunk025 image_chunk025 off h (by decide)


private theorem cell416 (off : Nat) (h : off < 16) :
    intfmtImage[416 + off]! = decChunk026[off]! :=
  extract_chunk 416 decChunk026 image_chunk026 off h (by decide)


private theorem cell432 (off : Nat) (h : off < 16) :
    intfmtImage[432 + off]! = decChunk027[off]! :=
  extract_chunk 432 decChunk027 image_chunk027 off h (by decide)


private theorem cell448 (off : Nat) (h : off < 16) :
    intfmtImage[448 + off]! = decChunk028[off]! :=
  extract_chunk 448 decChunk028 image_chunk028 off h (by decide)


private theorem cell464 (off : Nat) (h : off < 16) :
    intfmtImage[464 + off]! = decChunk029[off]! :=
  extract_chunk 464 decChunk029 image_chunk029 off h (by decide)


private theorem cell480 (off : Nat) (h : off < 16) :
    intfmtImage[480 + off]! = decChunk030[off]! :=
  extract_chunk 480 decChunk030 image_chunk030 off h (by decide)


private theorem cell496 (off : Nat) (h : off < 16) :
    intfmtImage[496 + off]! = decChunk031[off]! :=
  extract_chunk 496 decChunk031 image_chunk031 off h (by decide)


private theorem cell512 (off : Nat) (h : off < 16) :
    intfmtImage[512 + off]! = decChunk032[off]! :=
  extract_chunk 512 decChunk032 image_chunk032 off h (by decide)

/-- The assembled image matches `placeTemplate` at the `p1` loop. -/
theorem p1_image (off : Nat) (h : off < 81) :
    intfmtImage[270 + off]! = UInt16.ofNat (placeTemplate 270 6 21 off) := by
  match off with
  | 0 =>
    have hval : decChunk016[14]! = 18 := rfl
    have ht : placeTemplate 270 6 21 0 = 18 := rfl
    have himg : intfmtImage[270]! = decChunk016[14]! :=
      cell256 14 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 1 =>
    have hval : decChunk016[15]! = 18 := rfl
    have ht : placeTemplate 270 6 21 1 = 18 := rfl
    have himg : intfmtImage[271]! = decChunk016[15]! :=
      cell256 15 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 2 =>
    have hval : decChunk017[0]! = 273 := rfl
    have ht : placeTemplate 270 6 21 2 = 273 := rfl
    have himg : intfmtImage[272]! = decChunk017[0]! :=
      cell272 0 (by decide)
    have hnat : (273 : Word) = UInt16.ofNat 273 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 3 =>
    have hval : decChunk017[1]! = 17 := rfl
    have ht : placeTemplate 270 6 21 3 = 17 := rfl
    have himg : intfmtImage[273]! = decChunk017[1]! :=
      cell272 1 (by decide)
    have hnat : (17 : Word) = UInt16.ofNat 17 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 4 =>
    have hval : decChunk017[2]! = 0 := rfl
    have ht : placeTemplate 270 6 21 4 = 0 := rfl
    have himg : intfmtImage[274]! = decChunk017[2]! :=
      cell272 2 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 5 =>
    have hval : decChunk017[3]! = 276 := rfl
    have ht : placeTemplate 270 6 21 5 = 276 := rfl
    have himg : intfmtImage[275]! = decChunk017[3]! :=
      cell272 3 (by decide)
    have hnat : (276 : Word) = UInt16.ofNat 276 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 6 =>
    have hval : decChunk017[4]! = 0 := rfl
    have ht : placeTemplate 270 6 21 6 = 0 := rfl
    have himg : intfmtImage[276]! = decChunk017[4]! :=
      cell272 4 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 7 =>
    have hval : decChunk017[5]! = 18 := rfl
    have ht : placeTemplate 270 6 21 7 = 18 := rfl
    have himg : intfmtImage[277]! = decChunk017[5]! :=
      cell272 5 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 8 =>
    have hval : decChunk017[6]! = 279 := rfl
    have ht : placeTemplate 270 6 21 8 = 279 := rfl
    have himg : intfmtImage[278]! = decChunk017[6]! :=
      cell272 6 (by decide)
    have hnat : (279 : Word) = UInt16.ofNat 279 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 9 =>
    have hval : decChunk017[7]! = 0 := rfl
    have ht : placeTemplate 270 6 21 9 = 0 := rfl
    have himg : intfmtImage[279]! = decChunk017[7]! :=
      cell272 7 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 10 =>
    have hval : decChunk017[8]! = 0 := rfl
    have ht : placeTemplate 270 6 21 10 = 0 := rfl
    have himg : intfmtImage[280]! = decChunk017[8]! :=
      cell272 8 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 11 =>
    have hval : decChunk017[9]! = 282 := rfl
    have ht : placeTemplate 270 6 21 11 = 282 := rfl
    have himg : intfmtImage[281]! = decChunk017[9]! :=
      cell272 9 (by decide)
    have hnat : (282 : Word) = UInt16.ofNat 282 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 12 =>
    have hval : decChunk017[10]! = 0 := rfl
    have ht : placeTemplate 270 6 21 12 = 0 := rfl
    have himg : intfmtImage[282]! = decChunk017[10]! :=
      cell272 10 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 13 =>
    have hval : decChunk017[11]! = 18 := rfl
    have ht : placeTemplate 270 6 21 13 = 18 := rfl
    have himg : intfmtImage[283]! = decChunk017[11]! :=
      cell272 11 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 14 =>
    have hval : decChunk017[12]! = 288 := rfl
    have ht : placeTemplate 270 6 21 14 = 288 := rfl
    have himg : intfmtImage[284]! = decChunk017[12]! :=
      cell272 12 (by decide)
    have hnat : (288 : Word) = UInt16.ofNat 288 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 15 =>
    have hval : decChunk017[13]! = 0 := rfl
    have ht : placeTemplate 270 6 21 15 = 0 := rfl
    have himg : intfmtImage[285]! = decChunk017[13]! :=
      cell272 13 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 16 =>
    have hval : decChunk017[14]! = 0 := rfl
    have ht : placeTemplate 270 6 21 16 = 0 := rfl
    have himg : intfmtImage[286]! = decChunk017[14]! :=
      cell272 14 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 17 =>
    have hval : decChunk017[15]! = 303 := rfl
    have ht : placeTemplate 270 6 21 17 = 303 := rfl
    have himg : intfmtImage[287]! = decChunk017[15]! :=
      cell272 15 (by decide)
    have hnat : (303 : Word) = UInt16.ofNat 303 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 18 =>
    have hval : decChunk018[0]! = 3 := rfl
    have ht : placeTemplate 270 6 21 18 = 3 := rfl
    have himg : intfmtImage[288]! = decChunk018[0]! :=
      cell288 0 (by decide)
    have hnat : (3 : Word) = UInt16.ofNat 3 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 19 =>
    have hval : decChunk018[1]! = 0 := rfl
    have ht : placeTemplate 270 6 21 19 = 0 := rfl
    have himg : intfmtImage[289]! = decChunk018[1]! :=
      cell288 1 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 20 =>
    have hval : decChunk018[2]! = 291 := rfl
    have ht : placeTemplate 270 6 21 20 = 291 := rfl
    have himg : intfmtImage[290]! = decChunk018[2]! :=
      cell288 2 (by decide)
    have hnat : (291 : Word) = UInt16.ofNat 291 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 21 =>
    have hval : decChunk018[3]! = 0 := rfl
    have ht : placeTemplate 270 6 21 21 = 0 := rfl
    have himg : intfmtImage[291]! = decChunk018[3]! :=
      cell288 3 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 22 =>
    have hval : decChunk018[4]! = 18 := rfl
    have ht : placeTemplate 270 6 21 22 = 18 := rfl
    have himg : intfmtImage[292]! = decChunk018[4]! :=
      cell288 4 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 23 =>
    have hval : decChunk018[5]! = 294 := rfl
    have ht : placeTemplate 270 6 21 23 = 294 := rfl
    have himg : intfmtImage[293]! = decChunk018[5]! :=
      cell288 5 (by decide)
    have hnat : (294 : Word) = UInt16.ofNat 294 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 24 =>
    have hval : decChunk018[6]! = 0 := rfl
    have ht : placeTemplate 270 6 21 24 = 0 := rfl
    have himg : intfmtImage[294]! = decChunk018[6]! :=
      cell288 6 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 25 =>
    have hval : decChunk018[7]! = 0 := rfl
    have ht : placeTemplate 270 6 21 25 = 0 := rfl
    have himg : intfmtImage[295]! = decChunk018[7]! :=
      cell288 7 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 26 =>
    have hval : decChunk018[8]! = 297 := rfl
    have ht : placeTemplate 270 6 21 26 = 297 := rfl
    have himg : intfmtImage[296]! = decChunk018[8]! :=
      cell288 8 (by decide)
    have hnat : (297 : Word) = UInt16.ofNat 297 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 27 =>
    have hval : decChunk018[9]! = 0 := rfl
    have ht : placeTemplate 270 6 21 27 = 0 := rfl
    have himg : intfmtImage[297]! = decChunk018[9]! :=
      cell288 9 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 28 =>
    have hval : decChunk018[10]! = 18 := rfl
    have ht : placeTemplate 270 6 21 28 = 18 := rfl
    have himg : intfmtImage[298]! = decChunk018[10]! :=
      cell288 10 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 29 =>
    have hval : decChunk018[11]! = 336 := rfl
    have ht : placeTemplate 270 6 21 29 = 336 := rfl
    have himg : intfmtImage[299]! = decChunk018[11]! :=
      cell288 11 (by decide)
    have hnat : (336 : Word) = UInt16.ofNat 336 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 30 =>
    have hval : decChunk018[12]! = 0 := rfl
    have ht : placeTemplate 270 6 21 30 = 0 := rfl
    have himg : intfmtImage[300]! = decChunk018[12]! :=
      cell288 12 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 31 =>
    have hval : decChunk018[13]! = 0 := rfl
    have ht : placeTemplate 270 6 21 31 = 0 := rfl
    have himg : intfmtImage[301]! = decChunk018[13]! :=
      cell288 13 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 32 =>
    have hval : decChunk018[14]! = 351 := rfl
    have ht : placeTemplate 270 6 21 32 = 351 := rfl
    have himg : intfmtImage[302]! = decChunk018[14]! :=
      cell288 14 (by decide)
    have hnat : (351 : Word) = UInt16.ofNat 351 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 33 =>
    have hval : decChunk018[15]! = 18 := rfl
    have ht : placeTemplate 270 6 21 33 = 18 := rfl
    have himg : intfmtImage[303]! = decChunk018[15]! :=
      cell288 15 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 34 =>
    have hval : decChunk019[0]! = 18 := rfl
    have ht : placeTemplate 270 6 21 34 = 18 := rfl
    have himg : intfmtImage[304]! = decChunk019[0]! :=
      cell304 0 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 35 =>
    have hval : decChunk019[1]! = 306 := rfl
    have ht : placeTemplate 270 6 21 35 = 306 := rfl
    have himg : intfmtImage[305]! = decChunk019[1]! :=
      cell304 1 (by decide)
    have hnat : (306 : Word) = UInt16.ofNat 306 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 36 =>
    have hval : decChunk019[2]! = 17 := rfl
    have ht : placeTemplate 270 6 21 36 = 17 := rfl
    have himg : intfmtImage[306]! = decChunk019[2]! :=
      cell304 2 (by decide)
    have hnat : (17 : Word) = UInt16.ofNat 17 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 37 =>
    have hval : decChunk019[3]! = 0 := rfl
    have ht : placeTemplate 270 6 21 37 = 0 := rfl
    have himg : intfmtImage[307]! = decChunk019[3]! :=
      cell304 3 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 38 =>
    have hval : decChunk019[4]! = 309 := rfl
    have ht : placeTemplate 270 6 21 38 = 309 := rfl
    have himg : intfmtImage[308]! = decChunk019[4]! :=
      cell304 4 (by decide)
    have hnat : (309 : Word) = UInt16.ofNat 309 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 39 =>
    have hval : decChunk019[5]! = 0 := rfl
    have ht : placeTemplate 270 6 21 39 = 0 := rfl
    have himg : intfmtImage[309]! = decChunk019[5]! :=
      cell304 5 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 40 =>
    have hval : decChunk019[6]! = 18 := rfl
    have ht : placeTemplate 270 6 21 40 = 18 := rfl
    have himg : intfmtImage[310]! = decChunk019[6]! :=
      cell304 6 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 41 =>
    have hval : decChunk019[7]! = 312 := rfl
    have ht : placeTemplate 270 6 21 41 = 312 := rfl
    have himg : intfmtImage[311]! = decChunk019[7]! :=
      cell304 7 (by decide)
    have hnat : (312 : Word) = UInt16.ofNat 312 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 42 =>
    have hval : decChunk019[8]! = 0 := rfl
    have ht : placeTemplate 270 6 21 42 = 0 := rfl
    have himg : intfmtImage[312]! = decChunk019[8]! :=
      cell304 8 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 43 =>
    have hval : decChunk019[9]! = 0 := rfl
    have ht : placeTemplate 270 6 21 43 = 0 := rfl
    have himg : intfmtImage[313]! = decChunk019[9]! :=
      cell304 9 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 44 =>
    have hval : decChunk019[10]! = 315 := rfl
    have ht : placeTemplate 270 6 21 44 = 315 := rfl
    have himg : intfmtImage[314]! = decChunk019[10]! :=
      cell304 10 (by decide)
    have hnat : (315 : Word) = UInt16.ofNat 315 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 45 =>
    have hval : decChunk019[11]! = 6 := rfl
    have ht : placeTemplate 270 6 21 45 = 6 := rfl
    have himg : intfmtImage[315]! = decChunk019[11]! :=
      cell304 11 (by decide)
    have hnat : (6 : Word) = UInt16.ofNat 6 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 46 =>
    have hval : decChunk019[12]! = 18 := rfl
    have ht : placeTemplate 270 6 21 46 = 18 := rfl
    have himg : intfmtImage[316]! = decChunk019[12]! :=
      cell304 12 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 47 =>
    have hval : decChunk019[13]! = 318 := rfl
    have ht : placeTemplate 270 6 21 47 = 318 := rfl
    have himg : intfmtImage[317]! = decChunk019[13]! :=
      cell304 13 (by decide)
    have hnat : (318 : Word) = UInt16.ofNat 318 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 48 =>
    have hval : decChunk019[14]! = 0 := rfl
    have ht : placeTemplate 270 6 21 48 = 0 := rfl
    have himg : intfmtImage[318]! = decChunk019[14]! :=
      cell304 14 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 49 =>
    have hval : decChunk019[15]! = 18 := rfl
    have ht : placeTemplate 270 6 21 49 = 18 := rfl
    have himg : intfmtImage[319]! = decChunk019[15]! :=
      cell304 15 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 50 =>
    have hval : decChunk020[0]! = 324 := rfl
    have ht : placeTemplate 270 6 21 50 = 324 := rfl
    have himg : intfmtImage[320]! = decChunk020[0]! :=
      cell320 0 (by decide)
    have hnat : (324 : Word) = UInt16.ofNat 324 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 51 =>
    have hval : decChunk020[1]! = 0 := rfl
    have ht : placeTemplate 270 6 21 51 = 0 := rfl
    have himg : intfmtImage[321]! = decChunk020[1]! :=
      cell320 1 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 52 =>
    have hval : decChunk020[2]! = 0 := rfl
    have ht : placeTemplate 270 6 21 52 = 0 := rfl
    have himg : intfmtImage[322]! = decChunk020[2]! :=
      cell320 2 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 53 =>
    have hval : decChunk020[3]! = 336 := rfl
    have ht : placeTemplate 270 6 21 53 = 336 := rfl
    have himg : intfmtImage[323]! = decChunk020[3]! :=
      cell320 3 (by decide)
    have hnat : (336 : Word) = UInt16.ofNat 336 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 54 =>
    have hval : decChunk020[4]! = 3 := rfl
    have ht : placeTemplate 270 6 21 54 = 3 := rfl
    have himg : intfmtImage[324]! = decChunk020[4]! :=
      cell320 4 (by decide)
    have hnat : (3 : Word) = UInt16.ofNat 3 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 55 =>
    have hval : decChunk020[5]! = 0 := rfl
    have ht : placeTemplate 270 6 21 55 = 0 := rfl
    have himg : intfmtImage[325]! = decChunk020[5]! :=
      cell320 5 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 56 =>
    have hval : decChunk020[6]! = 327 := rfl
    have ht : placeTemplate 270 6 21 56 = 327 := rfl
    have himg : intfmtImage[326]! = decChunk020[6]! :=
      cell320 6 (by decide)
    have hnat : (327 : Word) = UInt16.ofNat 327 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 57 =>
    have hval : decChunk020[7]! = 0 := rfl
    have ht : placeTemplate 270 6 21 57 = 0 := rfl
    have himg : intfmtImage[327]! = decChunk020[7]! :=
      cell320 7 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 58 =>
    have hval : decChunk020[8]! = 18 := rfl
    have ht : placeTemplate 270 6 21 58 = 18 := rfl
    have himg : intfmtImage[328]! = decChunk020[8]! :=
      cell320 8 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 59 =>
    have hval : decChunk020[9]! = 330 := rfl
    have ht : placeTemplate 270 6 21 59 = 330 := rfl
    have himg : intfmtImage[329]! = decChunk020[9]! :=
      cell320 9 (by decide)
    have hnat : (330 : Word) = UInt16.ofNat 330 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 60 =>
    have hval : decChunk020[10]! = 0 := rfl
    have ht : placeTemplate 270 6 21 60 = 0 := rfl
    have himg : intfmtImage[330]! = decChunk020[10]! :=
      cell320 10 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 61 =>
    have hval : decChunk020[11]! = 0 := rfl
    have ht : placeTemplate 270 6 21 61 = 0 := rfl
    have himg : intfmtImage[331]! = decChunk020[11]! :=
      cell320 11 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 62 =>
    have hval : decChunk020[12]! = 333 := rfl
    have ht : placeTemplate 270 6 21 62 = 333 := rfl
    have himg : intfmtImage[332]! = decChunk020[12]! :=
      cell320 12 (by decide)
    have hnat : (333 : Word) = UInt16.ofNat 333 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 63 =>
    have hval : decChunk020[13]! = 0 := rfl
    have ht : placeTemplate 270 6 21 63 = 0 := rfl
    have himg : intfmtImage[333]! = decChunk020[13]! :=
      cell320 13 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 64 =>
    have hval : decChunk020[14]! = 18 := rfl
    have ht : placeTemplate 270 6 21 64 = 18 := rfl
    have himg : intfmtImage[334]! = decChunk020[14]! :=
      cell320 14 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 65 =>
    have hval : decChunk020[15]! = 351 := rfl
    have ht : placeTemplate 270 6 21 65 = 351 := rfl
    have himg : intfmtImage[335]! = decChunk020[15]! :=
      cell320 15 (by decide)
    have hnat : (351 : Word) = UInt16.ofNat 351 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 66 =>
    have hval : decChunk021[0]! = 6 := rfl
    have ht : placeTemplate 270 6 21 66 = 6 := rfl
    have himg : intfmtImage[336]! = decChunk021[0]! :=
      cell336 0 (by decide)
    have hnat : (6 : Word) = UInt16.ofNat 6 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 67 =>
    have hval : decChunk021[1]! = 17 := rfl
    have ht : placeTemplate 270 6 21 67 = 17 := rfl
    have himg : intfmtImage[337]! = decChunk021[1]! :=
      cell336 1 (by decide)
    have hnat : (17 : Word) = UInt16.ofNat 17 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 68 =>
    have hval : decChunk021[2]! = 339 := rfl
    have ht : placeTemplate 270 6 21 68 = 339 := rfl
    have himg : intfmtImage[338]! = decChunk021[2]! :=
      cell336 2 (by decide)
    have hnat : (339 : Word) = UInt16.ofNat 339 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 69 =>
    have hval : decChunk021[3]! = 3 := rfl
    have ht : placeTemplate 270 6 21 69 = 3 := rfl
    have himg : intfmtImage[339]! = decChunk021[3]! :=
      cell336 3 (by decide)
    have hnat : (3 : Word) = UInt16.ofNat 3 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 70 =>
    have hval : decChunk021[4]! = 0 := rfl
    have ht : placeTemplate 270 6 21 70 = 0 := rfl
    have himg : intfmtImage[340]! = decChunk021[4]! :=
      cell336 4 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 71 =>
    have hval : decChunk021[5]! = 342 := rfl
    have ht : placeTemplate 270 6 21 71 = 342 := rfl
    have himg : intfmtImage[341]! = decChunk021[5]! :=
      cell336 5 (by decide)
    have hnat : (342 : Word) = UInt16.ofNat 342 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 72 =>
    have hval : decChunk021[6]! = 0 := rfl
    have ht : placeTemplate 270 6 21 72 = 0 := rfl
    have himg : intfmtImage[342]! = decChunk021[6]! :=
      cell336 6 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 73 =>
    have hval : decChunk021[7]! = 21 := rfl
    have ht : placeTemplate 270 6 21 73 = 21 := rfl
    have himg : intfmtImage[343]! = decChunk021[7]! :=
      cell336 7 (by decide)
    have hnat : (21 : Word) = UInt16.ofNat 21 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 74 =>
    have hval : decChunk021[8]! = 345 := rfl
    have ht : placeTemplate 270 6 21 74 = 345 := rfl
    have himg : intfmtImage[344]! = decChunk021[8]! :=
      cell336 8 (by decide)
    have hnat : (345 : Word) = UInt16.ofNat 345 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 75 =>
    have hval : decChunk021[9]! = 0 := rfl
    have ht : placeTemplate 270 6 21 75 = 0 := rfl
    have himg : intfmtImage[345]! = decChunk021[9]! :=
      cell336 9 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 76 =>
    have hval : decChunk021[10]! = 0 := rfl
    have ht : placeTemplate 270 6 21 76 = 0 := rfl
    have himg : intfmtImage[346]! = decChunk021[10]! :=
      cell336 10 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 77 =>
    have hval : decChunk021[11]! = 348 := rfl
    have ht : placeTemplate 270 6 21 77 = 348 := rfl
    have himg : intfmtImage[347]! = decChunk021[11]! :=
      cell336 11 (by decide)
    have hnat : (348 : Word) = UInt16.ofNat 348 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 78 =>
    have hval : decChunk021[12]! = 0 := rfl
    have ht : placeTemplate 270 6 21 78 = 0 := rfl
    have himg : intfmtImage[348]! = decChunk021[12]! :=
      cell336 12 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 79 =>
    have hval : decChunk021[13]! = 0 := rfl
    have ht : placeTemplate 270 6 21 79 = 0 := rfl
    have himg : intfmtImage[349]! = decChunk021[13]! :=
      cell336 13 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 80 =>
    have hval : decChunk021[14]! = 270 := rfl
    have ht : placeTemplate 270 6 21 80 = 270 := rfl
    have himg : intfmtImage[350]! = decChunk021[14]! :=
      cell336 14 (by decide)
    have hnat : (270 : Word) = UInt16.ofNat 270 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | k + 81 =>
    have : k + 81 < 81 := h
    omega

/-- The assembled image matches `placeTemplate` at the `p2` loop. -/
theorem p2_image (off : Nat) (h : off < 81) :
    intfmtImage[351 + off]! = UInt16.ofNat (placeTemplate 351 5 22 off) := by
  match off with
  | 0 =>
    have hval : decChunk021[15]! = 18 := rfl
    have ht : placeTemplate 351 5 22 0 = 18 := rfl
    have himg : intfmtImage[351]! = decChunk021[15]! :=
      cell336 15 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 1 =>
    have hval : decChunk022[0]! = 18 := rfl
    have ht : placeTemplate 351 5 22 1 = 18 := rfl
    have himg : intfmtImage[352]! = decChunk022[0]! :=
      cell352 0 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 2 =>
    have hval : decChunk022[1]! = 354 := rfl
    have ht : placeTemplate 351 5 22 2 = 354 := rfl
    have himg : intfmtImage[353]! = decChunk022[1]! :=
      cell352 1 (by decide)
    have hnat : (354 : Word) = UInt16.ofNat 354 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 3 =>
    have hval : decChunk022[2]! = 17 := rfl
    have ht : placeTemplate 351 5 22 3 = 17 := rfl
    have himg : intfmtImage[354]! = decChunk022[2]! :=
      cell352 2 (by decide)
    have hnat : (17 : Word) = UInt16.ofNat 17 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 4 =>
    have hval : decChunk022[3]! = 0 := rfl
    have ht : placeTemplate 351 5 22 4 = 0 := rfl
    have himg : intfmtImage[355]! = decChunk022[3]! :=
      cell352 3 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 5 =>
    have hval : decChunk022[4]! = 357 := rfl
    have ht : placeTemplate 351 5 22 5 = 357 := rfl
    have himg : intfmtImage[356]! = decChunk022[4]! :=
      cell352 4 (by decide)
    have hnat : (357 : Word) = UInt16.ofNat 357 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 6 =>
    have hval : decChunk022[5]! = 0 := rfl
    have ht : placeTemplate 351 5 22 6 = 0 := rfl
    have himg : intfmtImage[357]! = decChunk022[5]! :=
      cell352 5 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 7 =>
    have hval : decChunk022[6]! = 18 := rfl
    have ht : placeTemplate 351 5 22 7 = 18 := rfl
    have himg : intfmtImage[358]! = decChunk022[6]! :=
      cell352 6 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 8 =>
    have hval : decChunk022[7]! = 360 := rfl
    have ht : placeTemplate 351 5 22 8 = 360 := rfl
    have himg : intfmtImage[359]! = decChunk022[7]! :=
      cell352 7 (by decide)
    have hnat : (360 : Word) = UInt16.ofNat 360 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 9 =>
    have hval : decChunk022[8]! = 0 := rfl
    have ht : placeTemplate 351 5 22 9 = 0 := rfl
    have himg : intfmtImage[360]! = decChunk022[8]! :=
      cell352 8 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 10 =>
    have hval : decChunk022[9]! = 0 := rfl
    have ht : placeTemplate 351 5 22 10 = 0 := rfl
    have himg : intfmtImage[361]! = decChunk022[9]! :=
      cell352 9 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 11 =>
    have hval : decChunk022[10]! = 363 := rfl
    have ht : placeTemplate 351 5 22 11 = 363 := rfl
    have himg : intfmtImage[362]! = decChunk022[10]! :=
      cell352 10 (by decide)
    have hnat : (363 : Word) = UInt16.ofNat 363 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 12 =>
    have hval : decChunk022[11]! = 0 := rfl
    have ht : placeTemplate 351 5 22 12 = 0 := rfl
    have himg : intfmtImage[363]! = decChunk022[11]! :=
      cell352 11 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 13 =>
    have hval : decChunk022[12]! = 18 := rfl
    have ht : placeTemplate 351 5 22 13 = 18 := rfl
    have himg : intfmtImage[364]! = decChunk022[12]! :=
      cell352 12 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 14 =>
    have hval : decChunk022[13]! = 369 := rfl
    have ht : placeTemplate 351 5 22 14 = 369 := rfl
    have himg : intfmtImage[365]! = decChunk022[13]! :=
      cell352 13 (by decide)
    have hnat : (369 : Word) = UInt16.ofNat 369 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 15 =>
    have hval : decChunk022[14]! = 0 := rfl
    have ht : placeTemplate 351 5 22 15 = 0 := rfl
    have himg : intfmtImage[366]! = decChunk022[14]! :=
      cell352 14 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 16 =>
    have hval : decChunk022[15]! = 0 := rfl
    have ht : placeTemplate 351 5 22 16 = 0 := rfl
    have himg : intfmtImage[367]! = decChunk022[15]! :=
      cell352 15 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 17 =>
    have hval : decChunk023[0]! = 384 := rfl
    have ht : placeTemplate 351 5 22 17 = 384 := rfl
    have himg : intfmtImage[368]! = decChunk023[0]! :=
      cell368 0 (by decide)
    have hnat : (384 : Word) = UInt16.ofNat 384 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 18 =>
    have hval : decChunk023[1]! = 3 := rfl
    have ht : placeTemplate 351 5 22 18 = 3 := rfl
    have himg : intfmtImage[369]! = decChunk023[1]! :=
      cell368 1 (by decide)
    have hnat : (3 : Word) = UInt16.ofNat 3 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 19 =>
    have hval : decChunk023[2]! = 0 := rfl
    have ht : placeTemplate 351 5 22 19 = 0 := rfl
    have himg : intfmtImage[370]! = decChunk023[2]! :=
      cell368 2 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 20 =>
    have hval : decChunk023[3]! = 372 := rfl
    have ht : placeTemplate 351 5 22 20 = 372 := rfl
    have himg : intfmtImage[371]! = decChunk023[3]! :=
      cell368 3 (by decide)
    have hnat : (372 : Word) = UInt16.ofNat 372 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 21 =>
    have hval : decChunk023[4]! = 0 := rfl
    have ht : placeTemplate 351 5 22 21 = 0 := rfl
    have himg : intfmtImage[372]! = decChunk023[4]! :=
      cell368 4 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 22 =>
    have hval : decChunk023[5]! = 18 := rfl
    have ht : placeTemplate 351 5 22 22 = 18 := rfl
    have himg : intfmtImage[373]! = decChunk023[5]! :=
      cell368 5 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 23 =>
    have hval : decChunk023[6]! = 375 := rfl
    have ht : placeTemplate 351 5 22 23 = 375 := rfl
    have himg : intfmtImage[374]! = decChunk023[6]! :=
      cell368 6 (by decide)
    have hnat : (375 : Word) = UInt16.ofNat 375 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 24 =>
    have hval : decChunk023[7]! = 0 := rfl
    have ht : placeTemplate 351 5 22 24 = 0 := rfl
    have himg : intfmtImage[375]! = decChunk023[7]! :=
      cell368 7 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 25 =>
    have hval : decChunk023[8]! = 0 := rfl
    have ht : placeTemplate 351 5 22 25 = 0 := rfl
    have himg : intfmtImage[376]! = decChunk023[8]! :=
      cell368 8 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 26 =>
    have hval : decChunk023[9]! = 378 := rfl
    have ht : placeTemplate 351 5 22 26 = 378 := rfl
    have himg : intfmtImage[377]! = decChunk023[9]! :=
      cell368 9 (by decide)
    have hnat : (378 : Word) = UInt16.ofNat 378 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 27 =>
    have hval : decChunk023[10]! = 0 := rfl
    have ht : placeTemplate 351 5 22 27 = 0 := rfl
    have himg : intfmtImage[378]! = decChunk023[10]! :=
      cell368 10 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 28 =>
    have hval : decChunk023[11]! = 18 := rfl
    have ht : placeTemplate 351 5 22 28 = 18 := rfl
    have himg : intfmtImage[379]! = decChunk023[11]! :=
      cell368 11 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 29 =>
    have hval : decChunk023[12]! = 417 := rfl
    have ht : placeTemplate 351 5 22 29 = 417 := rfl
    have himg : intfmtImage[380]! = decChunk023[12]! :=
      cell368 12 (by decide)
    have hnat : (417 : Word) = UInt16.ofNat 417 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 30 =>
    have hval : decChunk023[13]! = 0 := rfl
    have ht : placeTemplate 351 5 22 30 = 0 := rfl
    have himg : intfmtImage[381]! = decChunk023[13]! :=
      cell368 13 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 31 =>
    have hval : decChunk023[14]! = 0 := rfl
    have ht : placeTemplate 351 5 22 31 = 0 := rfl
    have himg : intfmtImage[382]! = decChunk023[14]! :=
      cell368 14 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 32 =>
    have hval : decChunk023[15]! = 432 := rfl
    have ht : placeTemplate 351 5 22 32 = 432 := rfl
    have himg : intfmtImage[383]! = decChunk023[15]! :=
      cell368 15 (by decide)
    have hnat : (432 : Word) = UInt16.ofNat 432 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 33 =>
    have hval : decChunk024[0]! = 18 := rfl
    have ht : placeTemplate 351 5 22 33 = 18 := rfl
    have himg : intfmtImage[384]! = decChunk024[0]! :=
      cell384 0 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 34 =>
    have hval : decChunk024[1]! = 18 := rfl
    have ht : placeTemplate 351 5 22 34 = 18 := rfl
    have himg : intfmtImage[385]! = decChunk024[1]! :=
      cell384 1 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 35 =>
    have hval : decChunk024[2]! = 387 := rfl
    have ht : placeTemplate 351 5 22 35 = 387 := rfl
    have himg : intfmtImage[386]! = decChunk024[2]! :=
      cell384 2 (by decide)
    have hnat : (387 : Word) = UInt16.ofNat 387 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 36 =>
    have hval : decChunk024[3]! = 17 := rfl
    have ht : placeTemplate 351 5 22 36 = 17 := rfl
    have himg : intfmtImage[387]! = decChunk024[3]! :=
      cell384 3 (by decide)
    have hnat : (17 : Word) = UInt16.ofNat 17 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 37 =>
    have hval : decChunk024[4]! = 0 := rfl
    have ht : placeTemplate 351 5 22 37 = 0 := rfl
    have himg : intfmtImage[388]! = decChunk024[4]! :=
      cell384 4 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 38 =>
    have hval : decChunk024[5]! = 390 := rfl
    have ht : placeTemplate 351 5 22 38 = 390 := rfl
    have himg : intfmtImage[389]! = decChunk024[5]! :=
      cell384 5 (by decide)
    have hnat : (390 : Word) = UInt16.ofNat 390 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 39 =>
    have hval : decChunk024[6]! = 0 := rfl
    have ht : placeTemplate 351 5 22 39 = 0 := rfl
    have himg : intfmtImage[390]! = decChunk024[6]! :=
      cell384 6 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 40 =>
    have hval : decChunk024[7]! = 18 := rfl
    have ht : placeTemplate 351 5 22 40 = 18 := rfl
    have himg : intfmtImage[391]! = decChunk024[7]! :=
      cell384 7 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 41 =>
    have hval : decChunk024[8]! = 393 := rfl
    have ht : placeTemplate 351 5 22 41 = 393 := rfl
    have himg : intfmtImage[392]! = decChunk024[8]! :=
      cell384 8 (by decide)
    have hnat : (393 : Word) = UInt16.ofNat 393 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 42 =>
    have hval : decChunk024[9]! = 0 := rfl
    have ht : placeTemplate 351 5 22 42 = 0 := rfl
    have himg : intfmtImage[393]! = decChunk024[9]! :=
      cell384 9 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 43 =>
    have hval : decChunk024[10]! = 0 := rfl
    have ht : placeTemplate 351 5 22 43 = 0 := rfl
    have himg : intfmtImage[394]! = decChunk024[10]! :=
      cell384 10 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 44 =>
    have hval : decChunk024[11]! = 396 := rfl
    have ht : placeTemplate 351 5 22 44 = 396 := rfl
    have himg : intfmtImage[395]! = decChunk024[11]! :=
      cell384 11 (by decide)
    have hnat : (396 : Word) = UInt16.ofNat 396 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 45 =>
    have hval : decChunk024[12]! = 5 := rfl
    have ht : placeTemplate 351 5 22 45 = 5 := rfl
    have himg : intfmtImage[396]! = decChunk024[12]! :=
      cell384 12 (by decide)
    have hnat : (5 : Word) = UInt16.ofNat 5 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 46 =>
    have hval : decChunk024[13]! = 18 := rfl
    have ht : placeTemplate 351 5 22 46 = 18 := rfl
    have himg : intfmtImage[397]! = decChunk024[13]! :=
      cell384 13 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 47 =>
    have hval : decChunk024[14]! = 399 := rfl
    have ht : placeTemplate 351 5 22 47 = 399 := rfl
    have himg : intfmtImage[398]! = decChunk024[14]! :=
      cell384 14 (by decide)
    have hnat : (399 : Word) = UInt16.ofNat 399 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 48 =>
    have hval : decChunk024[15]! = 0 := rfl
    have ht : placeTemplate 351 5 22 48 = 0 := rfl
    have himg : intfmtImage[399]! = decChunk024[15]! :=
      cell384 15 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 49 =>
    have hval : decChunk025[0]! = 18 := rfl
    have ht : placeTemplate 351 5 22 49 = 18 := rfl
    have himg : intfmtImage[400]! = decChunk025[0]! :=
      cell400 0 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 50 =>
    have hval : decChunk025[1]! = 405 := rfl
    have ht : placeTemplate 351 5 22 50 = 405 := rfl
    have himg : intfmtImage[401]! = decChunk025[1]! :=
      cell400 1 (by decide)
    have hnat : (405 : Word) = UInt16.ofNat 405 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 51 =>
    have hval : decChunk025[2]! = 0 := rfl
    have ht : placeTemplate 351 5 22 51 = 0 := rfl
    have himg : intfmtImage[402]! = decChunk025[2]! :=
      cell400 2 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 52 =>
    have hval : decChunk025[3]! = 0 := rfl
    have ht : placeTemplate 351 5 22 52 = 0 := rfl
    have himg : intfmtImage[403]! = decChunk025[3]! :=
      cell400 3 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 53 =>
    have hval : decChunk025[4]! = 417 := rfl
    have ht : placeTemplate 351 5 22 53 = 417 := rfl
    have himg : intfmtImage[404]! = decChunk025[4]! :=
      cell400 4 (by decide)
    have hnat : (417 : Word) = UInt16.ofNat 417 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 54 =>
    have hval : decChunk025[5]! = 3 := rfl
    have ht : placeTemplate 351 5 22 54 = 3 := rfl
    have himg : intfmtImage[405]! = decChunk025[5]! :=
      cell400 5 (by decide)
    have hnat : (3 : Word) = UInt16.ofNat 3 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 55 =>
    have hval : decChunk025[6]! = 0 := rfl
    have ht : placeTemplate 351 5 22 55 = 0 := rfl
    have himg : intfmtImage[406]! = decChunk025[6]! :=
      cell400 6 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 56 =>
    have hval : decChunk025[7]! = 408 := rfl
    have ht : placeTemplate 351 5 22 56 = 408 := rfl
    have himg : intfmtImage[407]! = decChunk025[7]! :=
      cell400 7 (by decide)
    have hnat : (408 : Word) = UInt16.ofNat 408 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 57 =>
    have hval : decChunk025[8]! = 0 := rfl
    have ht : placeTemplate 351 5 22 57 = 0 := rfl
    have himg : intfmtImage[408]! = decChunk025[8]! :=
      cell400 8 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 58 =>
    have hval : decChunk025[9]! = 18 := rfl
    have ht : placeTemplate 351 5 22 58 = 18 := rfl
    have himg : intfmtImage[409]! = decChunk025[9]! :=
      cell400 9 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 59 =>
    have hval : decChunk025[10]! = 411 := rfl
    have ht : placeTemplate 351 5 22 59 = 411 := rfl
    have himg : intfmtImage[410]! = decChunk025[10]! :=
      cell400 10 (by decide)
    have hnat : (411 : Word) = UInt16.ofNat 411 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 60 =>
    have hval : decChunk025[11]! = 0 := rfl
    have ht : placeTemplate 351 5 22 60 = 0 := rfl
    have himg : intfmtImage[411]! = decChunk025[11]! :=
      cell400 11 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 61 =>
    have hval : decChunk025[12]! = 0 := rfl
    have ht : placeTemplate 351 5 22 61 = 0 := rfl
    have himg : intfmtImage[412]! = decChunk025[12]! :=
      cell400 12 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 62 =>
    have hval : decChunk025[13]! = 414 := rfl
    have ht : placeTemplate 351 5 22 62 = 414 := rfl
    have himg : intfmtImage[413]! = decChunk025[13]! :=
      cell400 13 (by decide)
    have hnat : (414 : Word) = UInt16.ofNat 414 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 63 =>
    have hval : decChunk025[14]! = 0 := rfl
    have ht : placeTemplate 351 5 22 63 = 0 := rfl
    have himg : intfmtImage[414]! = decChunk025[14]! :=
      cell400 14 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 64 =>
    have hval : decChunk025[15]! = 18 := rfl
    have ht : placeTemplate 351 5 22 64 = 18 := rfl
    have himg : intfmtImage[415]! = decChunk025[15]! :=
      cell400 15 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 65 =>
    have hval : decChunk026[0]! = 432 := rfl
    have ht : placeTemplate 351 5 22 65 = 432 := rfl
    have himg : intfmtImage[416]! = decChunk026[0]! :=
      cell416 0 (by decide)
    have hnat : (432 : Word) = UInt16.ofNat 432 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 66 =>
    have hval : decChunk026[1]! = 5 := rfl
    have ht : placeTemplate 351 5 22 66 = 5 := rfl
    have himg : intfmtImage[417]! = decChunk026[1]! :=
      cell416 1 (by decide)
    have hnat : (5 : Word) = UInt16.ofNat 5 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 67 =>
    have hval : decChunk026[2]! = 17 := rfl
    have ht : placeTemplate 351 5 22 67 = 17 := rfl
    have himg : intfmtImage[418]! = decChunk026[2]! :=
      cell416 2 (by decide)
    have hnat : (17 : Word) = UInt16.ofNat 17 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 68 =>
    have hval : decChunk026[3]! = 420 := rfl
    have ht : placeTemplate 351 5 22 68 = 420 := rfl
    have himg : intfmtImage[419]! = decChunk026[3]! :=
      cell416 3 (by decide)
    have hnat : (420 : Word) = UInt16.ofNat 420 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 69 =>
    have hval : decChunk026[4]! = 3 := rfl
    have ht : placeTemplate 351 5 22 69 = 3 := rfl
    have himg : intfmtImage[420]! = decChunk026[4]! :=
      cell416 4 (by decide)
    have hnat : (3 : Word) = UInt16.ofNat 3 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 70 =>
    have hval : decChunk026[5]! = 0 := rfl
    have ht : placeTemplate 351 5 22 70 = 0 := rfl
    have himg : intfmtImage[421]! = decChunk026[5]! :=
      cell416 5 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 71 =>
    have hval : decChunk026[6]! = 423 := rfl
    have ht : placeTemplate 351 5 22 71 = 423 := rfl
    have himg : intfmtImage[422]! = decChunk026[6]! :=
      cell416 6 (by decide)
    have hnat : (423 : Word) = UInt16.ofNat 423 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 72 =>
    have hval : decChunk026[7]! = 0 := rfl
    have ht : placeTemplate 351 5 22 72 = 0 := rfl
    have himg : intfmtImage[423]! = decChunk026[7]! :=
      cell416 7 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 73 =>
    have hval : decChunk026[8]! = 22 := rfl
    have ht : placeTemplate 351 5 22 73 = 22 := rfl
    have himg : intfmtImage[424]! = decChunk026[8]! :=
      cell416 8 (by decide)
    have hnat : (22 : Word) = UInt16.ofNat 22 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 74 =>
    have hval : decChunk026[9]! = 426 := rfl
    have ht : placeTemplate 351 5 22 74 = 426 := rfl
    have himg : intfmtImage[425]! = decChunk026[9]! :=
      cell416 9 (by decide)
    have hnat : (426 : Word) = UInt16.ofNat 426 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 75 =>
    have hval : decChunk026[10]! = 0 := rfl
    have ht : placeTemplate 351 5 22 75 = 0 := rfl
    have himg : intfmtImage[426]! = decChunk026[10]! :=
      cell416 10 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 76 =>
    have hval : decChunk026[11]! = 0 := rfl
    have ht : placeTemplate 351 5 22 76 = 0 := rfl
    have himg : intfmtImage[427]! = decChunk026[11]! :=
      cell416 11 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 77 =>
    have hval : decChunk026[12]! = 429 := rfl
    have ht : placeTemplate 351 5 22 77 = 429 := rfl
    have himg : intfmtImage[428]! = decChunk026[12]! :=
      cell416 12 (by decide)
    have hnat : (429 : Word) = UInt16.ofNat 429 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 78 =>
    have hval : decChunk026[13]! = 0 := rfl
    have ht : placeTemplate 351 5 22 78 = 0 := rfl
    have himg : intfmtImage[429]! = decChunk026[13]! :=
      cell416 13 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 79 =>
    have hval : decChunk026[14]! = 0 := rfl
    have ht : placeTemplate 351 5 22 79 = 0 := rfl
    have himg : intfmtImage[430]! = decChunk026[14]! :=
      cell416 14 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 80 =>
    have hval : decChunk026[15]! = 351 := rfl
    have ht : placeTemplate 351 5 22 80 = 351 := rfl
    have himg : intfmtImage[431]! = decChunk026[15]! :=
      cell416 15 (by decide)
    have hnat : (351 : Word) = UInt16.ofNat 351 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | k + 81 =>
    have : k + 81 < 81 := h
    omega

/-- The assembled image matches `placeTemplate` at the `p3` loop. -/
theorem p3_image (off : Nat) (h : off < 81) :
    intfmtImage[432 + off]! = UInt16.ofNat (placeTemplate 432 4 23 off) := by
  match off with
  | 0 =>
    have hval : decChunk027[0]! = 18 := rfl
    have ht : placeTemplate 432 4 23 0 = 18 := rfl
    have himg : intfmtImage[432]! = decChunk027[0]! :=
      cell432 0 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 1 =>
    have hval : decChunk027[1]! = 18 := rfl
    have ht : placeTemplate 432 4 23 1 = 18 := rfl
    have himg : intfmtImage[433]! = decChunk027[1]! :=
      cell432 1 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 2 =>
    have hval : decChunk027[2]! = 435 := rfl
    have ht : placeTemplate 432 4 23 2 = 435 := rfl
    have himg : intfmtImage[434]! = decChunk027[2]! :=
      cell432 2 (by decide)
    have hnat : (435 : Word) = UInt16.ofNat 435 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 3 =>
    have hval : decChunk027[3]! = 17 := rfl
    have ht : placeTemplate 432 4 23 3 = 17 := rfl
    have himg : intfmtImage[435]! = decChunk027[3]! :=
      cell432 3 (by decide)
    have hnat : (17 : Word) = UInt16.ofNat 17 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 4 =>
    have hval : decChunk027[4]! = 0 := rfl
    have ht : placeTemplate 432 4 23 4 = 0 := rfl
    have himg : intfmtImage[436]! = decChunk027[4]! :=
      cell432 4 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 5 =>
    have hval : decChunk027[5]! = 438 := rfl
    have ht : placeTemplate 432 4 23 5 = 438 := rfl
    have himg : intfmtImage[437]! = decChunk027[5]! :=
      cell432 5 (by decide)
    have hnat : (438 : Word) = UInt16.ofNat 438 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 6 =>
    have hval : decChunk027[6]! = 0 := rfl
    have ht : placeTemplate 432 4 23 6 = 0 := rfl
    have himg : intfmtImage[438]! = decChunk027[6]! :=
      cell432 6 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 7 =>
    have hval : decChunk027[7]! = 18 := rfl
    have ht : placeTemplate 432 4 23 7 = 18 := rfl
    have himg : intfmtImage[439]! = decChunk027[7]! :=
      cell432 7 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 8 =>
    have hval : decChunk027[8]! = 441 := rfl
    have ht : placeTemplate 432 4 23 8 = 441 := rfl
    have himg : intfmtImage[440]! = decChunk027[8]! :=
      cell432 8 (by decide)
    have hnat : (441 : Word) = UInt16.ofNat 441 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 9 =>
    have hval : decChunk027[9]! = 0 := rfl
    have ht : placeTemplate 432 4 23 9 = 0 := rfl
    have himg : intfmtImage[441]! = decChunk027[9]! :=
      cell432 9 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 10 =>
    have hval : decChunk027[10]! = 0 := rfl
    have ht : placeTemplate 432 4 23 10 = 0 := rfl
    have himg : intfmtImage[442]! = decChunk027[10]! :=
      cell432 10 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 11 =>
    have hval : decChunk027[11]! = 444 := rfl
    have ht : placeTemplate 432 4 23 11 = 444 := rfl
    have himg : intfmtImage[443]! = decChunk027[11]! :=
      cell432 11 (by decide)
    have hnat : (444 : Word) = UInt16.ofNat 444 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 12 =>
    have hval : decChunk027[12]! = 0 := rfl
    have ht : placeTemplate 432 4 23 12 = 0 := rfl
    have himg : intfmtImage[444]! = decChunk027[12]! :=
      cell432 12 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 13 =>
    have hval : decChunk027[13]! = 18 := rfl
    have ht : placeTemplate 432 4 23 13 = 18 := rfl
    have himg : intfmtImage[445]! = decChunk027[13]! :=
      cell432 13 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 14 =>
    have hval : decChunk027[14]! = 450 := rfl
    have ht : placeTemplate 432 4 23 14 = 450 := rfl
    have himg : intfmtImage[446]! = decChunk027[14]! :=
      cell432 14 (by decide)
    have hnat : (450 : Word) = UInt16.ofNat 450 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 15 =>
    have hval : decChunk027[15]! = 0 := rfl
    have ht : placeTemplate 432 4 23 15 = 0 := rfl
    have himg : intfmtImage[447]! = decChunk027[15]! :=
      cell432 15 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 16 =>
    have hval : decChunk028[0]! = 0 := rfl
    have ht : placeTemplate 432 4 23 16 = 0 := rfl
    have himg : intfmtImage[448]! = decChunk028[0]! :=
      cell448 0 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 17 =>
    have hval : decChunk028[1]! = 465 := rfl
    have ht : placeTemplate 432 4 23 17 = 465 := rfl
    have himg : intfmtImage[449]! = decChunk028[1]! :=
      cell448 1 (by decide)
    have hnat : (465 : Word) = UInt16.ofNat 465 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 18 =>
    have hval : decChunk028[2]! = 3 := rfl
    have ht : placeTemplate 432 4 23 18 = 3 := rfl
    have himg : intfmtImage[450]! = decChunk028[2]! :=
      cell448 2 (by decide)
    have hnat : (3 : Word) = UInt16.ofNat 3 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 19 =>
    have hval : decChunk028[3]! = 0 := rfl
    have ht : placeTemplate 432 4 23 19 = 0 := rfl
    have himg : intfmtImage[451]! = decChunk028[3]! :=
      cell448 3 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 20 =>
    have hval : decChunk028[4]! = 453 := rfl
    have ht : placeTemplate 432 4 23 20 = 453 := rfl
    have himg : intfmtImage[452]! = decChunk028[4]! :=
      cell448 4 (by decide)
    have hnat : (453 : Word) = UInt16.ofNat 453 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 21 =>
    have hval : decChunk028[5]! = 0 := rfl
    have ht : placeTemplate 432 4 23 21 = 0 := rfl
    have himg : intfmtImage[453]! = decChunk028[5]! :=
      cell448 5 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 22 =>
    have hval : decChunk028[6]! = 18 := rfl
    have ht : placeTemplate 432 4 23 22 = 18 := rfl
    have himg : intfmtImage[454]! = decChunk028[6]! :=
      cell448 6 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 23 =>
    have hval : decChunk028[7]! = 456 := rfl
    have ht : placeTemplate 432 4 23 23 = 456 := rfl
    have himg : intfmtImage[455]! = decChunk028[7]! :=
      cell448 7 (by decide)
    have hnat : (456 : Word) = UInt16.ofNat 456 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 24 =>
    have hval : decChunk028[8]! = 0 := rfl
    have ht : placeTemplate 432 4 23 24 = 0 := rfl
    have himg : intfmtImage[456]! = decChunk028[8]! :=
      cell448 8 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 25 =>
    have hval : decChunk028[9]! = 0 := rfl
    have ht : placeTemplate 432 4 23 25 = 0 := rfl
    have himg : intfmtImage[457]! = decChunk028[9]! :=
      cell448 9 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 26 =>
    have hval : decChunk028[10]! = 459 := rfl
    have ht : placeTemplate 432 4 23 26 = 459 := rfl
    have himg : intfmtImage[458]! = decChunk028[10]! :=
      cell448 10 (by decide)
    have hnat : (459 : Word) = UInt16.ofNat 459 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 27 =>
    have hval : decChunk028[11]! = 0 := rfl
    have ht : placeTemplate 432 4 23 27 = 0 := rfl
    have himg : intfmtImage[459]! = decChunk028[11]! :=
      cell448 11 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 28 =>
    have hval : decChunk028[12]! = 18 := rfl
    have ht : placeTemplate 432 4 23 28 = 18 := rfl
    have himg : intfmtImage[460]! = decChunk028[12]! :=
      cell448 12 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 29 =>
    have hval : decChunk028[13]! = 498 := rfl
    have ht : placeTemplate 432 4 23 29 = 498 := rfl
    have himg : intfmtImage[461]! = decChunk028[13]! :=
      cell448 13 (by decide)
    have hnat : (498 : Word) = UInt16.ofNat 498 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 30 =>
    have hval : decChunk028[14]! = 0 := rfl
    have ht : placeTemplate 432 4 23 30 = 0 := rfl
    have himg : intfmtImage[462]! = decChunk028[14]! :=
      cell448 14 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 31 =>
    have hval : decChunk028[15]! = 0 := rfl
    have ht : placeTemplate 432 4 23 31 = 0 := rfl
    have himg : intfmtImage[463]! = decChunk028[15]! :=
      cell448 15 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 32 =>
    have hval : decChunk029[0]! = 513 := rfl
    have ht : placeTemplate 432 4 23 32 = 513 := rfl
    have himg : intfmtImage[464]! = decChunk029[0]! :=
      cell464 0 (by decide)
    have hnat : (513 : Word) = UInt16.ofNat 513 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 33 =>
    have hval : decChunk029[1]! = 18 := rfl
    have ht : placeTemplate 432 4 23 33 = 18 := rfl
    have himg : intfmtImage[465]! = decChunk029[1]! :=
      cell464 1 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 34 =>
    have hval : decChunk029[2]! = 18 := rfl
    have ht : placeTemplate 432 4 23 34 = 18 := rfl
    have himg : intfmtImage[466]! = decChunk029[2]! :=
      cell464 2 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 35 =>
    have hval : decChunk029[3]! = 468 := rfl
    have ht : placeTemplate 432 4 23 35 = 468 := rfl
    have himg : intfmtImage[467]! = decChunk029[3]! :=
      cell464 3 (by decide)
    have hnat : (468 : Word) = UInt16.ofNat 468 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 36 =>
    have hval : decChunk029[4]! = 17 := rfl
    have ht : placeTemplate 432 4 23 36 = 17 := rfl
    have himg : intfmtImage[468]! = decChunk029[4]! :=
      cell464 4 (by decide)
    have hnat : (17 : Word) = UInt16.ofNat 17 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 37 =>
    have hval : decChunk029[5]! = 0 := rfl
    have ht : placeTemplate 432 4 23 37 = 0 := rfl
    have himg : intfmtImage[469]! = decChunk029[5]! :=
      cell464 5 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 38 =>
    have hval : decChunk029[6]! = 471 := rfl
    have ht : placeTemplate 432 4 23 38 = 471 := rfl
    have himg : intfmtImage[470]! = decChunk029[6]! :=
      cell464 6 (by decide)
    have hnat : (471 : Word) = UInt16.ofNat 471 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 39 =>
    have hval : decChunk029[7]! = 0 := rfl
    have ht : placeTemplate 432 4 23 39 = 0 := rfl
    have himg : intfmtImage[471]! = decChunk029[7]! :=
      cell464 7 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 40 =>
    have hval : decChunk029[8]! = 18 := rfl
    have ht : placeTemplate 432 4 23 40 = 18 := rfl
    have himg : intfmtImage[472]! = decChunk029[8]! :=
      cell464 8 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 41 =>
    have hval : decChunk029[9]! = 474 := rfl
    have ht : placeTemplate 432 4 23 41 = 474 := rfl
    have himg : intfmtImage[473]! = decChunk029[9]! :=
      cell464 9 (by decide)
    have hnat : (474 : Word) = UInt16.ofNat 474 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 42 =>
    have hval : decChunk029[10]! = 0 := rfl
    have ht : placeTemplate 432 4 23 42 = 0 := rfl
    have himg : intfmtImage[474]! = decChunk029[10]! :=
      cell464 10 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 43 =>
    have hval : decChunk029[11]! = 0 := rfl
    have ht : placeTemplate 432 4 23 43 = 0 := rfl
    have himg : intfmtImage[475]! = decChunk029[11]! :=
      cell464 11 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 44 =>
    have hval : decChunk029[12]! = 477 := rfl
    have ht : placeTemplate 432 4 23 44 = 477 := rfl
    have himg : intfmtImage[476]! = decChunk029[12]! :=
      cell464 12 (by decide)
    have hnat : (477 : Word) = UInt16.ofNat 477 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 45 =>
    have hval : decChunk029[13]! = 4 := rfl
    have ht : placeTemplate 432 4 23 45 = 4 := rfl
    have himg : intfmtImage[477]! = decChunk029[13]! :=
      cell464 13 (by decide)
    have hnat : (4 : Word) = UInt16.ofNat 4 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 46 =>
    have hval : decChunk029[14]! = 18 := rfl
    have ht : placeTemplate 432 4 23 46 = 18 := rfl
    have himg : intfmtImage[478]! = decChunk029[14]! :=
      cell464 14 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 47 =>
    have hval : decChunk029[15]! = 480 := rfl
    have ht : placeTemplate 432 4 23 47 = 480 := rfl
    have himg : intfmtImage[479]! = decChunk029[15]! :=
      cell464 15 (by decide)
    have hnat : (480 : Word) = UInt16.ofNat 480 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 48 =>
    have hval : decChunk030[0]! = 0 := rfl
    have ht : placeTemplate 432 4 23 48 = 0 := rfl
    have himg : intfmtImage[480]! = decChunk030[0]! :=
      cell480 0 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 49 =>
    have hval : decChunk030[1]! = 18 := rfl
    have ht : placeTemplate 432 4 23 49 = 18 := rfl
    have himg : intfmtImage[481]! = decChunk030[1]! :=
      cell480 1 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 50 =>
    have hval : decChunk030[2]! = 486 := rfl
    have ht : placeTemplate 432 4 23 50 = 486 := rfl
    have himg : intfmtImage[482]! = decChunk030[2]! :=
      cell480 2 (by decide)
    have hnat : (486 : Word) = UInt16.ofNat 486 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 51 =>
    have hval : decChunk030[3]! = 0 := rfl
    have ht : placeTemplate 432 4 23 51 = 0 := rfl
    have himg : intfmtImage[483]! = decChunk030[3]! :=
      cell480 3 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 52 =>
    have hval : decChunk030[4]! = 0 := rfl
    have ht : placeTemplate 432 4 23 52 = 0 := rfl
    have himg : intfmtImage[484]! = decChunk030[4]! :=
      cell480 4 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 53 =>
    have hval : decChunk030[5]! = 498 := rfl
    have ht : placeTemplate 432 4 23 53 = 498 := rfl
    have himg : intfmtImage[485]! = decChunk030[5]! :=
      cell480 5 (by decide)
    have hnat : (498 : Word) = UInt16.ofNat 498 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 54 =>
    have hval : decChunk030[6]! = 3 := rfl
    have ht : placeTemplate 432 4 23 54 = 3 := rfl
    have himg : intfmtImage[486]! = decChunk030[6]! :=
      cell480 6 (by decide)
    have hnat : (3 : Word) = UInt16.ofNat 3 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 55 =>
    have hval : decChunk030[7]! = 0 := rfl
    have ht : placeTemplate 432 4 23 55 = 0 := rfl
    have himg : intfmtImage[487]! = decChunk030[7]! :=
      cell480 7 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 56 =>
    have hval : decChunk030[8]! = 489 := rfl
    have ht : placeTemplate 432 4 23 56 = 489 := rfl
    have himg : intfmtImage[488]! = decChunk030[8]! :=
      cell480 8 (by decide)
    have hnat : (489 : Word) = UInt16.ofNat 489 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 57 =>
    have hval : decChunk030[9]! = 0 := rfl
    have ht : placeTemplate 432 4 23 57 = 0 := rfl
    have himg : intfmtImage[489]! = decChunk030[9]! :=
      cell480 9 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 58 =>
    have hval : decChunk030[10]! = 18 := rfl
    have ht : placeTemplate 432 4 23 58 = 18 := rfl
    have himg : intfmtImage[490]! = decChunk030[10]! :=
      cell480 10 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 59 =>
    have hval : decChunk030[11]! = 492 := rfl
    have ht : placeTemplate 432 4 23 59 = 492 := rfl
    have himg : intfmtImage[491]! = decChunk030[11]! :=
      cell480 11 (by decide)
    have hnat : (492 : Word) = UInt16.ofNat 492 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 60 =>
    have hval : decChunk030[12]! = 0 := rfl
    have ht : placeTemplate 432 4 23 60 = 0 := rfl
    have himg : intfmtImage[492]! = decChunk030[12]! :=
      cell480 12 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 61 =>
    have hval : decChunk030[13]! = 0 := rfl
    have ht : placeTemplate 432 4 23 61 = 0 := rfl
    have himg : intfmtImage[493]! = decChunk030[13]! :=
      cell480 13 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 62 =>
    have hval : decChunk030[14]! = 495 := rfl
    have ht : placeTemplate 432 4 23 62 = 495 := rfl
    have himg : intfmtImage[494]! = decChunk030[14]! :=
      cell480 14 (by decide)
    have hnat : (495 : Word) = UInt16.ofNat 495 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 63 =>
    have hval : decChunk030[15]! = 0 := rfl
    have ht : placeTemplate 432 4 23 63 = 0 := rfl
    have himg : intfmtImage[495]! = decChunk030[15]! :=
      cell480 15 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 64 =>
    have hval : decChunk031[0]! = 18 := rfl
    have ht : placeTemplate 432 4 23 64 = 18 := rfl
    have himg : intfmtImage[496]! = decChunk031[0]! :=
      cell496 0 (by decide)
    have hnat : (18 : Word) = UInt16.ofNat 18 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 65 =>
    have hval : decChunk031[1]! = 513 := rfl
    have ht : placeTemplate 432 4 23 65 = 513 := rfl
    have himg : intfmtImage[497]! = decChunk031[1]! :=
      cell496 1 (by decide)
    have hnat : (513 : Word) = UInt16.ofNat 513 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 66 =>
    have hval : decChunk031[2]! = 4 := rfl
    have ht : placeTemplate 432 4 23 66 = 4 := rfl
    have himg : intfmtImage[498]! = decChunk031[2]! :=
      cell496 2 (by decide)
    have hnat : (4 : Word) = UInt16.ofNat 4 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 67 =>
    have hval : decChunk031[3]! = 17 := rfl
    have ht : placeTemplate 432 4 23 67 = 17 := rfl
    have himg : intfmtImage[499]! = decChunk031[3]! :=
      cell496 3 (by decide)
    have hnat : (17 : Word) = UInt16.ofNat 17 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 68 =>
    have hval : decChunk031[4]! = 501 := rfl
    have ht : placeTemplate 432 4 23 68 = 501 := rfl
    have himg : intfmtImage[500]! = decChunk031[4]! :=
      cell496 4 (by decide)
    have hnat : (501 : Word) = UInt16.ofNat 501 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 69 =>
    have hval : decChunk031[5]! = 3 := rfl
    have ht : placeTemplate 432 4 23 69 = 3 := rfl
    have himg : intfmtImage[501]! = decChunk031[5]! :=
      cell496 5 (by decide)
    have hnat : (3 : Word) = UInt16.ofNat 3 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 70 =>
    have hval : decChunk031[6]! = 0 := rfl
    have ht : placeTemplate 432 4 23 70 = 0 := rfl
    have himg : intfmtImage[502]! = decChunk031[6]! :=
      cell496 6 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 71 =>
    have hval : decChunk031[7]! = 504 := rfl
    have ht : placeTemplate 432 4 23 71 = 504 := rfl
    have himg : intfmtImage[503]! = decChunk031[7]! :=
      cell496 7 (by decide)
    have hnat : (504 : Word) = UInt16.ofNat 504 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 72 =>
    have hval : decChunk031[8]! = 0 := rfl
    have ht : placeTemplate 432 4 23 72 = 0 := rfl
    have himg : intfmtImage[504]! = decChunk031[8]! :=
      cell496 8 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 73 =>
    have hval : decChunk031[9]! = 23 := rfl
    have ht : placeTemplate 432 4 23 73 = 23 := rfl
    have himg : intfmtImage[505]! = decChunk031[9]! :=
      cell496 9 (by decide)
    have hnat : (23 : Word) = UInt16.ofNat 23 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 74 =>
    have hval : decChunk031[10]! = 507 := rfl
    have ht : placeTemplate 432 4 23 74 = 507 := rfl
    have himg : intfmtImage[506]! = decChunk031[10]! :=
      cell496 10 (by decide)
    have hnat : (507 : Word) = UInt16.ofNat 507 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 75 =>
    have hval : decChunk031[11]! = 0 := rfl
    have ht : placeTemplate 432 4 23 75 = 0 := rfl
    have himg : intfmtImage[507]! = decChunk031[11]! :=
      cell496 11 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 76 =>
    have hval : decChunk031[12]! = 0 := rfl
    have ht : placeTemplate 432 4 23 76 = 0 := rfl
    have himg : intfmtImage[508]! = decChunk031[12]! :=
      cell496 12 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 77 =>
    have hval : decChunk031[13]! = 510 := rfl
    have ht : placeTemplate 432 4 23 77 = 510 := rfl
    have himg : intfmtImage[509]! = decChunk031[13]! :=
      cell496 13 (by decide)
    have hnat : (510 : Word) = UInt16.ofNat 510 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 78 =>
    have hval : decChunk031[14]! = 0 := rfl
    have ht : placeTemplate 432 4 23 78 = 0 := rfl
    have himg : intfmtImage[510]! = decChunk031[14]! :=
      cell496 14 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 79 =>
    have hval : decChunk031[15]! = 0 := rfl
    have ht : placeTemplate 432 4 23 79 = 0 := rfl
    have himg : intfmtImage[511]! = decChunk031[15]! :=
      cell496 15 (by decide)
    have hnat : (0 : Word) = UInt16.ofNat 0 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | 80 =>
    have hval : decChunk032[0]! = 432 := rfl
    have ht : placeTemplate 432 4 23 80 = 432 := rfl
    have himg : intfmtImage[512]! = decChunk032[0]! :=
      cell512 0 (by decide)
    have hnat : (432 : Word) = UInt16.ofNat 432 := rfl
    exact himg.trans (hval.trans (ht ▸ hnat.symm))
  | k + 81 =>
    have : k + 81 < 81 := h
    omega

end IntFmt
