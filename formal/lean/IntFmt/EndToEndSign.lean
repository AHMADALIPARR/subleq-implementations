/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Signed-mode end-to-end theorems at default `CAP = 8`, `WIDTH = 0`.
Output is the 8-cell `BUF` together with `LEN`.
-/

import IntFmt.EndToEndRun

namespace IntFmt

open Subleq

set_option maxHeartbeats 4000000

theorem intToDec_nonneg {n : Int} (h : ¬ n < 0) :
    intToDec n = uToDec n.toNat := by
  unfold intToDec
  simp [h]

theorem intToDec_neg_toList {n : Int} (h : n < 0) :
    (intToDec n).toList = '-' :: (uToDec n.natAbs).toList := by
  unfold intToDec
  simp [h]

theorem formatPayload_nonneg (n : Int16) (h : ¬ n.toInt < 0) :
    formatPayload n = (uToDec n.toInt.toNat).toList.map Char.toNat := by
  unfold formatPayload
  rw [intToDec_nonneg h]

theorem formatPayload_neg (n : Int16) (h : n.toInt < 0) :
    formatPayload n = 45 :: (uToDec n.toInt.natAbs).toList.map Char.toNat := by
  unfold formatPayload
  rw [intToDec_neg_toList h]
  simp [List.map_cons, minus_toNat]

@[irreducible] def prepS (input : Word) : Machine :=
  prepMachine input 1 8

theorem prepS_eq (input : Word) : prepS input = prepMachine input 1 8 := by
  unfold prepS; rfl

@[irreducible] def bitsOf (n : Int16) : Word :=
  UInt16.ofNat n.toBitVec.toNat

theorem bitsOf_eq (n : Int16) :
    bitsOf n = UInt16.ofNat n.toBitVec.toNat := by
  unfold bitsOf; rfl

theorem loadIntfmtDec_eq_prepS (n : Int16) :
    loadIntfmtDec n = prepS (bitsOf n) := by
  rw [prepS_eq, bitsOf_eq]; rfl

@[irreducible] def afterFrontSZero (input : Word) : Machine :=
  runN (prepMachine input 1 8) 30

@[irreducible] def afterFrontSPos (input : Word) : Machine :=
  runN (prepMachine input 1 8) 26

@[irreducible] def afterFrontSNeg (input : Word) : Machine :=
  runN (prepMachine input 1 8) 40

theorem afterFrontSZero_eq (input : Word) :
    afterFrontSZero input = runN (prepMachine input 1 8) 30 := by
  unfold afterFrontSZero; rfl

theorem afterFrontSPos_eq (input : Word) :
    afterFrontSPos input = runN (prepMachine input 1 8) 26 := by
  unfold afterFrontSPos; rfl

theorem afterFrontSNeg_eq (input : Word) :
    afterFrontSNeg input = runN (prepMachine input 1 8) 40 := by
  unfold afterFrontSNeg; rfl

theorem signed_nonneg_steps_le (front n : Nat) (hn : n < 65536) (hf : front ≤ 30) :
    front + placeAllSteps n + unsignedTail n ≤ 1363 := by
  have h1 := placeAllSteps_le_of_word n hn
  have h2 := unsignedTail_le n
  omega

/-- Zero arrival, transported along `input = 0` without unfolding `runN`. -/
theorem signed_zero_at_digits_of_eq (input : Word) (h : input = 0) :
    atDigitsDefault (afterFrontSZero input) ∧
    (afterFrontSZero input).mem.get 19 = 0 ∧
    (afterFrontSZero input).mem.get 17 = 0 := by
  have hat := signed_zero_at_digits_default
  have heq : afterFrontSZero input = runN (prepMachine 0 1 8) 30 := by
    rw [afterFrontSZero_eq, h]
  rw [heq]
  exact hat

theorem signed_prep_zero (n : Int16) (hz : n.toInt = 0) :
    (runN (prepS (bitsOf n))
      (30 + placeAllSteps (bitsOf n).toNat +
        unsignedTail (bitsOf n).toNat)).pc = 32768 ∧
    (runN (prepS (bitsOf n))
      (30 + placeAllSteps (bitsOf n).toNat +
        unsignedTail (bitsOf n).toNat)).halted = true ∧
    (machineBuf (runN (prepS (bitsOf n))
      (30 + placeAllSteps (bitsOf n).toNat +
        unsignedTail (bitsOf n).toNat)) 8).map UInt16.toNat =
      (formatSpec n).1 ∧
    (machineLen (runN (prepS (bitsOf n))
      (30 + placeAllSteps (bitsOf n).toNat +
        unsignedTail (bitsOf n).toNat))).toNat =
      (formatSpec n).2 ∧
    30 + placeAllSteps (bitsOf n).toNat +
      unsignedTail (bitsOf n).toNat ≤ 1363 := by
  have hbits : bitsOf n = 0 := by rw [bitsOf_eq]; exact int16_zero_bits n hz
  have hnn : ¬ n.toInt < 0 := by omega
  have hat := signed_zero_at_digits_of_eq (bitsOf n) hbits
  have hatD : atDigitsDefault (afterFrontSZero (bitsOf n)) := hat.1
  have hatS : (afterFrontSZero (bitsOf n)).mem.get 19 = 0 := hat.2.1
  have hN : (afterFrontSZero (bitsOf n)).mem.get 17 = 0 := hat.2.2
  have hn17 : ((afterFrontSZero (bitsOf n)).mem.get 17).toNat = (bitsOf n).toNat := by
    rw [hN, hbits]
  have hkle :=
    signed_nonneg_steps_le 30 (bitsOf n).toNat (UInt16.toNat_lt_size (bitsOf n)) (by decide)
  have hsplit (t : Nat) :
      runN (prepS (bitsOf n)) (30 + placeAllSteps (bitsOf n).toNat + t) =
        runN (afterFrontSZero (bitsOf n)) (placeAllSteps (bitsOf n).toNat + t) := by
    rw [prepS_eq, afterFrontSZero_eq]
    have has : 30 + placeAllSteps (bitsOf n).toNat + t =
        30 + (placeAllSteps (bitsOf n).toNat + t) := by omega
    rw [has]
    exact runN_add (prepMachine (bitsOf n) 1 8) 30 (placeAllSteps (bitsOf n).toNat + t)
  have hshift (t : Nat) :
      placeAllSteps ((afterFrontSZero (bitsOf n)).mem.get 17).toNat + t =
        placeAllSteps (bitsOf n).toNat + t := by rw [hn17]
  have h1 : (bitsOf n).toNat < 10 := by rw [hbits]; decide
  have ht : unsignedTail (bitsOf n).toNat = 337 := by unfold unsignedTail; simp [h1]
  have hnlo : ((afterFrontSZero (bitsOf n)).mem.get 17).toNat < 10 := by
    rw [hn17]; exact h1
  have hd := unsigned_digits_ndig1_done (s := afterFrontSZero (bitsOf n)) hatD hatS hnlo
  have hsD :
      runN (prepS (bitsOf n)) (30 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat) =
        runN (afterFrontSZero (bitsOf n))
          (placeAllSteps ((afterFrontSZero (bitsOf n)).mem.get 17).toNat + 337) := by
    rw [ht, hsplit 337, ← hshift 337]
  have hpay0 := formatPayload_nonneg n hnn
  have hnt : n.toInt.toNat = (bitsOf n).toNat := by rw [hz, hbits]; rfl
  have hpay := payload_u_1 h1
  have hspec1 : (formatSpec n).1 = (snprintfSpec [48 + (bitsOf n).toNat] 8).1 := by
    unfold formatSpec; rw [hpay0, hnt, hpay]
  have hspec2 : (formatSpec n).2 = 1 := by
    unfold formatSpec; rw [hpay0, hnt, hpay, snprintf_length]; rfl
  refine ⟨?_, ?_, ?_, ?_, hkle⟩
  · rw [hsD]; exact hd.1
  · rw [hsD]; exact hd.2.1
  · rw [hsD, hd.2.2.1, hspec1, hn17]
  · rw [hsD, hd.2.2.2, hspec2]

theorem signed_prep_pos (n : Int16) (hpos : 0 < n.toInt) :
    (runN (prepS (bitsOf n))
      (26 + placeAllSteps (bitsOf n).toNat +
        unsignedTail (bitsOf n).toNat)).pc = 32768 ∧
    (runN (prepS (bitsOf n))
      (26 + placeAllSteps (bitsOf n).toNat +
        unsignedTail (bitsOf n).toNat)).halted = true ∧
    (machineBuf (runN (prepS (bitsOf n))
      (26 + placeAllSteps (bitsOf n).toNat +
        unsignedTail (bitsOf n).toNat)) 8).map UInt16.toNat =
      (formatSpec n).1 ∧
    (machineLen (runN (prepS (bitsOf n))
      (26 + placeAllSteps (bitsOf n).toNat +
        unsignedTail (bitsOf n).toNat))).toNat =
      (formatSpec n).2 ∧
    26 + placeAllSteps (bitsOf n).toNat +
      unsignedTail (bitsOf n).toNat ≤ 1363 := by
  have hb := int16_pos_bits n hpos
  have hposW : 0 < (bitsOf n).toNat := by rw [bitsOf_eq]; exact hb.1
  have hhi : (bitsOf n).toNat < 32768 := by rw [bitsOf_eq]; exact hb.2.1
  have hnt : n.toInt.toNat = (bitsOf n).toNat := by rw [bitsOf_eq]; exact hb.2.2.symm
  have hnn : ¬ n.toInt < 0 := by omega
  have hat0 := signed_pos_at_digits_default (bitsOf n) hposW hhi
  have hatD : atDigitsDefault (afterFrontSPos (bitsOf n)) := by
    rw [afterFrontSPos_eq]; exact hat0.1
  have hatS : (afterFrontSPos (bitsOf n)).mem.get 19 = 0 := by
    rw [afterFrontSPos_eq]; exact hat0.2.1
  have hN : (afterFrontSPos (bitsOf n)).mem.get 17 = bitsOf n := by
    rw [afterFrontSPos_eq]; exact hat0.2.2
  have hn17 : ((afterFrontSPos (bitsOf n)).mem.get 17).toNat = (bitsOf n).toNat := by
    rw [hN]
  have hkle :=
    signed_nonneg_steps_le 26 (bitsOf n).toNat (UInt16.toNat_lt_size (bitsOf n)) (by decide)
  have hsplit (t : Nat) :
      runN (prepS (bitsOf n)) (26 + placeAllSteps (bitsOf n).toNat + t) =
        runN (afterFrontSPos (bitsOf n)) (placeAllSteps (bitsOf n).toNat + t) := by
    rw [prepS_eq, afterFrontSPos_eq]
    have has : 26 + placeAllSteps (bitsOf n).toNat + t =
        26 + (placeAllSteps (bitsOf n).toNat + t) := by omega
    rw [has]
    exact runN_add (prepMachine (bitsOf n) 1 8) 26 (placeAllSteps (bitsOf n).toNat + t)
  have hshift (t : Nat) :
      placeAllSteps ((afterFrontSPos (bitsOf n)).mem.get 17).toNat + t =
        placeAllSteps (bitsOf n).toNat + t := by rw [hn17]
  have hpay0 := formatPayload_nonneg n hnn
  by_cases h1 : (bitsOf n).toNat < 10
  · have ht : unsignedTail (bitsOf n).toNat = 337 := by unfold unsignedTail; simp [h1]
    have hnlo : ((afterFrontSPos (bitsOf n)).mem.get 17).toNat < 10 := by
      rw [hn17]; exact h1
    have hd := unsigned_digits_ndig1_done (s := afterFrontSPos (bitsOf n)) hatD hatS hnlo
    have hsD :
        runN (prepS (bitsOf n)) (26 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat) =
          runN (afterFrontSPos (bitsOf n))
            (placeAllSteps ((afterFrontSPos (bitsOf n)).mem.get 17).toNat + 337) := by
      rw [ht, hsplit 337, ← hshift 337]
    have hpay := payload_u_1 h1
    have hspec1 : (formatSpec n).1 = (snprintfSpec [48 + (bitsOf n).toNat] 8).1 := by
      unfold formatSpec; rw [hpay0, hnt, hpay]
    have hspec2 : (formatSpec n).2 = 1 := by
      unfold formatSpec; rw [hpay0, hnt, hpay, snprintf_length]; rfl
    refine ⟨?_, ?_, ?_, ?_, hkle⟩
    · rw [hsD]; exact hd.1
    · rw [hsD]; exact hd.2.1
    · rw [hsD, hd.2.2.1, hspec1, hn17]
    · rw [hsD, hd.2.2.2, hspec2]
  · by_cases h2 : (bitsOf n).toNat < 100
    · have ht : unsignedTail (bitsOf n).toNat = 405 := by unfold unsignedTail; simp [h1, h2]
      have hlo : 10 ≤ ((afterFrontSPos (bitsOf n)).mem.get 17).toNat := by
        rw [hn17]; exact Nat.le_of_not_lt h1
      have hhi' : ((afterFrontSPos (bitsOf n)).mem.get 17).toNat < 100 := by
        rw [hn17]; exact h2
      have hd := unsigned_digits_ndig2_done (s := afterFrontSPos (bitsOf n)) hatD hatS hlo hhi'
      have hsD :
          runN (prepS (bitsOf n)) (26 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat) =
            runN (afterFrontSPos (bitsOf n))
              (placeAllSteps ((afterFrontSPos (bitsOf n)).mem.get 17).toNat + 405) := by
        rw [ht, hsplit 405, ← hshift 405]
      have hpay := payload_u_2 (Nat.le_of_not_lt h1) h2
      have hspec1 : (formatSpec n).1 =
          (snprintfSpec [48 + (bitsOf n).toNat / 10, 48 + (bitsOf n).toNat % 10] 8).1 := by
        unfold formatSpec; rw [hpay0, hnt, hpay]
      have hspec2 : (formatSpec n).2 = 2 := by
        unfold formatSpec; rw [hpay0, hnt, hpay, snprintf_length]; rfl
      refine ⟨?_, ?_, ?_, ?_, hkle⟩
      · rw [hsD]; exact hd.1
      · rw [hsD]; exact hd.2.1
      · rw [hsD, hd.2.2.1, hspec1, hn17]
      · rw [hsD, hd.2.2.2, hspec2]
    · by_cases h3 : (bitsOf n).toNat < 1000
      · have ht : unsignedTail (bitsOf n).toNat = 462 := by
          unfold unsignedTail; simp [h1, h2, h3]
        have hlo : 100 ≤ ((afterFrontSPos (bitsOf n)).mem.get 17).toNat := by
          rw [hn17]; exact Nat.le_of_not_lt h2
        have hhi' : ((afterFrontSPos (bitsOf n)).mem.get 17).toNat < 1000 := by
          rw [hn17]; exact h3
        have hd := unsigned_digits_ndig3_done (s := afterFrontSPos (bitsOf n)) hatD hatS hlo hhi'
        have hsD :
            runN (prepS (bitsOf n)) (26 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat) =
              runN (afterFrontSPos (bitsOf n))
                (placeAllSteps ((afterFrontSPos (bitsOf n)).mem.get 17).toNat + 462) := by
          rw [ht, hsplit 462, ← hshift 462]
        have hpay := payload_u_3 (Nat.le_of_not_lt h2) h3
        have hspec1 : (formatSpec n).1 =
            (snprintfSpec [48 + (bitsOf n).toNat / 100, 48 + (bitsOf n).toNat / 10 % 10,
              48 + (bitsOf n).toNat % 10] 8).1 := by
          unfold formatSpec; rw [hpay0, hnt, hpay]
        have hspec2 : (formatSpec n).2 = 3 := by
          unfold formatSpec; rw [hpay0, hnt, hpay, snprintf_length]; rfl
        refine ⟨?_, ?_, ?_, ?_, hkle⟩
        · rw [hsD]; exact hd.1
        · rw [hsD]; exact hd.2.1
        · rw [hsD, hd.2.2.1, hspec1, hn17]
        · rw [hsD, hd.2.2.2, hspec2]
      · by_cases h4 : (bitsOf n).toNat < 10000
        · have ht : unsignedTail (bitsOf n).toNat = 519 := by
            unfold unsignedTail; simp [h1, h2, h3, h4]
          have hlo : 1000 ≤ ((afterFrontSPos (bitsOf n)).mem.get 17).toNat := by
            rw [hn17]; exact Nat.le_of_not_lt h3
          have hhi' : ((afterFrontSPos (bitsOf n)).mem.get 17).toNat < 10000 := by
            rw [hn17]; exact h4
          have hd := unsigned_digits_ndig4_done (s := afterFrontSPos (bitsOf n)) hatD hatS hlo hhi'
          have hsD :
              runN (prepS (bitsOf n)) (26 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat) =
                runN (afterFrontSPos (bitsOf n))
                  (placeAllSteps ((afterFrontSPos (bitsOf n)).mem.get 17).toNat + 519) := by
            rw [ht, hsplit 519, ← hshift 519]
          have hpay := payload_u_4 (Nat.le_of_not_lt h3) h4
          have hspec1 : (formatSpec n).1 =
              (snprintfSpec [48 + (bitsOf n).toNat / 1000, 48 + (bitsOf n).toNat / 100 % 10,
                48 + (bitsOf n).toNat / 10 % 10, 48 + (bitsOf n).toNat % 10] 8).1 := by
            unfold formatSpec; rw [hpay0, hnt, hpay]
          have hspec2 : (formatSpec n).2 = 4 := by
            unfold formatSpec; rw [hpay0, hnt, hpay, snprintf_length]; rfl
          refine ⟨?_, ?_, ?_, ?_, hkle⟩
          · rw [hsD]; exact hd.1
          · rw [hsD]; exact hd.2.1
          · rw [hsD, hd.2.2.1, hspec1, hn17]
          · rw [hsD, hd.2.2.2, hspec2]
        · have ht : unsignedTail (bitsOf n).toNat = 576 := by
            unfold unsignedTail; simp [h1, h2, h3, h4]
          have hhiN : (bitsOf n).toNat < 100000 :=
            Nat.lt_trans (UInt16.toNat_lt_size (bitsOf n)) (by decide)
          have hlo : 10000 ≤ ((afterFrontSPos (bitsOf n)).mem.get 17).toNat := by
            rw [hn17]; exact Nat.le_of_not_lt h4
          have hhi' : ((afterFrontSPos (bitsOf n)).mem.get 17).toNat < 100000 := by
            rw [hn17]; exact hhiN
          have hd := unsigned_digits_ndig5_done (s := afterFrontSPos (bitsOf n)) hatD hatS hlo hhi'
          have hsD :
              runN (prepS (bitsOf n)) (26 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat) =
                runN (afterFrontSPos (bitsOf n))
                  (placeAllSteps ((afterFrontSPos (bitsOf n)).mem.get 17).toNat + 576) := by
            rw [ht, hsplit 576, ← hshift 576]
          have hpay := payload_u_5 (Nat.le_of_not_lt h4) hhiN
          have hspec1 : (formatSpec n).1 =
              (snprintfSpec [48 + (bitsOf n).toNat / 10000, 48 + (bitsOf n).toNat / 1000 % 10,
                48 + (bitsOf n).toNat / 100 % 10, 48 + (bitsOf n).toNat / 10 % 10,
                48 + (bitsOf n).toNat % 10] 8).1 := by
            unfold formatSpec; rw [hpay0, hnt, hpay]
          have hspec2 : (formatSpec n).2 = 5 := by
            unfold formatSpec; rw [hpay0, hnt, hpay, snprintf_length]; rfl
          refine ⟨?_, ?_, ?_, ?_, hkle⟩
          · rw [hsD]; exact hd.1
          · rw [hsD]; exact hd.2.1
          · rw [hsD, hd.2.2.1, hspec1, hn17]
          · rw [hsD, hd.2.2.2, hspec2]

/-- Magnitude of a negative signed input after the front-end negation. -/
def magOf (n : Int16) : Nat := (0 - bitsOf n).toNat

theorem signed_prep_neg (n : Int16) (hneg : n.toInt < 0) :
    (runN (prepS (bitsOf n))
      (40 + placeAllSteps (magOf n) + signedTail (magOf n))).pc = 32768 ∧
    (runN (prepS (bitsOf n))
      (40 + placeAllSteps (magOf n) + signedTail (magOf n))).halted = true ∧
    (machineBuf (runN (prepS (bitsOf n))
      (40 + placeAllSteps (magOf n) + signedTail (magOf n))) 8).map UInt16.toNat =
      (formatSpec n).1 ∧
    (machineLen (runN (prepS (bitsOf n))
      (40 + placeAllSteps (magOf n) + signedTail (magOf n)))).toNat =
      (formatSpec n).2 ∧
    40 + placeAllSteps (magOf n) + signedTail (magOf n) ≤ 1433 := by
  have hnegW : 32768 ≤ (bitsOf n).toNat := by
    rw [bitsOf_eq]; exact int16_neg_bits n hneg
  have hmag : magOf n = n.toInt.natAbs := by
    unfold magOf; rw [bitsOf_eq]; exact int16_neg_mag n hneg
  have hat0 := signed_neg_at_digits_default (bitsOf n) hnegW
  have hatD : atDigitsDefault (afterFrontSNeg (bitsOf n)) := by
    rw [afterFrontSNeg_eq]; exact hat0.1
  have hS : (afterFrontSNeg (bitsOf n)).mem.get 19 = 1 := by
    rw [afterFrontSNeg_eq]; exact hat0.2.1
  have hN : (afterFrontSNeg (bitsOf n)).mem.get 17 = 0 - bitsOf n := by
    rw [afterFrontSNeg_eq]; exact hat0.2.2
  have hn17 : ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat = magOf n := by
    rw [hN]; rfl
  have hSlo : 0 < ((afterFrontSNeg (bitsOf n)).mem.get 19).toNat := by
    rw [hS]; decide
  have hShi : ((afterFrontSNeg (bitsOf n)).mem.get 19).toNat < 32768 := by
    rw [hS]; decide
  have hkle :=
    signed_steps_le 40 (magOf n) (UInt16.toNat_lt_size (0 - bitsOf n)) (by decide)
  have hsplit (t : Nat) :
      runN (prepS (bitsOf n)) (40 + placeAllSteps (magOf n) + t) =
        runN (afterFrontSNeg (bitsOf n)) (placeAllSteps (magOf n) + t) := by
    rw [prepS_eq, afterFrontSNeg_eq]
    have has : 40 + placeAllSteps (magOf n) + t =
        40 + (placeAllSteps (magOf n) + t) := by omega
    rw [has]
    exact runN_add (prepMachine (bitsOf n) 1 8) 40 (placeAllSteps (magOf n) + t)
  have hshift (t : Nat) :
      placeAllSteps ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat + t =
        placeAllSteps (magOf n) + t := by rw [hn17]
  have hpay0 := formatPayload_neg n hneg
  by_cases h1 : magOf n < 10
  · have ht : signedTail (magOf n) = 389 := by unfold signedTail; simp [h1]
    have hnlo : ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat < 10 := by
      rw [hn17]; exact h1
    have hd := signed_digits_ndig1_done (s := afterFrontSNeg (bitsOf n)) hatD hSlo hShi hnlo
    have hsD :
        runN (prepS (bitsOf n)) (40 + placeAllSteps (magOf n) + signedTail (magOf n)) =
          runN (afterFrontSNeg (bitsOf n))
            (placeAllSteps ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat + 389) := by
      rw [ht, hsplit 389, ← hshift 389]
    have hpay := payload_u_1 h1
    have hspec1 : (formatSpec n).1 = (snprintfSpec [45, 48 + magOf n] 8).1 := by
      unfold formatSpec; rw [hpay0, hmag.symm, hpay]
    have hspec2 : (formatSpec n).2 = 2 := by
      unfold formatSpec; rw [hpay0, hmag.symm, hpay, snprintf_length]; rfl
    refine ⟨?_, ?_, ?_, ?_, hkle⟩
    · rw [hsD]; exact hd.1
    · rw [hsD]; exact hd.2.1
    · rw [hsD, hd.2.2.1, hspec1, hn17]
    · rw [hsD, hd.2.2.2, hspec2]
  · by_cases h2 : magOf n < 100
    · have ht : signedTail (magOf n) = 459 := by unfold signedTail; simp [h1, h2]
      have hlo : 10 ≤ ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat := by
        rw [hn17]; exact Nat.le_of_not_lt h1
      have hhi' : ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat < 100 := by
        rw [hn17]; exact h2
      have hd := signed_digits_ndig2_done (s := afterFrontSNeg (bitsOf n)) hatD hSlo hShi hlo hhi'
      have hsD :
          runN (prepS (bitsOf n)) (40 + placeAllSteps (magOf n) + signedTail (magOf n)) =
            runN (afterFrontSNeg (bitsOf n))
              (placeAllSteps ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat + 459) := by
        rw [ht, hsplit 459, ← hshift 459]
      have hpay := payload_u_2 (Nat.le_of_not_lt h1) h2
      have hspec1 : (formatSpec n).1 =
          (snprintfSpec [45, 48 + magOf n / 10, 48 + magOf n % 10] 8).1 := by
        unfold formatSpec; rw [hpay0, hmag.symm, hpay]
      have hspec2 : (formatSpec n).2 = 3 := by
        unfold formatSpec; rw [hpay0, hmag.symm, hpay, snprintf_length]; rfl
      refine ⟨?_, ?_, ?_, ?_, hkle⟩
      · rw [hsD]; exact hd.1
      · rw [hsD]; exact hd.2.1
      · rw [hsD, hd.2.2.1, hspec1, hn17]
      · rw [hsD, hd.2.2.2, hspec2]
    · by_cases h3 : magOf n < 1000
      · have ht : signedTail (magOf n) = 518 := by unfold signedTail; simp [h1, h2, h3]
        have hlo : 100 ≤ ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat := by
          rw [hn17]; exact Nat.le_of_not_lt h2
        have hhi' : ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat < 1000 := by
          rw [hn17]; exact h3
        have hd := signed_digits_ndig3_done (s := afterFrontSNeg (bitsOf n)) hatD hSlo hShi hlo hhi'
        have hsD :
            runN (prepS (bitsOf n)) (40 + placeAllSteps (magOf n) + signedTail (magOf n)) =
              runN (afterFrontSNeg (bitsOf n))
                (placeAllSteps ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat + 518) := by
          rw [ht, hsplit 518, ← hshift 518]
        have hpay := payload_u_3 (Nat.le_of_not_lt h2) h3
        have hspec1 : (formatSpec n).1 =
            (snprintfSpec [45, 48 + magOf n / 100, 48 + magOf n / 10 % 10,
              48 + magOf n % 10] 8).1 := by
          unfold formatSpec; rw [hpay0, hmag.symm, hpay]
        have hspec2 : (formatSpec n).2 = 4 := by
          unfold formatSpec; rw [hpay0, hmag.symm, hpay, snprintf_length]; rfl
        refine ⟨?_, ?_, ?_, ?_, hkle⟩
        · rw [hsD]; exact hd.1
        · rw [hsD]; exact hd.2.1
        · rw [hsD, hd.2.2.1, hspec1, hn17]
        · rw [hsD, hd.2.2.2, hspec2]
      · by_cases h4 : magOf n < 10000
        · have ht : signedTail (magOf n) = 577 := by
            unfold signedTail; simp [h1, h2, h3, h4]
          have hlo : 1000 ≤ ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat := by
            rw [hn17]; exact Nat.le_of_not_lt h3
          have hhi' : ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat < 10000 := by
            rw [hn17]; exact h4
          have hd := signed_digits_ndig4_done (s := afterFrontSNeg (bitsOf n)) hatD hSlo hShi hlo hhi'
          have hsD :
              runN (prepS (bitsOf n)) (40 + placeAllSteps (magOf n) + signedTail (magOf n)) =
                runN (afterFrontSNeg (bitsOf n))
                  (placeAllSteps ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat + 577) := by
            rw [ht, hsplit 577, ← hshift 577]
          have hpay := payload_u_4 (Nat.le_of_not_lt h3) h4
          have hspec1 : (formatSpec n).1 =
              (snprintfSpec [45, 48 + magOf n / 1000, 48 + magOf n / 100 % 10,
                48 + magOf n / 10 % 10, 48 + magOf n % 10] 8).1 := by
            unfold formatSpec; rw [hpay0, hmag.symm, hpay]
          have hspec2 : (formatSpec n).2 = 5 := by
            unfold formatSpec; rw [hpay0, hmag.symm, hpay, snprintf_length]; rfl
          refine ⟨?_, ?_, ?_, ?_, hkle⟩
          · rw [hsD]; exact hd.1
          · rw [hsD]; exact hd.2.1
          · rw [hsD, hd.2.2.1, hspec1, hn17]
          · rw [hsD, hd.2.2.2, hspec2]
        · have ht : signedTail (magOf n) = 636 := by
            unfold signedTail; simp [h1, h2, h3, h4]
          have hhiN : magOf n < 100000 :=
            Nat.lt_trans (UInt16.toNat_lt_size (0 - bitsOf n)) (by decide)
          have hlo : 10000 ≤ ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat := by
            rw [hn17]; exact Nat.le_of_not_lt h4
          have hhi' : ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat < 100000 := by
            rw [hn17]; exact hhiN
          have hd := signed_digits_ndig5_done (s := afterFrontSNeg (bitsOf n)) hatD hSlo hShi hlo hhi'
          have hsD :
              runN (prepS (bitsOf n)) (40 + placeAllSteps (magOf n) + signedTail (magOf n)) =
                runN (afterFrontSNeg (bitsOf n))
                  (placeAllSteps ((afterFrontSNeg (bitsOf n)).mem.get 17).toNat + 636) := by
            rw [ht, hsplit 636, ← hshift 636]
          have hpay := payload_u_5 (Nat.le_of_not_lt h4) hhiN
          have hspec1 : (formatSpec n).1 =
              (snprintfSpec [45, 48 + magOf n / 10000, 48 + magOf n / 1000 % 10,
                48 + magOf n / 100 % 10, 48 + magOf n / 10 % 10,
                48 + magOf n % 10] 8).1 := by
            unfold formatSpec; rw [hpay0, hmag.symm, hpay]
          have hspec2 : (formatSpec n).2 = 6 := by
            unfold formatSpec; rw [hpay0, hmag.symm, hpay, snprintf_length]; rfl
          refine ⟨?_, ?_, ?_, ?_, hkle⟩
          · rw [hsD]; exact hd.1
          · rw [hsD]; exact hd.2.1
          · rw [hsD, hd.2.2.1, hspec1, hn17]
          · rw [hsD, hd.2.2.2, hspec2]

/-- Signed-mode end-to-end theorem at default `CAP = 8`, `WIDTH = 0`.
The prepared machine is `loadIntfmtDec n` (`MODE = 1`). Output is the
8-cell `BUF` together with `LEN`, equal to `formatSpec n`. The default
call path has `WIDTH = 0`, so this theorem does not claim general
padding. The proved per-input step bound is at most 1433 (negative
max-case), hence a fuel of 2000 suffices. -/
theorem intfmt_signed_e2e (n : Int16) :
    (runCounted (prepS (bitsOf n)) 2000).kind = HaltKind.programHalt ∧
    (runCounted (prepS (bitsOf n)) 2000).steps ≤ 2000 ∧
    (runCounted (prepS (bitsOf n)) 2000).state.halted = true ∧
    (machineBuf (runCounted (prepS (bitsOf n)) 2000).state 8).map UInt16.toNat =
      (formatSpec n).1 ∧
    (machineLen (runCounted (prepS (bitsOf n)) 2000).state).toNat =
      (formatSpec n).2 := by
  by_cases hneg : n.toInt < 0
  · have hd := signed_prep_neg n hneg
    have hkle : 40 + placeAllSteps (magOf n) + signedTail (magOf n) ≤ 1433 := hd.2.2.2.2
    have hfuel : 40 + placeAllSteps (magOf n) + signedTail (magOf n) ≤ 2000 :=
      Nat.le_trans hkle (by decide)
    have hhalt :
        (runN (prepS (bitsOf n)) (40 + placeAllSteps (magOf n) + signedTail (magOf n))).halted = true ∨
          32768 ≤ (runN (prepS (bitsOf n)) (40 + placeAllSteps (magOf n) + signedTail (magOf n))).pc.toNat :=
      Or.inl hd.2.1
    have ⟨hkind, hsteps, hh, hm⟩ :=
      runCounted_programHalt_of_runN (prepS (bitsOf n))
        (40 + placeAllSteps (magOf n) + signedTail (magOf n)) 2000 hfuel hhalt
    refine ⟨hkind, Nat.le_trans hsteps hfuel, hh, ?_, ?_⟩
    · have hc := machineBuf_congr hm
      rw [hc]
      exact hd.2.2.1
    · have hc := machineLen_congr (hm 16)
      rw [hc]
      exact hd.2.2.2.1
  · by_cases hz : n.toInt = 0
    · have hd := signed_prep_zero n hz
      have hkle : 30 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat ≤ 1363 :=
        hd.2.2.2.2
      have hfuel : 30 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat ≤ 2000 :=
        Nat.le_trans hkle (by decide)
      have hhalt :
          (runN (prepS (bitsOf n))
            (30 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat)).halted = true ∨
            32768 ≤ (runN (prepS (bitsOf n))
              (30 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat)).pc.toNat :=
        Or.inl hd.2.1
      have ⟨hkind, hsteps, hh, hm⟩ :=
        runCounted_programHalt_of_runN (prepS (bitsOf n))
          (30 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat) 2000 hfuel hhalt
      refine ⟨hkind, Nat.le_trans hsteps hfuel, hh, ?_, ?_⟩
      · have hc := machineBuf_congr hm
        rw [hc]
        exact hd.2.2.1
      · have hc := machineLen_congr (hm 16)
        rw [hc]
        exact hd.2.2.2.1
    · have hpos : 0 < n.toInt := by omega
      have hd := signed_prep_pos n hpos
      have hkle : 26 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat ≤ 1363 :=
        hd.2.2.2.2
      have hfuel : 26 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat ≤ 2000 :=
        Nat.le_trans hkle (by decide)
      have hhalt :
          (runN (prepS (bitsOf n))
            (26 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat)).halted = true ∨
            32768 ≤ (runN (prepS (bitsOf n))
              (26 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat)).pc.toNat :=
        Or.inl hd.2.1
      have ⟨hkind, hsteps, hh, hm⟩ :=
        runCounted_programHalt_of_runN (prepS (bitsOf n))
          (26 + placeAllSteps (bitsOf n).toNat + unsignedTail (bitsOf n).toNat) 2000 hfuel hhalt
      refine ⟨hkind, Nat.le_trans hsteps hfuel, hh, ?_, ?_⟩
      · have hc := machineBuf_congr hm
        rw [hc]
        exact hd.2.2.1
      · have hc := machineLen_congr (hm 16)
        rw [hc]
        exact hd.2.2.2.1

/-- Same statement, written on `loadIntfmtDec n` (`prepMachine` of the
bit-pattern, signed mode, capacity 8). -/
theorem intfmt_signed_e2e_load (n : Int16) :
    (runCounted (loadIntfmtDec n) 2000).kind = HaltKind.programHalt ∧
    (runCounted (loadIntfmtDec n) 2000).steps ≤ 2000 ∧
    (runCounted (loadIntfmtDec n) 2000).state.halted = true ∧
    (machineBuf (runCounted (loadIntfmtDec n) 2000).state 8).map UInt16.toNat =
      (formatSpec n).1 ∧
    (machineLen (runCounted (loadIntfmtDec n) 2000).state).toNat =
      (formatSpec n).2 := by
  have h := intfmt_signed_e2e n
  rw [loadIntfmtDec_eq_prepS]
  exact h


end IntFmt
