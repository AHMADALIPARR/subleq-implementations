/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Front-to-halt compositions and end-to-end theorems at default
`CAP = 8`, `WIDTH = 0`. Output is the 8-cell `BUF` together with `LEN`.
-/

import IntFmt.EndToEnd

namespace IntFmt

open Subleq

set_option maxHeartbeats 4000000

theorem machineBuf_congr {s t : Machine}
    (h : ∀ a, s.mem.get a = t.mem.get a) :
    machineBuf s 8 = machineBuf t 8 := by
  rw [machineBuf_eight s, machineBuf_eight t]
  simp [h 32, h 33, h 34, h 35, h 36, h 37, h 38, h 39]

theorem machineLen_congr {s t : Machine}
    (h : s.mem.get 16 = t.mem.get 16) :
    machineLen s = machineLen t := by
  simp [machineLen, addrLen, h]

@[irreducible] def prepU (input : Word) : Machine :=
  prepMachine input 0 8

@[irreducible] def afterFrontU (input : Word) : Machine :=
  runN (prepMachine input 0 8) 15

theorem prepU_eq (input : Word) : prepU input = prepMachine input 0 8 := by
  unfold prepU; rfl

theorem afterFrontU_eq (input : Word) :
    afterFrontU input = runN (prepMachine input 0 8) 15 := by
  unfold afterFrontU; rfl

theorem unsigned_prep_done (input : Word) :
    (runN (prepU input) (15 + placeAllSteps input.toNat + unsignedTail input.toNat)).pc = 32768 ∧
    (runN (prepU input) (15 + placeAllSteps input.toNat + unsignedTail input.toNat)).halted = true ∧
    (machineBuf (runN (prepU input) (15 + placeAllSteps input.toNat + unsignedTail input.toNat)) 8).map UInt16.toNat =
      (formatSpecUnsigned input).1 ∧
    (machineLen (runN (prepU input) (15 + placeAllSteps input.toNat + unsignedTail input.toNat))).toNat =
      (formatSpecUnsigned input).2 ∧
    15 + placeAllSteps input.toNat + unsignedTail input.toNat ≤ 1348 := by
  have hat := unsigned_at_digits_default input
  have hN : (afterFrontU input).mem.get 17 = input := by
    rw [afterFrontU_eq]; exact hat.2.2
  have hn17 : ((afterFrontU input).mem.get 17).toNat = input.toNat := by rw [hN]
  have hatD : atDigitsDefault (afterFrontU input) := by
    rw [afterFrontU_eq]; exact hat.1
  have hatS : (afterFrontU input).mem.get 19 = 0 := by
    rw [afterFrontU_eq]; exact hat.2.1
  have hkle := unsigned_steps_le input.toNat (UInt16.toNat_lt_size input)
  have hsplit (t : Nat) :
      runN (prepU input) (15 + placeAllSteps input.toNat + t) =
        runN (afterFrontU input) (placeAllSteps input.toNat + t) := by
    rw [prepU_eq, afterFrontU_eq]
    have has : 15 + placeAllSteps input.toNat + t =
        15 + (placeAllSteps input.toNat + t) := by omega
    rw [has]
    exact runN_add (prepMachine input 0 8) 15 (placeAllSteps input.toNat + t)
  have hshift (t : Nat) :
      placeAllSteps ((afterFrontU input).mem.get 17).toNat + t =
        placeAllSteps input.toNat + t := by rw [hn17]
  by_cases h1 : input.toNat < 10
  · have ht : unsignedTail input.toNat = 337 := by unfold unsignedTail; simp [h1]
    have hnlo : ((afterFrontU input).mem.get 17).toNat < 10 := by rw [hn17]; exact h1
    have hd := unsigned_digits_ndig1_done (s := afterFrontU input) hatD hatS hnlo
    have hsD :
        runN (prepU input) (15 + placeAllSteps input.toNat + unsignedTail input.toNat) =
          runN (afterFrontU input)
            (placeAllSteps ((afterFrontU input).mem.get 17).toNat + 337) := by
      rw [ht, hsplit 337, ← hshift 337]
    have hpay := payload_u_1 h1
    have hspec1 : (formatSpecUnsigned input).1 = (snprintfSpec [48 + input.toNat] 8).1 := by
      unfold formatSpecUnsigned formatPayloadUnsigned; rw [hpay]
    have hspec2 : (formatSpecUnsigned input).2 = 1 := by
      unfold formatSpecUnsigned formatPayloadUnsigned; rw [hpay, snprintf_length]; rfl
    refine ⟨?_, ?_, ?_, ?_, hkle⟩
    · rw [hsD]; exact hd.1
    · rw [hsD]; exact hd.2.1
    · rw [hsD, hd.2.2.1, hspec1, hn17]
    · rw [hsD, hd.2.2.2, hspec2]
  · by_cases h2 : input.toNat < 100
    · have ht : unsignedTail input.toNat = 405 := by unfold unsignedTail; simp [h1, h2]
      have hlo : 10 ≤ ((afterFrontU input).mem.get 17).toNat := by rw [hn17]; exact Nat.le_of_not_lt h1
      have hhi : ((afterFrontU input).mem.get 17).toNat < 100 := by rw [hn17]; exact h2
      have hd := unsigned_digits_ndig2_done (s := afterFrontU input) hatD hatS hlo hhi
      have hsD :
          runN (prepU input) (15 + placeAllSteps input.toNat + unsignedTail input.toNat) =
            runN (afterFrontU input)
              (placeAllSteps ((afterFrontU input).mem.get 17).toNat + 405) := by
        rw [ht, hsplit 405, ← hshift 405]
      have hpay := payload_u_2 (Nat.le_of_not_lt h1) h2
      have hspec1 : (formatSpecUnsigned input).1 =
          (snprintfSpec [48 + input.toNat / 10, 48 + input.toNat % 10] 8).1 := by
        unfold formatSpecUnsigned formatPayloadUnsigned; rw [hpay]
      have hspec2 : (formatSpecUnsigned input).2 = 2 := by
        unfold formatSpecUnsigned formatPayloadUnsigned; rw [hpay, snprintf_length]; rfl
      refine ⟨?_, ?_, ?_, ?_, hkle⟩
      · rw [hsD]; exact hd.1
      · rw [hsD]; exact hd.2.1
      · rw [hsD, hd.2.2.1, hspec1, hn17]
      · rw [hsD, hd.2.2.2, hspec2]
    · by_cases h3 : input.toNat < 1000
      · have ht : unsignedTail input.toNat = 462 := by unfold unsignedTail; simp [h1, h2, h3]
        have hlo : 100 ≤ ((afterFrontU input).mem.get 17).toNat := by rw [hn17]; exact Nat.le_of_not_lt h2
        have hhi : ((afterFrontU input).mem.get 17).toNat < 1000 := by rw [hn17]; exact h3
        have hd := unsigned_digits_ndig3_done (s := afterFrontU input) hatD hatS hlo hhi
        have hsD :
            runN (prepU input) (15 + placeAllSteps input.toNat + unsignedTail input.toNat) =
              runN (afterFrontU input)
                (placeAllSteps ((afterFrontU input).mem.get 17).toNat + 462) := by
          rw [ht, hsplit 462, ← hshift 462]
        have hpay := payload_u_3 (Nat.le_of_not_lt h2) h3
        have hspec1 : (formatSpecUnsigned input).1 =
            (snprintfSpec [48 + input.toNat / 100, 48 + input.toNat / 10 % 10,
              48 + input.toNat % 10] 8).1 := by
          unfold formatSpecUnsigned formatPayloadUnsigned; rw [hpay]
        have hspec2 : (formatSpecUnsigned input).2 = 3 := by
          unfold formatSpecUnsigned formatPayloadUnsigned; rw [hpay, snprintf_length]; rfl
        refine ⟨?_, ?_, ?_, ?_, hkle⟩
        · rw [hsD]; exact hd.1
        · rw [hsD]; exact hd.2.1
        · rw [hsD, hd.2.2.1, hspec1, hn17]
        · rw [hsD, hd.2.2.2, hspec2]
      · by_cases h4 : input.toNat < 10000
        · have ht : unsignedTail input.toNat = 519 := by unfold unsignedTail; simp [h1, h2, h3, h4]
          have hlo : 1000 ≤ ((afterFrontU input).mem.get 17).toNat := by rw [hn17]; exact Nat.le_of_not_lt h3
          have hhi : ((afterFrontU input).mem.get 17).toNat < 10000 := by rw [hn17]; exact h4
          have hd := unsigned_digits_ndig4_done (s := afterFrontU input) hatD hatS hlo hhi
          have hsD :
              runN (prepU input) (15 + placeAllSteps input.toNat + unsignedTail input.toNat) =
                runN (afterFrontU input)
                  (placeAllSteps ((afterFrontU input).mem.get 17).toNat + 519) := by
            rw [ht, hsplit 519, ← hshift 519]
          have hpay := payload_u_4 (Nat.le_of_not_lt h3) h4
          have hspec1 : (formatSpecUnsigned input).1 =
              (snprintfSpec [48 + input.toNat / 1000, 48 + input.toNat / 100 % 10,
                48 + input.toNat / 10 % 10, 48 + input.toNat % 10] 8).1 := by
            unfold formatSpecUnsigned formatPayloadUnsigned; rw [hpay]
          have hspec2 : (formatSpecUnsigned input).2 = 4 := by
            unfold formatSpecUnsigned formatPayloadUnsigned; rw [hpay, snprintf_length]; rfl
          refine ⟨?_, ?_, ?_, ?_, hkle⟩
          · rw [hsD]; exact hd.1
          · rw [hsD]; exact hd.2.1
          · rw [hsD, hd.2.2.1, hspec1, hn17]
          · rw [hsD, hd.2.2.2, hspec2]
        · have ht : unsignedTail input.toNat = 576 := by unfold unsignedTail; simp [h1, h2, h3, h4]
          have hhiN : input.toNat < 100000 :=
            Nat.lt_trans (UInt16.toNat_lt_size input) (by decide)
          have hlo : 10000 ≤ ((afterFrontU input).mem.get 17).toNat := by rw [hn17]; exact Nat.le_of_not_lt h4
          have hhi : ((afterFrontU input).mem.get 17).toNat < 100000 := by rw [hn17]; exact hhiN
          have hd := unsigned_digits_ndig5_done (s := afterFrontU input) hatD hatS hlo hhi
          have hsD :
              runN (prepU input) (15 + placeAllSteps input.toNat + unsignedTail input.toNat) =
                runN (afterFrontU input)
                  (placeAllSteps ((afterFrontU input).mem.get 17).toNat + 576) := by
            rw [ht, hsplit 576, ← hshift 576]
          have hpay := payload_u_5 (Nat.le_of_not_lt h4) hhiN
          have hspec1 : (formatSpecUnsigned input).1 =
              (snprintfSpec [48 + input.toNat / 10000, 48 + input.toNat / 1000 % 10,
                48 + input.toNat / 100 % 10, 48 + input.toNat / 10 % 10,
                48 + input.toNat % 10] 8).1 := by
            unfold formatSpecUnsigned formatPayloadUnsigned; rw [hpay]
          have hspec2 : (formatSpecUnsigned input).2 = 5 := by
            unfold formatSpecUnsigned formatPayloadUnsigned; rw [hpay, snprintf_length]; rfl
          refine ⟨?_, ?_, ?_, ?_, hkle⟩
          · rw [hsD]; exact hd.1
          · rw [hsD]; exact hd.2.1
          · rw [hsD, hd.2.2.1, hspec1, hn17]
          · rw [hsD, hd.2.2.2, hspec2]

/-- End-to-end for unsigned mode at the default prepared machine
(`CAP = 8`, `WIDTH = 0`). -/
theorem intfmt_unsigned_e2e (n : Word) :
    (runCounted (prepU n) 2000).kind = HaltKind.programHalt ∧
    (runCounted (prepU n) 2000).steps ≤ 2000 ∧
    (runCounted (prepU n) 2000).state.halted = true ∧
    (machineBuf (runCounted (prepU n) 2000).state 8).map UInt16.toNat =
      (formatSpecUnsigned n).1 ∧
    (machineLen (runCounted (prepU n) 2000).state).toNat =
      (formatSpecUnsigned n).2 := by
  have hd := unsigned_prep_done n
  have hkle : 15 + placeAllSteps n.toNat + unsignedTail n.toNat ≤ 1348 := hd.2.2.2.2
  have hfuel : 15 + placeAllSteps n.toNat + unsignedTail n.toNat ≤ 2000 :=
    Nat.le_trans hkle (by decide)
  have hhalt :
      (runN (prepU n) (15 + placeAllSteps n.toNat + unsignedTail n.toNat)).halted = true ∨
        32768 ≤ (runN (prepU n) (15 + placeAllSteps n.toNat + unsignedTail n.toNat)).pc.toNat :=
    Or.inl hd.2.1
  have ⟨hkind, hsteps, hh, hm⟩ :=
    runCounted_programHalt_of_runN (prepU n)
      (15 + placeAllSteps n.toNat + unsignedTail n.toNat) 2000 hfuel hhalt
  refine ⟨hkind, Nat.le_trans hsteps hfuel, hh, ?_, ?_⟩
  · have hc := machineBuf_congr hm
    rw [hc]
    exact hd.2.2.1
  · have hc := machineLen_congr (hm 16)
    rw [hc]
    exact hd.2.2.2.1

end IntFmt
