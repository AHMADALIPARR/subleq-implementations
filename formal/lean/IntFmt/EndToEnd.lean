/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

End-to-end theorems for `intfmt.dec` at the default prepared machine
(`CAP = 8`, `WIDTH = 0`): every unsigned 16-bit word and every `Int16`
in signed mode halts within 2000 steps, and `BUF`/`LEN` (plus the
terminating NUL) match `formatSpec` / `formatSpecUnsigned`.
-/

import IntFmt.FrontPath
import IntFmt.AsciiHalt
import IntFmt.SignHalt
import IntFmt.HaveDigHalt5

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-! ### Decimal length, `uToDigits`, and `snprintfSpec` -/

theorem digitsLSD_of_lt {n base : Nat} (_hb : 2 ≤ base) (hn : n < base) :
    digitsLSD n base = [n] := by
  unfold digitsLSD
  have h : ¬ (2 ≤ base ∧ base ≤ n) := by omega
  simp [h]

theorem digitsLSD_of_ge {n base : Nat} (_hb : 2 ≤ base) (hn : base ≤ n) :
    digitsLSD n base = (n % base) :: digitsLSD (n / base) base := by
  have eq := divmodSub_eq n base _hb
  have h : 2 ≤ base ∧ base ≤ n := ⟨_hb, hn⟩
  have hdef : digitsLSD n base =
      (divmodSub n base).2 :: digitsLSD (divmodSub n base).1 base := by
    conv =>
      lhs
      unfold digitsLSD
    simp [h]
  rw [hdef, eq]

theorem uToDigits_succ {n : Nat} (h : 10 ≤ n) :
    uToDigits n 10 = uToDigits (n / 10) 10 ++ [n % 10] := by
  simp [uToDigits, digitsLSD_of_ge (by decide : 2 ≤ 10) h, List.reverse_cons]

theorem uToDigits_1 {n : Nat} (h : n < 10) :
    uToDigits n 10 = [n] := by
  simp [uToDigits, digitsLSD_of_lt (by decide : 2 ≤ 10) h]

theorem uToDigits_2 {n : Nat} (h1 : 10 ≤ n) (h2 : n < 100) :
    uToDigits n 10 = [n / 10, n % 10] := by
  have hdiv : n / 10 < 10 := by omega
  rw [uToDigits_succ h1, uToDigits_1 hdiv]
  rfl

theorem uToDigits_3 {n : Nat} (h1 : 100 ≤ n) (h2 : n < 1000) :
    uToDigits n 10 = [n / 100, n / 10 % 10, n % 10] := by
  have hdiv : 10 ≤ n / 10 := by omega
  have hdiv2 : n / 10 < 100 := by omega
  have h10 : 10 ≤ n := by omega
  rw [uToDigits_succ h10, uToDigits_2 hdiv hdiv2]
  have hsplit : n / 10 / 10 = n / 100 := by omega
  have hmod : n / 10 % 10 = n / 10 % 10 := rfl
  simp [hsplit]

theorem uToDigits_4 {n : Nat} (h1 : 1000 ≤ n) (h2 : n < 10000) :
    uToDigits n 10 = [n / 1000, n / 100 % 10, n / 10 % 10, n % 10] := by
  have hdiv : 100 ≤ n / 10 := by omega
  have hdiv2 : n / 10 < 1000 := by omega
  have h10 : 10 ≤ n := by omega
  rw [uToDigits_succ h10, uToDigits_3 hdiv hdiv2]
  have hd : n / 10 / 100 = n / 1000 := by omega
  have hm : n / 10 / 10 % 10 = n / 100 % 10 := by omega
  simp [hd, hm]

theorem uToDigits_5 {n : Nat} (h1 : 10000 ≤ n) (h2 : n < 100000) :
    uToDigits n 10 = [n / 10000, n / 1000 % 10, n / 100 % 10, n / 10 % 10, n % 10] := by
  have hdiv : 1000 ≤ n / 10 := by omega
  have hdiv2 : n / 10 < 10000 := by omega
  have h10 : 10 ≤ n := by omega
  rw [uToDigits_succ h10, uToDigits_4 hdiv hdiv2]
  have hd : n / 10 / 1000 = n / 10000 := by omega
  have hm1 : n / 10 / 100 % 10 = n / 1000 % 10 := by omega
  have hm2 : n / 10 / 10 % 10 = n / 100 % 10 := by omega
  simp [hd, hm1, hm2]

theorem places_1 {n : Nat} (h : n < 10) :
    n / 10000 = 0 ∧ n / 1000 % 10 = 0 ∧ n / 100 % 10 = 0 ∧
    n / 10 % 10 = 0 ∧ n % 10 = n := by omega

theorem places_2 {n : Nat} (h1 : 10 ≤ n) (h2 : n < 100) :
    n / 10000 = 0 ∧ n / 1000 % 10 = 0 ∧ n / 100 % 10 = 0 ∧
    n / 10 % 10 = n / 10 ∧ 0 < n / 10 ∧ n / 10 ≤ 9 ∧ n % 10 ≤ 9 := by omega

theorem places_3 {n : Nat} (h1 : 100 ≤ n) (h2 : n < 1000) :
    n / 10000 = 0 ∧ n / 1000 % 10 = 0 ∧ n / 100 % 10 = n / 100 ∧
    0 < n / 100 ∧ n / 100 ≤ 9 ∧ n / 10 % 10 ≤ 9 ∧ n % 10 ≤ 9 := by omega

theorem places_4 {n : Nat} (h1 : 1000 ≤ n) (h2 : n < 10000) :
    n / 10000 = 0 ∧ n / 1000 % 10 = n / 1000 ∧
    0 < n / 1000 ∧ n / 1000 ≤ 9 ∧ n / 100 % 10 ≤ 9 ∧
    n / 10 % 10 ≤ 9 ∧ n % 10 ≤ 9 := by omega

theorem places_5 {n : Nat} (h1 : 10000 ≤ n) (h2 : n < 100000) :
    n / 10000 = n / 10000 ∧
    0 < n / 10000 ∧ n / 10000 ≤ 9 ∧ n / 1000 % 10 ≤ 9 ∧
    n / 100 % 10 ≤ 9 ∧ n / 10 % 10 ≤ 9 ∧ n % 10 ≤ 9 := by omega

theorem zero_toNat : ('0').toNat = 48 := rfl

theorem minus_toNat : ('-').toNat = 45 := rfl

theorem digitChar_toNat {d : Nat} (hd : d ≤ 9) :
    (digitChar d).toNat = 48 + d := by
  have hz : ('0').toNat = 48 := zero_toNat
  have hval : Nat.isValidChar (48 + d) := Or.inl (by omega)
  have hdef : digitChar d = Char.ofNat (48 + d) := by
    unfold digitChar
    rw [hz]
  rw [hdef]
  unfold Char.ofNat
  simp [hval, Char.ofNatAux, Char.toNat]
  have : 48 + d < UInt32.size := by
    have hsz : UInt32.size = 4294967296 := rfl
    rw [hsz]; omega
  omega

theorem uToDec_toList (n : Nat) :
    (uToDec n).toList = (uToDigits n 10).map digitChar := by
  simp [uToDec, String.toList_ofList]

theorem payload_u_1 {n : Nat} (h : n < 10) :
    (uToDec n).toList.map Char.toNat = [48 + n] := by
  rw [uToDec_toList, uToDigits_1 h]
  simp [digitChar_toNat (Nat.le_of_lt_succ h)]

theorem payload_u_2 {n : Nat} (h1 : 10 ≤ n) (h2 : n < 100) :
    (uToDec n).toList.map Char.toNat = [48 + n / 10, 48 + n % 10] := by
  have ⟨_, _, _, _, hlo, hhi, hones⟩ := places_2 h1 h2
  rw [uToDec_toList, uToDigits_2 h1 h2]
  simp [digitChar_toNat (Nat.le_trans hhi (by decide : 9 ≤ 9)),
        digitChar_toNat hones]

theorem payload_u_3 {n : Nat} (h1 : 100 ≤ n) (h2 : n < 1000) :
    (uToDec n).toList.map Char.toNat =
      [48 + n / 100, 48 + n / 10 % 10, 48 + n % 10] := by
  have ⟨_, _, _, _, hhi, hm, hones⟩ := places_3 h1 h2
  rw [uToDec_toList, uToDigits_3 h1 h2]
  simp [digitChar_toNat hhi, digitChar_toNat hm, digitChar_toNat hones]

theorem payload_u_4 {n : Nat} (h1 : 1000 ≤ n) (h2 : n < 10000) :
    (uToDec n).toList.map Char.toNat =
      [48 + n / 1000, 48 + n / 100 % 10, 48 + n / 10 % 10, 48 + n % 10] := by
  have ⟨_, _, _, hhi, hm1, hm2, hones⟩ := places_4 h1 h2
  rw [uToDec_toList, uToDigits_4 h1 h2]
  simp [digitChar_toNat hhi, digitChar_toNat hm1, digitChar_toNat hm2,
        digitChar_toNat hones]

theorem payload_u_5 {n : Nat} (h1 : 10000 ≤ n) (h2 : n < 100000) :
    (uToDec n).toList.map Char.toNat =
      [48 + n / 10000, 48 + n / 1000 % 10, 48 + n / 100 % 10,
       48 + n / 10 % 10, 48 + n % 10] := by
  have ⟨_, _, hhi, hm1, hm2, hm3, hones⟩ := places_5 h1 h2
  rw [uToDec_toList, uToDigits_5 h1 h2]
  simp [digitChar_toNat hhi, digitChar_toNat hm1, digitChar_toNat hm2,
        digitChar_toNat hm3, digitChar_toNat hones]

theorem snprintf_fits (payload : List Nat) (h : payload.length ≤ 7) :
    snprintfSpec payload 8 =
      (payload ++ [0] ++ List.replicate (7 - payload.length) 0, payload.length) := by
  unfold snprintfSpec
  have htake : payload.take 7 = payload := List.take_of_length_le (by omega)
  simp [htake]
  have : min 7 payload.length = payload.length := Nat.min_eq_right (by omega)
  omega

def formatPayloadUnsigned (n : Word) : List Nat :=
  (uToDec n.toNat).toList.map (fun c => c.toNat)

def formatSpecUnsigned (n : Word) : List Nat × Nat :=
  snprintfSpec (formatPayloadUnsigned n) 8

def loadIntfmtDecUnsigned (n : Word) : Machine :=
  prepMachine n 0 8

theorem word_eq_zero {w : Word} (h : w.toNat = 0) : w = 0 :=
  UInt16.toNat.inj (h.trans (UInt16.toNat_zero).symm)

theorem word_toNat_eight : (8 : Word).toNat = 8 := rfl

theorem word_toNat_forty_eight : (48 : Word).toNat = 48 := rfl

theorem word_add_48 {w : Word} (h : w.toNat ≤ 9) :
    (w + 48).toNat = w.toNat + 48 := by
  have hw : (48 : Word) = UInt16.ofNat 48 := rfl
  rw [hw]
  have hadd := word_add_toNat w 48 (by omega)
  exact hadd

/-! ### `runCounted` from a halted `runN` -/

theorem runCounted_programHalt_of_runN (s : Machine) (k fuel : Nat)
    (hle : k ≤ fuel)
    (hhalt : (runN s k).halted = true ∨ 32768 ≤ (runN s k).pc.toNat) :
    (runCounted s fuel).kind = HaltKind.programHalt ∧
    (runCounted s fuel).steps ≤ k ∧
    (runCounted s fuel).state.halted = true ∧
    (∀ a, (runCounted s fuel).state.mem.get a = (runN s k).mem.get a) := by
  induction fuel generalizing s k with
  | zero =>
    have hk : k = 0 := Nat.eq_zero_of_le_zero hle
    subst hk
    have hb : (s.halted || 32768 ≤ s.pc.toNat) = true := by
      cases hhalt' : hhalt with
      | inl hh =>
        have : s.halted = true := by simpa [runN_zero] using hh
        simp [this]
      | inr hp =>
        have : 32768 ≤ s.pc.toNat := by simpa [runN_zero] using hp
        simp [this]
    simp [runCounted, hb, runN_zero]
  | succ fuel ih =>
    cases hb : (s.halted || 32768 ≤ s.pc.toNat) with
    | true =>
      have hmem : ∀ a, ({ s with halted := true } : Machine).mem.get a = (runN s k).mem.get a := by
        intro a
        have : ({ s with halted := true } : Machine).mem = s.mem := rfl
        rw [this]
        cases k with
        | zero =>
          simp [runN_zero]
        | succ k =>
          simp [runN_succ, hb]
      have hr : runCounted s (fuel + 1) =
          { state := { s with halted := true }, steps := 0, kind := HaltKind.programHalt } := by
        simp [runCounted, hb]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [hr]
      · simp [hr]
      · simp [hr]
      · intro a; simpa [hr] using hmem a
    | false =>
      have hgo : s.halted = false ∧ s.pc.toNat < 32768 := by
        cases hs : s.halted with
        | true => simp [hs] at hb
        | false =>
          refine ⟨rfl, ?_⟩
          have : ¬ (32768 ≤ s.pc.toNat) := by
            intro hp; simp [hs, hp] at hb
          exact Nat.lt_of_not_ge this
      cases k with
      | zero =>
        have hhalt0 : (runN s 0).halted = true ∨ 32768 ≤ (runN s 0).pc.toNat := hhalt
        simp [runN_zero] at hhalt0
        cases hs : s.halted with
        | true => simp [hs] at hb
        | false =>
          cases hhalt0 with
          | inl hh => simp [hs] at hh
          | inr hp =>
            have : ¬ (32768 ≤ s.pc.toNat) := Nat.not_le_of_lt hgo.2
            exact (this hp).elim
      | succ k =>
        have hle' : k ≤ fuel := Nat.succ_le_succ_iff.mp hle
        have hrun : runN s (k + 1) = runN (step s) k :=
          runN_succ_go s k hgo.1 hgo.2
        have hhalt' : (runN (step s) k).halted = true ∨
            32768 ≤ (runN (step s) k).pc.toNat := by
          simpa [hrun] using hhalt
        have ⟨hk, hs, hh, hm⟩ := ih (step s) k hle' hhalt'
        have hr : runCounted s (fuel + 1) =
            let r := runCounted (step s) fuel
            { r with steps := r.steps + 1 } := by
          simp [runCounted, hb]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [hr] using hk
        · have : (runCounted s (fuel + 1)).steps = (runCounted (step s) fuel).steps + 1 := by
            simp [hr]
          omega
        · simpa [hr] using hh
        · intro a
          have : (runCounted s (fuel + 1)).state.mem.get a =
              (runCounted (step s) fuel).state.mem.get a := by
            simp [hr]
          exact this.trans ((hm a).trans (by simp [hrun]))

/-! ### Image / arrival buffer zeros -/

theorem image_cell_BUF {i : Nat} (hi : i < 8) :
    intfmtImage[32 + i]! = 0 := by
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h
  <;> subst h
  <;> rfl

theorem addrBuf_add {i : Nat} (hi : i < 8) :
    addrBuf + UInt16.ofNat i = UInt16.ofNat (32 + i) := by
  have h32 : addrBuf = UInt16.ofNat 32 := rfl
  rw [h32]
  apply UInt16.toNat.inj
  have h32t : (UInt16.ofNat 32).toNat = 32 := UInt16.toNat_ofNat_of_lt (by decide)
  have hsum : (UInt16.ofNat 32).toNat + i < 65536 := by rw [h32t]; omega
  have hL := word_add_toNat (UInt16.ofNat 32) i hsum
  have hsz : UInt16.size = 65536 := rfl
  have hR : (UInt16.ofNat (32 + i)).toNat = 32 + i :=
    UInt16.toNat_ofNat_of_lt (by rw [hsz]; omega)
  rw [hL, h32t, hR]

theorem machineBuf_eight (s : Machine) :
    machineBuf s 8 =
      [s.mem.get 32, s.mem.get 33, s.mem.get 34, s.mem.get 35,
       s.mem.get 36, s.mem.get 37, s.mem.get 38, s.mem.get 39] := by
  have hr : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  unfold machineBuf
  rw [hr]
  simp only [List.map]
  have e0 := addrBuf_add (i := 0) (by decide)
  have e1 := addrBuf_add (i := 1) (by decide)
  have e2 := addrBuf_add (i := 2) (by decide)
  have e3 := addrBuf_add (i := 3) (by decide)
  have e4 := addrBuf_add (i := 4) (by decide)
  have e5 := addrBuf_add (i := 5) (by decide)
  have e6 := addrBuf_add (i := 6) (by decide)
  have e7 := addrBuf_add (i := 7) (by decide)
  have c32 : UInt16.ofNat 32 = (32 : Word) := rfl
  have c33 : UInt16.ofNat 33 = (33 : Word) := rfl
  have c34 : UInt16.ofNat 34 = (34 : Word) := rfl
  have c35 : UInt16.ofNat 35 = (35 : Word) := rfl
  have c36 : UInt16.ofNat 36 = (36 : Word) := rfl
  have c37 : UInt16.ofNat 37 = (37 : Word) := rfl
  have c38 : UInt16.ofNat 38 = (38 : Word) := rfl
  have c39 : UInt16.ofNat 39 = (39 : Word) := rfl
  rw [e0, e1, e2, e3, e4, e5, e6, e7, c32, c33, c34, c35, c36, c37, c38, c39]

theorem machineBuf_map_eight (s : Machine)
    (h32 h33 h34 h35 h36 h37 h38 h39 : Nat)
    (e32 : (s.mem.get 32).toNat = h32)
    (e33 : (s.mem.get 33).toNat = h33)
    (e34 : (s.mem.get 34).toNat = h34)
    (e35 : (s.mem.get 35).toNat = h35)
    (e36 : (s.mem.get 36).toNat = h36)
    (e37 : (s.mem.get 37).toNat = h37)
    (e38 : (s.mem.get 38).toNat = h38)
    (e39 : (s.mem.get 39).toNat = h39) :
    (machineBuf s 8).map UInt16.toNat = [h32, h33, h34, h35, h36, h37, h38, h39] := by
  rw [machineBuf_eight]
  simp [e32, e33, e34, e35, e36, e37, e38, e39]

/-! ### Arrival lemmas: unread image cells, including `BUF` -/

private theorem ofNat_ne_word (k b : Nat)
    (hk : k < 65536) (hb : b < 65536) (hne : k ≠ b) :
    UInt16.ofNat k ≠ UInt16.ofNat b :=
  ofNat_ne k b hk hb hne

theorem unsigned_at_digits_get (input cap : Word) (k : Nat)
    (hk : k < 2323)
    (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13)
    (hSIGN : k ≠ 19) (hLEN : k ≠ 16) (hPAD : k ≠ 27) (hNDIG : k ≠ 25)
    (hN : k ≠ 17) (hZ : k ≠ 0) (hT : k ≠ 18) :
    (runN (prepMachine input 0 cap) 15).mem.get (UInt16.ofNat k) =
      intfmtImage[k]! := by
  have hs : runN (prepMachine input 0 cap) 15 =
      runN (afterStartMov input 0 cap) 6 :=
    unsigned_prep_to_digits input cap
  rw [hs]
  have hd := mode_dispatch_unsigned input cap
  have hpres := hd.2.2.2.2.2.2.2
  have n18 : UInt16.ofNat k ≠ (18 : Word) := by
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]; exact ofNat_ne_word k 18 (by omega) (by decide) hT
  have n0 : UInt16.ofNat k ≠ (0 : Word) := by
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]; exact ofNat_ne_word k 0 (by omega) (by decide) hZ
  have himg := afterStartMov_get_image input 0 cap k hk hIn hMo hCa
    hSIGN hLEN hPAD hNDIG hN hZ
  exact (hpres (UInt16.ofNat k) n18 n0).trans himg

theorem unsigned_at_digits_buf0 (input cap : Word) {i : Nat} (hi : i < 8) :
    (runN (prepMachine input 0 cap) 15).mem.get (UInt16.ofNat (32 + i)) = 0 :=
  (unsigned_at_digits_get input cap (32 + i) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)).trans
    (image_cell_BUF hi)

theorem signed_pos_at_digits_get (input cap : Word)
    (hpos : 0 < input.toNat) (hhi : input.toNat < 32768) (k : Nat)
    (hk : k < 2323)
    (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13)
    (hSIGN : k ≠ 19) (hLEN : k ≠ 16) (hPAD : k ≠ 27) (hNDIG : k ≠ 25)
    (hN : k ≠ 17) (hZ : k ≠ 0) (hT : k ≠ 18) :
    (runN (prepMachine input 1 cap) 26).mem.get (UInt16.ofNat k) =
      intfmtImage[k]! := by
  have hs : runN (prepMachine input 1 cap) 26 =
      runN (afterSignedDispatch input cap) 11 :=
    signed_pos_prep_to_digits input cap hpos hhi
  rw [hs]
  have hp := i_path_pos input cap hpos hhi
  have hpres := hp.2.2.2.2.2.2
  have n18 : UInt16.ofNat k ≠ (18 : Word) := by
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]; exact ofNat_ne_word k 18 (by omega) (by decide) hT
  have n0 : UInt16.ofNat k ≠ (0 : Word) := by
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]; exact ofNat_ne_word k 0 (by omega) (by decide) hZ
  have himg := afterSignedDispatch_get input cap k hk hIn hMo hCa
    hSIGN hLEN hPAD hNDIG hN hZ hT
  exact (hpres (UInt16.ofNat k) n18 n0).trans himg

theorem signed_pos_at_digits_buf0 (input cap : Word)
    (hpos : 0 < input.toNat) (hhi : input.toNat < 32768)
    {i : Nat} (hi : i < 8) :
    (runN (prepMachine input 1 cap) 26).mem.get (UInt16.ofNat (32 + i)) = 0 :=
  (signed_pos_at_digits_get input cap hpos hhi (32 + i) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)).trans
    (image_cell_BUF hi)

theorem signed_zero_at_digits_get (cap : Word) (k : Nat)
    (hk : k < 2323)
    (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13)
    (hSIGN : k ≠ 19) (hLEN : k ≠ 16) (hPAD : k ≠ 27) (hNDIG : k ≠ 25)
    (hN : k ≠ 17) (hZ : k ≠ 0) (hT : k ≠ 18) :
    (runN (prepMachine 0 1 cap) 30).mem.get (UInt16.ofNat k) =
      intfmtImage[k]! := by
  have hs : runN (prepMachine 0 1 cap) 30 =
      runN (afterSignedDispatch 0 cap) 15 :=
    signed_zero_prep_to_digits cap
  rw [hs]
  have hp := i_path_zero cap
  have hpres := hp.2.2.2.2.2.2
  have n18 : UInt16.ofNat k ≠ (18 : Word) := by
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]; exact ofNat_ne_word k 18 (by omega) (by decide) hT
  have n0 : UInt16.ofNat k ≠ (0 : Word) := by
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]; exact ofNat_ne_word k 0 (by omega) (by decide) hZ
  have himg := afterSignedDispatch_get 0 cap k hk hIn hMo hCa
    hSIGN hLEN hPAD hNDIG hN hZ hT
  exact (hpres (UInt16.ofNat k) n18 n0).trans himg

theorem signed_zero_at_digits_buf0 (cap : Word) {i : Nat} (hi : i < 8) :
    (runN (prepMachine 0 1 cap) 30).mem.get (UInt16.ofNat (32 + i)) = 0 :=
  (signed_zero_at_digits_get cap (32 + i) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)).trans
    (image_cell_BUF hi)

theorem signed_neg_at_digits_get (input cap : Word)
    (hneg : 32768 ≤ input.toNat) (k : Nat)
    (hk : k < 2323)
    (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13)
    (hSIGN : k ≠ 19) (hLEN : k ≠ 16) (hPAD : k ≠ 27) (hNDIG : k ≠ 25)
    (hN : k ≠ 17) (hZ : k ≠ 0) (hT : k ≠ 18) :
    (runN (prepMachine input 1 cap) 40).mem.get (UInt16.ofNat k) =
      intfmtImage[k]! := by
  have hs : runN (prepMachine input 1 cap) 40 =
      runN (afterSignedDispatch input cap) 25 :=
    signed_neg_prep_to_digits input cap hneg
  rw [hs]
  have hp := i_path_neg input cap hneg
  have hpres := hp.2.2.2.2.2.2
  have n18 : UInt16.ofNat k ≠ (18 : Word) := by
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]; exact ofNat_ne_word k 18 (by omega) (by decide) hT
  have n0 : UInt16.ofNat k ≠ (0 : Word) := by
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]; exact ofNat_ne_word k 0 (by omega) (by decide) hZ
  have n19 : UInt16.ofNat k ≠ (19 : Word) := by
    have : (19 : Word) = UInt16.ofNat 19 := rfl
    rw [this]; exact ofNat_ne_word k 19 (by omega) (by decide) hSIGN
  have n17 : UInt16.ofNat k ≠ (17 : Word) := by
    have : (17 : Word) = UInt16.ofNat 17 := rfl
    rw [this]; exact ofNat_ne_word k 17 (by omega) (by decide) hN
  have himg := afterSignedDispatch_get input cap k hk hIn hMo hCa
    hSIGN hLEN hPAD hNDIG hN hZ hT
  exact (hpres (UInt16.ofNat k) n18 n0 n19 n17).trans himg

theorem signed_neg_at_digits_buf0 (input cap : Word)
    (hneg : 32768 ≤ input.toNat) {i : Nat} (hi : i < 8) :
    (runN (prepMachine input 1 cap) 40).mem.get (UInt16.ofNat (32 + i)) = 0 :=
  (signed_neg_at_digits_get input cap hneg (32 + i) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)).trans
    (image_cell_BUF hi)

/-! ### Int16 bit-pattern / magnitude -/

private theorem int16_toInt_eq_bits (n : Int16) :
    n.toInt =
      if 2 * n.toBitVec.toNat < 2 ^ 16 then
        (n.toBitVec.toNat : Int)
      else
        (n.toBitVec.toNat : Int) - 65536 := by
  have hti : n.toInt = n.toBitVec.toInt := rfl
  have hcond := BitVec.toInt_eq_toNat_cond (n := 16) n.toBitVec
  rw [hti, hcond]
  simp

theorem int16_bits_nonneg (n : Int16) (h : 0 ≤ n.toInt) :
    n.toBitVec.toNat = n.toInt.toNat := by
  have hrep := int16_toInt_eq_bits n
  by_cases hm : 2 * n.toBitVec.toNat < 2 ^ 16
  · have : n.toInt = n.toBitVec.toNat := by simp [hrep, hm]
    rw [this, Int.toNat_natCast]
  · have : n.toInt = (n.toBitVec.toNat : Int) - 65536 := by simp [hrep, hm]
    have hlt : n.toBitVec.toNat < 65536 :=
      Nat.lt_of_lt_of_eq n.toBitVec.isLt (by decide)
    omega

theorem int16_bits_neg (n : Int16) (h : n.toInt < 0) :
    n.toBitVec.toNat = (n.toInt + 65536).toNat := by
  have hrep := int16_toInt_eq_bits n
  by_cases hm : 2 * n.toBitVec.toNat < 2 ^ 16
  · have : n.toInt = n.toBitVec.toNat := by simp [hrep, hm]
    omega
  · have : n.toInt = (n.toBitVec.toNat : Int) - 65536 := by simp [hrep, hm]
    have heq : n.toInt + 65536 = n.toBitVec.toNat := by omega
    rw [heq, Int.toNat_natCast]

theorem int16_input_toNat (n : Int16) :
    (UInt16.ofNat n.toBitVec.toNat).toNat = n.toBitVec.toNat :=
  UInt16.toNat_ofNat_of_lt (Nat.lt_of_lt_of_eq n.toBitVec.isLt (by decide))

theorem int16_pos_bits (n : Int16) (h : 0 < n.toInt) :
    0 < (UInt16.ofNat n.toBitVec.toNat).toNat ∧
    (UInt16.ofNat n.toBitVec.toNat).toNat < 32768 ∧
    (UInt16.ofNat n.toBitVec.toNat).toNat = n.toInt.toNat := by
  have hnn : 0 ≤ n.toInt := Int.le_of_lt h
  have hb := int16_bits_nonneg n hnn
  have ht := int16_input_toNat n
  have hlt := Int16.toInt_lt n
  have hbound : n.toInt < 32768 := by
    have : (2 ^ 15 : Int) = 32768 := rfl
    exact lt_of_lt_of_eq hlt this
  have hnat : n.toInt.toNat < 32768 := by
    have hc : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg hnn
    have : (n.toInt.toNat : Int) < 32768 := by omega
    exact Int.ofNat_lt.mp this
  omega

theorem int16_zero_bits (n : Int16) (h : n.toInt = 0) :
    UInt16.ofNat n.toBitVec.toNat = 0 := by
  have hb := int16_bits_nonneg n (by omega)
  have : n.toBitVec.toNat = 0 := by
    rw [hb, h]
    rfl
  exact word_eq_zero ((int16_input_toNat n).trans this)

theorem int16_neg_bits (n : Int16) (h : n.toInt < 0) :
    32768 ≤ (UInt16.ofNat n.toBitVec.toNat).toNat := by
  have hrep := int16_toInt_eq_bits n
  by_cases hm : 2 * n.toBitVec.toNat < 2 ^ 16
  · have : n.toInt = n.toBitVec.toNat := by simp [hrep, hm]
    omega
  · have : n.toInt = (n.toBitVec.toNat : Int) - 65536 := by simp [hrep, hm]
    have : (n.toBitVec.toNat : Int) ≥ 32768 := by omega
    have hbits : 32768 ≤ n.toBitVec.toNat := Int.ofNat_le.mp this
    have ht := int16_input_toNat n
    omega

theorem int16_neg_mag (n : Int16) (h : n.toInt < 0) :
    (0 - UInt16.ofNat n.toBitVec.toNat).toNat = n.toInt.natAbs := by
  have ht := int16_input_toNat n
  have hrep := int16_toInt_eq_bits n
  have hm : ¬ (2 * n.toBitVec.toNat < 2 ^ 16) := by
    intro hm
    have : n.toInt = n.toBitVec.toNat := by simp [hrep, hm]
    omega
  have hrep' : n.toInt = (n.toBitVec.toNat : Int) - 65536 := by simp [hrep, hm]
  have hpos : 0 < n.toBitVec.toNat := by
    have : (n.toBitVec.toNat : Int) ≥ 32768 := by omega
    have : 32768 ≤ n.toBitVec.toNat := Int.ofNat_le.mp this
    omega
  rw [UInt16.zero_sub, UInt16.toNat_neg, ht]
  have hsz : UInt16.size = 65536 := rfl
  rw [hsz]
  have hmod : (65536 - n.toBitVec.toNat) % 65536 = 65536 - n.toBitVec.toNat :=
    Nat.mod_eq_of_lt (Nat.sub_lt (by decide) hpos)
  rw [hmod]
  have habs : (n.toInt.natAbs : Int) = -n.toInt :=
    Int.ofNat_natAbs_of_nonpos (Int.le_of_lt h)
  have hbits_le : n.toBitVec.toNat ≤ 65536 :=
    Nat.le_of_lt (Nat.lt_of_lt_of_eq n.toBitVec.isLt (by decide))
  have hrhs : ((65536 - n.toBitVec.toNat : Nat) : Int) = -n.toInt := by
    rw [Int.natCast_sub hbits_le, hrep']
    omega
  exact Int.ofNat_inj.mp (hrhs.trans habs.symm)


/-! ### Helpers to lift constants and code through the place loops -/

private theorem digits_pres_get {s sP : Machine}
    (hpres : ∀ a, a ≠ 17 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 24 → a ≠ 18 → a ≠ 0 →
      sP.mem.get a = s.mem.get a)
    (a : Word)
    (h17 : a ≠ 17) (h20 : a ≠ 20) (h21 : a ≠ 21) (h22 : a ≠ 22)
    (h23 : a ≠ 23) (h24 : a ≠ 24) (h18 : a ≠ 18) (h0 : a ≠ 0) :
    sP.mem.get a = s.mem.get a :=
  hpres a h17 h20 h21 h22 h23 h24 h18 h0

private theorem p3_code_from_digits {s sP : Machine}
    (hpres : ∀ a, a ≠ 17 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 24 → a ≠ 18 → a ≠ 0 →
      sP.mem.get a = s.mem.get a)
    (hcode : ∀ k : Nat, 174 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    ∀ k : Nat, 513 ≤ k → k < 2319 →
      sP.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
  intro k h1 h2
  have n17 : UInt16.ofNat k ≠ (17 : Word) := by
    have : (17 : Word) = UInt16.ofNat 17 := rfl
    rw [this]; exact ofNat_ne_word k 17 (by omega) (by decide) (by omega)
  have n20 : UInt16.ofNat k ≠ (20 : Word) := by
    have : (20 : Word) = UInt16.ofNat 20 := rfl
    rw [this]; exact ofNat_ne_word k 20 (by omega) (by decide) (by omega)
  have n21 : UInt16.ofNat k ≠ (21 : Word) := by
    have : (21 : Word) = UInt16.ofNat 21 := rfl
    rw [this]; exact ofNat_ne_word k 21 (by omega) (by decide) (by omega)
  have n22 : UInt16.ofNat k ≠ (22 : Word) := by
    have : (22 : Word) = UInt16.ofNat 22 := rfl
    rw [this]; exact ofNat_ne_word k 22 (by omega) (by decide) (by omega)
  have n23 : UInt16.ofNat k ≠ (23 : Word) := by
    have : (23 : Word) = UInt16.ofNat 23 := rfl
    rw [this]; exact ofNat_ne_word k 23 (by omega) (by decide) (by omega)
  have n24 : UInt16.ofNat k ≠ (24 : Word) := by
    have : (24 : Word) = UInt16.ofNat 24 := rfl
    rw [this]; exact ofNat_ne_word k 24 (by omega) (by decide) (by omega)
  have n18 : UInt16.ofNat k ≠ (18 : Word) := by
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]; exact ofNat_ne_word k 18 (by omega) (by decide) (by omega)
  have n0 : UInt16.ofNat k ≠ (0 : Word) := by
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]; exact ofNat_ne_word k 0 (by omega) (by decide) (by omega)
  exact (hpres (UInt16.ofNat k) n17 n20 n21 n22 n23 n24 n18 n0).trans
    (hcode k (by omega) h2)

private theorem buf0_cell {s : Machine}
    (hbuf : ∀ i : Nat, i < 8 → s.mem.get (UInt16.ofNat (32 + i)) = 0)
    (w : Word) (i : Nat) (hi : i < 8) (heq : w = UInt16.ofNat (32 + i)) :
    s.mem.get w = 0 := by
  rw [heq]; exact hbuf i hi

theorem snprintf_1 (d : Nat) :
    snprintfSpec [48 + d] 8 = ([48 + d, 0, 0, 0, 0, 0, 0, 0], 1) := by
  have h := snprintf_fits [48 + d] (by simp)
  have hr : List.replicate 6 0 = [0, 0, 0, 0, 0, 0] := rfl
  simpa [hr] using h

theorem snprintf_2 (a b : Nat) :
    snprintfSpec [48 + a, 48 + b] 8 = ([48 + a, 48 + b, 0, 0, 0, 0, 0, 0], 2) := by
  have h := snprintf_fits [48 + a, 48 + b] (by simp)
  have hr : List.replicate 5 0 = [0, 0, 0, 0, 0] := rfl
  simpa [hr] using h

theorem snprintf_3 (a b c : Nat) :
    snprintfSpec [48 + a, 48 + b, 48 + c] 8 =
      ([48 + a, 48 + b, 48 + c, 0, 0, 0, 0, 0], 3) := by
  have h := snprintf_fits [48 + a, 48 + b, 48 + c] (by simp)
  have hr : List.replicate 4 0 = [0, 0, 0, 0] := rfl
  simpa [hr] using h

theorem snprintf_4 (a b c d : Nat) :
    snprintfSpec [48 + a, 48 + b, 48 + c, 48 + d] 8 =
      ([48 + a, 48 + b, 48 + c, 48 + d, 0, 0, 0, 0], 4) := by
  have h := snprintf_fits [48 + a, 48 + b, 48 + c, 48 + d] (by simp)
  have hr : List.replicate 3 0 = [0, 0, 0] := rfl
  simpa [hr] using h

theorem snprintf_5 (a b c d e : Nat) :
    snprintfSpec [48 + a, 48 + b, 48 + c, 48 + d, 48 + e] 8 =
      ([48 + a, 48 + b, 48 + c, 48 + d, 48 + e, 0, 0, 0], 5) := by
  have h := snprintf_fits [48 + a, 48 + b, 48 + c, 48 + d, 48 + e] (by simp)
  have hr : List.replicate 2 0 = [0, 0] := rfl
  simpa [hr] using h

theorem snprintf_m1 (d : Nat) :
    snprintfSpec [45, 48 + d] 8 = ([45, 48 + d, 0, 0, 0, 0, 0, 0], 2) := by
  have h := snprintf_fits [45, 48 + d] (by simp)
  have hr : List.replicate 5 0 = [0, 0, 0, 0, 0] := rfl
  simpa [hr] using h

theorem snprintf_m2 (a b : Nat) :
    snprintfSpec [45, 48 + a, 48 + b] 8 =
      ([45, 48 + a, 48 + b, 0, 0, 0, 0, 0], 3) := by
  have h := snprintf_fits [45, 48 + a, 48 + b] (by simp)
  have hr : List.replicate 4 0 = [0, 0, 0, 0] := rfl
  simpa [hr] using h

theorem snprintf_m3 (a b c : Nat) :
    snprintfSpec [45, 48 + a, 48 + b, 48 + c] 8 =
      ([45, 48 + a, 48 + b, 48 + c, 0, 0, 0, 0], 4) := by
  have h := snprintf_fits [45, 48 + a, 48 + b, 48 + c] (by simp)
  have hr : List.replicate 3 0 = [0, 0, 0] := rfl
  simpa [hr] using h

theorem snprintf_m4 (a b c d : Nat) :
    snprintfSpec [45, 48 + a, 48 + b, 48 + c, 48 + d] 8 =
      ([45, 48 + a, 48 + b, 48 + c, 48 + d, 0, 0, 0], 5) := by
  have h := snprintf_fits [45, 48 + a, 48 + b, 48 + c, 48 + d] (by simp)
  have hr : List.replicate 2 0 = [0, 0] := rfl
  simpa [hr] using h

theorem snprintf_m5 (a b c d e : Nat) :
    snprintfSpec [45, 48 + a, 48 + b, 48 + c, 48 + d, 48 + e] 8 =
      ([45, 48 + a, 48 + b, 48 + c, 48 + d, 48 + e, 0, 0], 6) := by
  have h := snprintf_fits [45, 48 + a, 48 + b, 48 + c, 48 + d, 48 + e] (by simp)
  have hr : List.replicate 1 0 = [0] := rfl
  simpa [hr] using h

def unsignedTail (n : Nat) : Nat :=
  if n < 10 then 337
  else if n < 100 then 405
  else if n < 1000 then 462
  else if n < 10000 then 519
  else 576

def signedTail (n : Nat) : Nat :=
  if n < 10 then 389
  else if n < 100 then 459
  else if n < 1000 then 518
  else if n < 10000 then 577
  else 636

theorem unsignedTail_le (n : Nat) : unsignedTail n ≤ 576 := by
  unfold unsignedTail
  by_cases h1 : n < 10
  · simp [h1]
  · by_cases h2 : n < 100
    · simp [h1, h2]
    · by_cases h3 : n < 1000
      · simp [h1, h2, h3]
      · by_cases h4 : n < 10000
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

theorem signedTail_le (n : Nat) : signedTail n ≤ 636 := by
  unfold signedTail
  by_cases h1 : n < 10
  · simp [h1]
  · by_cases h2 : n < 100
    · simp [h1, h2]
    · by_cases h3 : n < 1000
      · simp [h1, h2, h3]
      · by_cases h4 : n < 10000
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

/-- Shared hypotheses for a machine sitting at `DIGITS` with default
`CAP = 8`, `WIDTH = 0`, and a zeroed 8-cell `BUF`. -/
def atDigitsDefault (s : Machine) : Prop :=
  s.pc = 174 ∧
  s.halted = false ∧
  s.mem.get 0 = 0 ∧
  s.mem.get 3 = 1 ∧
  s.mem.get 4 = 10 ∧
  s.mem.get 5 = 100 ∧
  s.mem.get 6 = 1000 ∧
  s.mem.get 7 = 10000 ∧
  s.mem.get 8 = 48 ∧
  s.mem.get 9 = 45 ∧
  s.mem.get 2322 = 5 ∧
  s.mem.get 14 = 0 ∧
  s.mem.get 13 = 8 ∧
  (∀ i : Nat, i < 8 → s.mem.get (UInt16.ofNat (32 + i)) = 0) ∧
  (∀ k : Nat, 174 ≤ k → k < 2319 →
    s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)



/-! ### From `DIGITS` through `P3_DONE` tails, unsigned (`SIGN = 0`) -/

set_option maxHeartbeats 16000000

private theorem digits_hcode_place {s : Machine}
    (hcode : ∀ k : Nat, 174 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    ∀ k : Nat, 174 ≤ k → k < 513 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
  fun k h1 h2 => hcode k h1 (Nat.lt_trans h2 (by decide))

theorem unsigned_digits_ndig1_done {s : Machine}
    (hat : atDigitsDefault s)
    (hS : s.mem.get 19 = 0)
    (hn : (s.mem.get 17).toNat < 10) :
    let n := (s.mem.get 17).toNat
    let sD := runN s (placeAllSteps n + 337)
    sD.pc = 32768 ∧
    sD.halted = true ∧
    (machineBuf sD 8).map UInt16.toNat = (snprintfSpec [48 + n] 8).1 ∧
    (machineLen sD).toNat = 1 := by
  intro n sD
  have ⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
        hW, hC, hbuf, hcode⟩ := hat
  have hp := digits_to_p3_done (s := s) hpc hh hZ hONE hTEN hC100 hC1000
    hC10000 (digits_hcode_place hcode)
  have ⟨hpcP, hhP, hZP, hQ0, hQ1, hQ2, hQ3, hones, hQ4, hpres⟩ := hp
  let sP := runN s (placeAllSteps n)
  have hrun : sD = runN sP 337 :=
    runN_add_eq s (placeAllSteps n) 337 (placeAllSteps n + 337) rfl
  have pl := places_1 hn
  have z20 : sP.mem.get 20 = 0 := word_eq_zero (hQ0.trans pl.1)
  have z21 : sP.mem.get 21 = 0 := word_eq_zero (hQ1.trans pl.2.1)
  have z22 : sP.mem.get 22 = 0 := word_eq_zero (hQ2.trans pl.2.2.1)
  have z23 : sP.mem.get 23 = 0 := word_eq_zero (hQ3.trans pl.2.2.2.1)
  have hONEP : sP.mem.get 3 = 1 :=
    (hpres 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48P : sP.mem.get 8 = 48 :=
    (hpres 8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hK5P : sP.mem.get 2322 = 5 :=
    (hpres 2322 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hSP : sP.mem.get 19 = 0 :=
    (hpres 19 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hS
  have hWP : sP.mem.get 14 = 0 :=
    (hpres 14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hW
  have hCP : sP.mem.get 13 = 8 :=
    (hpres 13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hC
  have hClo : 0 < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hChi : (sP.mem.get 13).toNat < 32768 := by rw [hCP, word_toNat_eight]; decide
  have hLlt : (1 : Nat) < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hcodeP := p3_code_from_digits hpres hcode
  have hd := p3_done_unsigned_ndig1_done (s := sP) hpcP hhP hZP hONEP hK48P
    hK5P hSP hWP z20 z21 z22 z23 hClo hChi hLlt hcodeP
  have ⟨hpcD, hhD, hZD, g32, g33, g29, g16, hpresD⟩ := hd
  have hones_le : (sP.mem.get 17).toNat ≤ 9 := by
    rw [hones, pl.2.2.2.2]; omega
  have t32 : (sD.mem.get 32).toNat = 48 + n := by
    rw [hrun, g32, word_add_48 hones_le, hones, pl.2.2.2.2]
    omega
  have t33 : (sD.mem.get 33).toNat = 0 := by
    rw [hrun, g33]; decide
  have z : ∀ i : Nat, i < 8 → s.mem.get (UInt16.ofNat (32 + i)) = 0 := hbuf
  have t34 : (sD.mem.get 34).toNat = 0 := by
    have : (34 : Word) = UInt16.ofNat 34 := rfl
    have hs : s.mem.get 34 = 0 := by rw [this]; exact z 2 (by decide)
    have hP : sP.mem.get 34 = s.mem.get 34 :=
      hpres 34 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 34 = sP.mem.get 34 := by
      rw [hrun]
      exact (hpresD 34
      (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t35 : (sD.mem.get 35).toNat = 0 := by
    have : (35 : Word) = UInt16.ofNat 35 := rfl
    have hs : s.mem.get 35 = 0 := by rw [this]; exact z 3 (by decide)
    have hP : sP.mem.get 35 = s.mem.get 35 :=
      hpres 35 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 35 = sP.mem.get 35 := by
      rw [hrun]
      exact (hpresD 35
      (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t36 : (sD.mem.get 36).toNat = 0 := by
    have : (36 : Word) = UInt16.ofNat 36 := rfl
    have hs : s.mem.get 36 = 0 := by rw [this]; exact z 4 (by decide)
    have hP : sP.mem.get 36 = s.mem.get 36 :=
      hpres 36 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 36 = sP.mem.get 36 := by
      rw [hrun]
      exact (hpresD 36
      (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t37 : (sD.mem.get 37).toNat = 0 := by
    have : (37 : Word) = UInt16.ofNat 37 := rfl
    have hs : s.mem.get 37 = 0 := by rw [this]; exact z 5 (by decide)
    have hP : sP.mem.get 37 = s.mem.get 37 :=
      hpres 37 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 37 = sP.mem.get 37 := by
      rw [hrun]
      exact (hpresD 37
      (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t38 : (sD.mem.get 38).toNat = 0 := by
    have : (38 : Word) = UInt16.ofNat 38 := rfl
    have hs : s.mem.get 38 = 0 := by rw [this]; exact z 6 (by decide)
    have hP : sP.mem.get 38 = s.mem.get 38 :=
      hpres 38 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 38 = sP.mem.get 38 := by
      rw [hrun]
      exact (hpresD 38
      (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t39 : (sD.mem.get 39).toNat = 0 := by
    have : (39 : Word) = UInt16.ofNat 39 := rfl
    have hs : s.mem.get 39 = 0 := by rw [this]; exact z 7 (by decide)
    have hP : sP.mem.get 39 = s.mem.get 39 :=
      hpres 39 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 39 = sP.mem.get 39 := by
      rw [hrun]
      exact (hpresD 39
      (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have hbufD := machineBuf_map_eight sD (48 + n) 0 0 0 0 0 0 0
    t32 t33 t34 t35 t36 t37 t38 t39
  have hspec := snprintf_1 n
  have hlen : (machineLen sD).toNat = 1 := by
    have : machineLen sD = sD.mem.get 16 := by
      simp [machineLen, addrLen]
    rw [this, hrun, g16]; decide
  refine ⟨?_, ?_, ?_, hlen⟩
  · rw [hrun]; exact hpcD
  · rw [hrun]; exact hhD
  · rw [hbufD, hspec]



theorem unsigned_digits_ndig2_done {s : Machine}
    (hat : atDigitsDefault s)
    (hS : s.mem.get 19 = 0)
    (hlo : 10 ≤ (s.mem.get 17).toNat)
    (hhi : (s.mem.get 17).toNat < 100) :
    let n := (s.mem.get 17).toNat
    let sD := runN s (placeAllSteps n + 405)
    sD.pc = 32768 ∧
    sD.halted = true ∧
    (machineBuf sD 8).map UInt16.toNat =
      (snprintfSpec [48 + n / 10, 48 + n % 10] 8).1 ∧
    (machineLen sD).toNat = 2 := by
  intro n sD
  have ⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
        hW, hC, hbuf, hcode⟩ := hat
  have hp := digits_to_p3_done (s := s) hpc hh hZ hONE hTEN hC100 hC1000
    hC10000 (digits_hcode_place hcode)
  have ⟨hpcP, hhP, hZP, hQ0, hQ1, hQ2, hQ3, hones, hQ4, hpres⟩ := hp
  let sP := runN s (placeAllSteps n)
  have hrun : sD = runN sP 405 :=
    runN_add_eq s (placeAllSteps n) 405 (placeAllSteps n + 405) rfl
  have pl := places_2 hlo hhi
  have hONEP : sP.mem.get 3 = 1 :=
    (hpres 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48P : sP.mem.get 8 = 48 :=
    (hpres 8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hK5P : sP.mem.get 2322 = 5 :=
    (hpres 2322 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hSP : sP.mem.get 19 = 0 :=
    (hpres 19 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hS
  have hWP : sP.mem.get 14 = 0 :=
    (hpres 14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hW
  have hCP : sP.mem.get 13 = 8 :=
    (hpres 13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hC
  have hClo : 0 < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hChi : (sP.mem.get 13).toNat < 32768 := by rw [hCP, word_toNat_eight]; decide
  have hLlt : (2 : Nat) < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hcodeP := p3_code_from_digits hpres hcode

  have z20 : sP.mem.get 20 = 0 := word_eq_zero (hQ0.trans pl.1)
  have z21 : sP.mem.get 21 = 0 := word_eq_zero (hQ1.trans pl.2.1)
  have z22 : sP.mem.get 22 = 0 := word_eq_zero (hQ2.trans pl.2.2.1)
  have hLlo : 0 < (sP.mem.get 23).toNat := by rw [hQ3, pl.2.2.2.1]; exact pl.2.2.2.2.1
  have hLhi : (sP.mem.get 23).toNat ≤ 9 := by rw [hQ3, pl.2.2.2.1]; exact pl.2.2.2.2.2.1
  have hd := p3_done_unsigned_ndig2_done (s := sP) hpcP hhP hZP hONEP hK48P
    hK5P hSP hWP z20 z21 z22 hLlo hLhi hClo hChi hLlt hcodeP
  have ⟨hpcD, hhD, hZD, g32, g33, g34, g29, g16, hpresD⟩ := hd
  have q3le : (sP.mem.get 23).toNat ≤ 9 := hLhi
  have onesle : (sP.mem.get 17).toNat ≤ 9 := by rw [hones]; exact pl.2.2.2.2.2.2
  have t32 : (sD.mem.get 32).toNat = 48 + n / 10 := by
    rw [hrun, g32, word_add_48 q3le, hQ3, pl.2.2.2.1]
    omega
  have t33 : (sD.mem.get 33).toNat = 48 + n % 10 := by
    rw [hrun, g33, word_add_48 onesle, hones]
    omega
  have t34 : (sD.mem.get 34).toNat = 0 := by
    rw [hrun, g34]; decide
  have z : ∀ i : Nat, i < 8 → s.mem.get (UInt16.ofNat (32 + i)) = 0 := hbuf
  have t35 : (sD.mem.get 35).toNat = 0 := by
    have : (35 : Word) = UInt16.ofNat 35 := rfl
    have hs : s.mem.get 35 = 0 := by rw [this]; exact z 3 (by decide)
    have hP : sP.mem.get 35 = s.mem.get 35 :=
      hpres 35 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 35 = sP.mem.get 35 := by
      rw [hrun]
      exact (hpresD 35
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide))
    rw [hD, hP, hs]; decide
  have t36 : (sD.mem.get 36).toNat = 0 := by
    have : (36 : Word) = UInt16.ofNat 36 := rfl
    have hs : s.mem.get 36 = 0 := by rw [this]; exact z 4 (by decide)
    have hP : sP.mem.get 36 = s.mem.get 36 :=
      hpres 36 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 36 = sP.mem.get 36 := by
      rw [hrun]
      exact (hpresD 36
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide))
    rw [hD, hP, hs]; decide
  have t37 : (sD.mem.get 37).toNat = 0 := by
    have : (37 : Word) = UInt16.ofNat 37 := rfl
    have hs : s.mem.get 37 = 0 := by rw [this]; exact z 5 (by decide)
    have hP : sP.mem.get 37 = s.mem.get 37 :=
      hpres 37 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 37 = sP.mem.get 37 := by
      rw [hrun]
      exact (hpresD 37
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide))
    rw [hD, hP, hs]; decide
  have t38 : (sD.mem.get 38).toNat = 0 := by
    have : (38 : Word) = UInt16.ofNat 38 := rfl
    have hs : s.mem.get 38 = 0 := by rw [this]; exact z 6 (by decide)
    have hP : sP.mem.get 38 = s.mem.get 38 :=
      hpres 38 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 38 = sP.mem.get 38 := by
      rw [hrun]
      exact (hpresD 38
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide))
    rw [hD, hP, hs]; decide
  have t39 : (sD.mem.get 39).toNat = 0 := by
    have : (39 : Word) = UInt16.ofNat 39 := rfl
    have hs : s.mem.get 39 = 0 := by rw [this]; exact z 7 (by decide)
    have hP : sP.mem.get 39 = s.mem.get 39 :=
      hpres 39 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 39 = sP.mem.get 39 := by
      rw [hrun]
      exact (hpresD 39
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide))
    rw [hD, hP, hs]; decide

  have hbufD := machineBuf_map_eight sD (48 + n / 10) (48 + n % 10) 0 0 0 0 0 0
    t32 t33 t34 t35 t36 t37 t38 t39
  have hspec := snprintf_2 (n / 10) (n % 10)
  have hlen : (machineLen sD).toNat = 2 := by
    have : machineLen sD = sD.mem.get 16 := by simp [machineLen, addrLen]
    rw [this, hrun, g16]; decide
  refine ⟨?_, ?_, ?_, hlen⟩
  · rw [hrun]; exact hpcD
  · rw [hrun]; exact hhD
  · rw [hbufD, hspec]

theorem unsigned_digits_ndig3_done {s : Machine}
    (hat : atDigitsDefault s)
    (hS : s.mem.get 19 = 0)
    (hlo : 100 ≤ (s.mem.get 17).toNat)
    (hhi : (s.mem.get 17).toNat < 1000) :
    let n := (s.mem.get 17).toNat
    let sD := runN s (placeAllSteps n + 462)
    sD.pc = 32768 ∧
    sD.halted = true ∧
    (machineBuf sD 8).map UInt16.toNat =
      (snprintfSpec [48 + n / 100, 48 + n / 10 % 10, 48 + n % 10] 8).1 ∧
    (machineLen sD).toNat = 3 := by
  intro n sD
  have ⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
        hW, hC, hbuf, hcode⟩ := hat
  have hp := digits_to_p3_done (s := s) hpc hh hZ hONE hTEN hC100 hC1000
    hC10000 (digits_hcode_place hcode)
  have ⟨hpcP, hhP, hZP, hQ0, hQ1, hQ2, hQ3, hones, hQ4, hpres⟩ := hp
  let sP := runN s (placeAllSteps n)
  have hrun : sD = runN sP 462 :=
    runN_add_eq s (placeAllSteps n) 462 (placeAllSteps n + 462) rfl
  have pl := places_3 hlo hhi
  have hONEP : sP.mem.get 3 = 1 :=
    (hpres 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48P : sP.mem.get 8 = 48 :=
    (hpres 8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hK5P : sP.mem.get 2322 = 5 :=
    (hpres 2322 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hSP : sP.mem.get 19 = 0 :=
    (hpres 19 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hS
  have hWP : sP.mem.get 14 = 0 :=
    (hpres 14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hW
  have hCP : sP.mem.get 13 = 8 :=
    (hpres 13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hC
  have hClo : 0 < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hChi : (sP.mem.get 13).toNat < 32768 := by rw [hCP, word_toNat_eight]; decide
  have hLlt : (3 : Nat) < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hcodeP := p3_code_from_digits hpres hcode

  have z20 : sP.mem.get 20 = 0 := word_eq_zero (hQ0.trans pl.1)
  have z21 : sP.mem.get 21 = 0 := word_eq_zero (hQ1.trans pl.2.1)
  have hLlo : 0 < (sP.mem.get 22).toNat := by rw [hQ2, pl.2.2.1]; exact pl.2.2.2.1
  have hLhi : (sP.mem.get 22).toNat ≤ 9 := by rw [hQ2, pl.2.2.1]; exact pl.2.2.2.2.1
  have hd := p3_done_unsigned_ndig3_done (s := sP) hpcP hhP hZP hONEP hK48P
    hK5P hSP hWP z20 z21 hLlo hLhi hClo hChi hLlt hcodeP
  have ⟨hpcD, hhD, hZD, g32, g33, g34, g35, g29, g16, hpresD⟩ := hd
  have q2le : (sP.mem.get 22).toNat ≤ 9 := hLhi
  have q3le : (sP.mem.get 23).toNat ≤ 9 := by rw [hQ3]; exact pl.2.2.2.2.2.1
  have onesle : (sP.mem.get 17).toNat ≤ 9 := by rw [hones]; exact pl.2.2.2.2.2.2
  have t32 : (sD.mem.get 32).toNat = 48 + n / 100 := by
    rw [hrun, g32, word_add_48 q2le, hQ2, pl.2.2.1]
    omega
  have t33 : (sD.mem.get 33).toNat = 48 + n / 10 % 10 := by
    rw [hrun, g33, word_add_48 q3le, hQ3]
    omega
  have t34 : (sD.mem.get 34).toNat = 48 + n % 10 := by
    rw [hrun, g34, word_add_48 onesle, hones]
    omega
  have t35 : (sD.mem.get 35).toNat = 0 := by
    rw [hrun, g35]; decide
  have z : ∀ i : Nat, i < 8 → s.mem.get (UInt16.ofNat (32 + i)) = 0 := hbuf
  have t36 : (sD.mem.get 36).toNat = 0 := by
    have : (36 : Word) = UInt16.ofNat 36 := rfl
    have hs : s.mem.get 36 = 0 := by rw [this]; exact z 4 (by decide)
    have hP : sP.mem.get 36 = s.mem.get 36 :=
      hpres 36 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 36 = sP.mem.get 36 := by
      rw [hrun]
      exact (hpresD 36
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t37 : (sD.mem.get 37).toNat = 0 := by
    have : (37 : Word) = UInt16.ofNat 37 := rfl
    have hs : s.mem.get 37 = 0 := by rw [this]; exact z 5 (by decide)
    have hP : sP.mem.get 37 = s.mem.get 37 :=
      hpres 37 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 37 = sP.mem.get 37 := by
      rw [hrun]
      exact (hpresD 37
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t38 : (sD.mem.get 38).toNat = 0 := by
    have : (38 : Word) = UInt16.ofNat 38 := rfl
    have hs : s.mem.get 38 = 0 := by rw [this]; exact z 6 (by decide)
    have hP : sP.mem.get 38 = s.mem.get 38 :=
      hpres 38 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 38 = sP.mem.get 38 := by
      rw [hrun]
      exact (hpresD 38
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t39 : (sD.mem.get 39).toNat = 0 := by
    have : (39 : Word) = UInt16.ofNat 39 := rfl
    have hs : s.mem.get 39 = 0 := by rw [this]; exact z 7 (by decide)
    have hP : sP.mem.get 39 = s.mem.get 39 :=
      hpres 39 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 39 = sP.mem.get 39 := by
      rw [hrun]
      exact (hpresD 39
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
    rw [hD, hP, hs]; decide

  have hbufD := machineBuf_map_eight sD (48 + n / 100) (48 + n / 10 % 10) (48 + n % 10) 0 0 0 0 0
    t32 t33 t34 t35 t36 t37 t38 t39
  have hspec := snprintf_3 (n / 100) (n / 10 % 10) (n % 10)
  have hlen : (machineLen sD).toNat = 3 := by
    have : machineLen sD = sD.mem.get 16 := by simp [machineLen, addrLen]
    rw [this, hrun, g16]; decide
  refine ⟨?_, ?_, ?_, hlen⟩
  · rw [hrun]; exact hpcD
  · rw [hrun]; exact hhD
  · rw [hbufD, hspec]

theorem unsigned_digits_ndig4_done {s : Machine}
    (hat : atDigitsDefault s)
    (hS : s.mem.get 19 = 0)
    (hlo : 1000 ≤ (s.mem.get 17).toNat)
    (hhi : (s.mem.get 17).toNat < 10000) :
    let n := (s.mem.get 17).toNat
    let sD := runN s (placeAllSteps n + 519)
    sD.pc = 32768 ∧
    sD.halted = true ∧
    (machineBuf sD 8).map UInt16.toNat =
      (snprintfSpec [48 + n / 1000, 48 + n / 100 % 10, 48 + n / 10 % 10, 48 + n % 10] 8).1 ∧
    (machineLen sD).toNat = 4 := by
  intro n sD
  have ⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
        hW, hC, hbuf, hcode⟩ := hat
  have hp := digits_to_p3_done (s := s) hpc hh hZ hONE hTEN hC100 hC1000
    hC10000 (digits_hcode_place hcode)
  have ⟨hpcP, hhP, hZP, hQ0, hQ1, hQ2, hQ3, hones, hQ4, hpres⟩ := hp
  let sP := runN s (placeAllSteps n)
  have hrun : sD = runN sP 519 :=
    runN_add_eq s (placeAllSteps n) 519 (placeAllSteps n + 519) rfl
  have pl := places_4 hlo hhi
  have hONEP : sP.mem.get 3 = 1 :=
    (hpres 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48P : sP.mem.get 8 = 48 :=
    (hpres 8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hK5P : sP.mem.get 2322 = 5 :=
    (hpres 2322 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hSP : sP.mem.get 19 = 0 :=
    (hpres 19 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hS
  have hWP : sP.mem.get 14 = 0 :=
    (hpres 14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hW
  have hCP : sP.mem.get 13 = 8 :=
    (hpres 13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hC
  have hClo : 0 < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hChi : (sP.mem.get 13).toNat < 32768 := by rw [hCP, word_toNat_eight]; decide
  have hLlt : (4 : Nat) < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hcodeP := p3_code_from_digits hpres hcode

  have z20 : sP.mem.get 20 = 0 := word_eq_zero (hQ0.trans pl.1)
  have hLlo : 0 < (sP.mem.get 21).toNat := by rw [hQ1, pl.2.1]; exact pl.2.2.1
  have hLhi : (sP.mem.get 21).toNat ≤ 9 := by rw [hQ1, pl.2.1]; exact pl.2.2.2.1
  have hd := p3_done_unsigned_ndig4_done (s := sP) hpcP hhP hZP hONEP hK48P
    hK5P hSP hWP z20 hLlo hLhi hClo hChi hLlt hcodeP
  have ⟨hpcD, hhD, hZD, g32, g33, g34, g35, g36, g29, g16, hpresD⟩ := hd
  have q1le : (sP.mem.get 21).toNat ≤ 9 := hLhi
  have q2le : (sP.mem.get 22).toNat ≤ 9 := by rw [hQ2]; exact pl.2.2.2.2.1
  have q3le : (sP.mem.get 23).toNat ≤ 9 := by rw [hQ3]; exact pl.2.2.2.2.2.1
  have onesle : (sP.mem.get 17).toNat ≤ 9 := by rw [hones]; exact pl.2.2.2.2.2.2
  have t32 : (sD.mem.get 32).toNat = 48 + n / 1000 := by
    rw [hrun, g32, word_add_48 q1le, hQ1, pl.2.1]
    omega
  have t33 : (sD.mem.get 33).toNat = 48 + n / 100 % 10 := by
    rw [hrun, g33, word_add_48 q2le, hQ2]
    omega
  have t34 : (sD.mem.get 34).toNat = 48 + n / 10 % 10 := by
    rw [hrun, g34, word_add_48 q3le, hQ3]
    omega
  have t35 : (sD.mem.get 35).toNat = 48 + n % 10 := by
    rw [hrun, g35, word_add_48 onesle, hones]
    omega
  have t36 : (sD.mem.get 36).toNat = 0 := by
    rw [hrun, g36]; decide
  have z : ∀ i : Nat, i < 8 → s.mem.get (UInt16.ofNat (32 + i)) = 0 := hbuf
  have t37 : (sD.mem.get 37).toNat = 0 := by
    have : (37 : Word) = UInt16.ofNat 37 := rfl
    have hs : s.mem.get 37 = 0 := by rw [this]; exact z 5 (by decide)
    have hP : sP.mem.get 37 = s.mem.get 37 :=
      hpres 37 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 37 = sP.mem.get 37 := by
      rw [hrun]
      exact (hpresD 37
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t38 : (sD.mem.get 38).toNat = 0 := by
    have : (38 : Word) = UInt16.ofNat 38 := rfl
    have hs : s.mem.get 38 = 0 := by rw [this]; exact z 6 (by decide)
    have hP : sP.mem.get 38 = s.mem.get 38 :=
      hpres 38 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 38 = sP.mem.get 38 := by
      rw [hrun]
      exact (hpresD 38
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t39 : (sD.mem.get 39).toNat = 0 := by
    have : (39 : Word) = UInt16.ofNat 39 := rfl
    have hs : s.mem.get 39 = 0 := by rw [this]; exact z 7 (by decide)
    have hP : sP.mem.get 39 = s.mem.get 39 :=
      hpres 39 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 39 = sP.mem.get 39 := by
      rw [hrun]
      exact (hpresD 39
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide

  have hbufD := machineBuf_map_eight sD (48 + n / 1000) (48 + n / 100 % 10)
    (48 + n / 10 % 10) (48 + n % 10) 0 0 0 0
    t32 t33 t34 t35 t36 t37 t38 t39
  have hspec := snprintf_4 (n / 1000) (n / 100 % 10) (n / 10 % 10) (n % 10)
  have hlen : (machineLen sD).toNat = 4 := by
    have : machineLen sD = sD.mem.get 16 := by simp [machineLen, addrLen]
    rw [this, hrun, g16]; decide
  refine ⟨?_, ?_, ?_, hlen⟩
  · rw [hrun]; exact hpcD
  · rw [hrun]; exact hhD
  · rw [hbufD, hspec]

theorem unsigned_digits_ndig5_done {s : Machine}
    (hat : atDigitsDefault s)
    (hS : s.mem.get 19 = 0)
    (hlo : 10000 ≤ (s.mem.get 17).toNat)
    (hhi : (s.mem.get 17).toNat < 100000) :
    let n := (s.mem.get 17).toNat
    let sD := runN s (placeAllSteps n + 576)
    sD.pc = 32768 ∧
    sD.halted = true ∧
    (machineBuf sD 8).map UInt16.toNat =
      (snprintfSpec [48 + n / 10000, 48 + n / 1000 % 10, 48 + n / 100 % 10,
        48 + n / 10 % 10, 48 + n % 10] 8).1 ∧
    (machineLen sD).toNat = 5 := by
  intro n sD
  have ⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
        hW, hC, hbuf, hcode⟩ := hat
  have hp := digits_to_p3_done (s := s) hpc hh hZ hONE hTEN hC100 hC1000
    hC10000 (digits_hcode_place hcode)
  have ⟨hpcP, hhP, hZP, hQ0, hQ1, hQ2, hQ3, hones, hQ4, hpres⟩ := hp
  let sP := runN s (placeAllSteps n)
  have hrun : sD = runN sP 576 :=
    runN_add_eq s (placeAllSteps n) 576 (placeAllSteps n + 576) rfl
  have pl := places_5 hlo hhi
  have hONEP : sP.mem.get 3 = 1 :=
    (hpres 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48P : sP.mem.get 8 = 48 :=
    (hpres 8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hK5P : sP.mem.get 2322 = 5 :=
    (hpres 2322 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hSP : sP.mem.get 19 = 0 :=
    (hpres 19 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hS
  have hWP : sP.mem.get 14 = 0 :=
    (hpres 14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hW
  have hCP : sP.mem.get 13 = 8 :=
    (hpres 13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hC
  have hClo : 0 < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hChi : (sP.mem.get 13).toNat < 32768 := by rw [hCP, word_toNat_eight]; decide
  have hLlt : (5 : Nat) < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hcodeP := p3_code_from_digits hpres hcode

  have hLlo : 0 < (sP.mem.get 20).toNat := by rw [hQ0, pl.1]; exact pl.2.1
  have hLhi : (sP.mem.get 20).toNat ≤ 9 := by rw [hQ0, pl.1]; exact pl.2.2.1
  have hd := p3_done_unsigned_ndig5_done (s := sP) hpcP hhP hZP hONEP hK48P
    hK5P hSP hWP hLlo hLhi hClo hChi hLlt hcodeP
  have ⟨hpcD, hhD, hZD, g32, g33, g34, g35, g36, g37, g29, g16, hpresD⟩ := hd
  have q0le : (sP.mem.get 20).toNat ≤ 9 := hLhi
  have q1le : (sP.mem.get 21).toNat ≤ 9 := by rw [hQ1]; exact pl.2.2.2.1
  have q2le : (sP.mem.get 22).toNat ≤ 9 := by rw [hQ2]; exact pl.2.2.2.2.1
  have q3le : (sP.mem.get 23).toNat ≤ 9 := by rw [hQ3]; exact pl.2.2.2.2.2.1
  have onesle : (sP.mem.get 17).toNat ≤ 9 := by rw [hones]; exact pl.2.2.2.2.2.2
  have t32 : (sD.mem.get 32).toNat = 48 + n / 10000 := by
    rw [hrun, g32, word_add_48 q0le, hQ0, pl.1]
    omega
  have t33 : (sD.mem.get 33).toNat = 48 + n / 1000 % 10 := by
    rw [hrun, g33, word_add_48 q1le, hQ1]
    omega
  have t34 : (sD.mem.get 34).toNat = 48 + n / 100 % 10 := by
    rw [hrun, g34, word_add_48 q2le, hQ2]
    omega
  have t35 : (sD.mem.get 35).toNat = 48 + n / 10 % 10 := by
    rw [hrun, g35, word_add_48 q3le, hQ3]
    omega
  have t36 : (sD.mem.get 36).toNat = 48 + n % 10 := by
    rw [hrun, g36, word_add_48 onesle, hones]
    omega
  have t37 : (sD.mem.get 37).toNat = 0 := by
    rw [hrun, g37]; decide
  have z : ∀ i : Nat, i < 8 → s.mem.get (UInt16.ofNat (32 + i)) = 0 := hbuf
  have t38 : (sD.mem.get 38).toNat = 0 := by
    have : (38 : Word) = UInt16.ofNat 38 := rfl
    have hs : s.mem.get 38 = 0 := by rw [this]; exact z 6 (by decide)
    have hP : sP.mem.get 38 = s.mem.get 38 :=
      hpres 38 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 38 = sP.mem.get 38 := by
      rw [hrun]
      exact (hpresD 38
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t39 : (sD.mem.get 39).toNat = 0 := by
    have : (39 : Word) = UInt16.ofNat 39 := rfl
    have hs : s.mem.get 39 = 0 := by rw [this]; exact z 7 (by decide)
    have hP : sP.mem.get 39 = s.mem.get 39 :=
      hpres 39 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 39 = sP.mem.get 39 := by
      rw [hrun]
      exact (hpresD 39
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide

  have hbufD := machineBuf_map_eight sD (48 + n / 10000) (48 + n / 1000 % 10)
    (48 + n / 100 % 10) (48 + n / 10 % 10) (48 + n % 10) 0 0 0
    t32 t33 t34 t35 t36 t37 t38 t39
  have hspec := snprintf_5 (n / 10000) (n / 1000 % 10) (n / 100 % 10)
    (n / 10 % 10) (n % 10)
  have hlen : (machineLen sD).toNat = 5 := by
    have : machineLen sD = sD.mem.get 16 := by simp [machineLen, addrLen]
    rw [this, hrun, g16]; decide
  refine ⟨?_, ?_, ?_, hlen⟩
  · rw [hrun]; exact hpcD
  · rw [hrun]; exact hhD
  · rw [hbufD, hspec]

theorem unsigned_at_digits_default (input : Word) :
    atDigitsDefault (runN (prepMachine input 0 8) 15) ∧
    (runN (prepMachine input 0 8) 15).mem.get 19 = 0 ∧
    (runN (prepMachine input 0 8) 15).mem.get 17 = input := by
  have h := unsigned_at_digits input 8
  have ⟨hpc, hh, hZ, hN, hS, hW, hC, hONE, hTEN, hC100, hC1000, hC10000,
        hK48, hK45, hK5, hcode⟩ := h
  have hbuf : ∀ i : Nat, i < 8 →
      (runN (prepMachine input 0 8) 15).mem.get (UInt16.ofNat (32 + i)) = 0 :=
    fun i hi => unsigned_at_digits_buf0 input 8 hi
  exact ⟨⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
      hW, hC, hbuf, hcode⟩, hS, hN⟩

theorem unsigned_steps_le (n : Nat) (hn : n < 65536) :
    15 + placeAllSteps n + unsignedTail n ≤ 1348 := by
  have h1 := placeAllSteps_le_of_word n hn
  have h2 := unsignedTail_le n
  omega




theorem signed_pos_at_digits_default (input : Word)
    (hpos : 0 < input.toNat) (hhi : input.toNat < 32768) :
    atDigitsDefault (runN (prepMachine input 1 8) 26) ∧
    (runN (prepMachine input 1 8) 26).mem.get 19 = 0 ∧
    (runN (prepMachine input 1 8) 26).mem.get 17 = input := by
  have h := signed_pos_at_digits input 8 hpos hhi
  have ⟨hpc, hh, hZ, hN, hS, hW, hC, hONE, hTEN, hC100, hC1000, hC10000,
        hK48, hK45, hK5, hcode⟩ := h
  have hbuf : ∀ i : Nat, i < 8 →
      (runN (prepMachine input 1 8) 26).mem.get (UInt16.ofNat (32 + i)) = 0 :=
    fun i hi => signed_pos_at_digits_buf0 input 8 hpos hhi hi
  exact ⟨⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
      hW, hC, hbuf, hcode⟩, hS, hN⟩

theorem signed_zero_at_digits_default :
    atDigitsDefault (runN (prepMachine 0 1 8) 30) ∧
    (runN (prepMachine 0 1 8) 30).mem.get 19 = 0 ∧
    (runN (prepMachine 0 1 8) 30).mem.get 17 = 0 := by
  have h := signed_zero_at_digits (8 : Word)
  have ⟨hpc, hh, hZ, hN, hS, hW, hC, hONE, hTEN, hC100, hC1000, hC10000,
        hK48, hK45, hK5, hcode⟩ := h
  have hbuf : ∀ i : Nat, i < 8 →
      (runN (prepMachine 0 1 8) 30).mem.get (UInt16.ofNat (32 + i)) = 0 :=
    fun i hi => signed_zero_at_digits_buf0 (8 : Word) hi
  exact ⟨⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
      hW, hC, hbuf, hcode⟩, hS, hN⟩

theorem signed_neg_at_digits_default (input : Word)
    (hneg : 32768 ≤ input.toNat) :
    atDigitsDefault (runN (prepMachine input 1 8) 40) ∧
    (runN (prepMachine input 1 8) 40).mem.get 19 = 1 ∧
    (runN (prepMachine input 1 8) 40).mem.get 17 = 0 - input := by
  have h := signed_neg_at_digits input 8 hneg
  have ⟨hpc, hh, hZ, hN, hS, hW, hC, hONE, hTEN, hC100, hC1000, hC10000,
        hK48, hK45, hK5, hcode⟩ := h
  have hbuf : ∀ i : Nat, i < 8 →
      (runN (prepMachine input 1 8) 40).mem.get (UInt16.ofNat (32 + i)) = 0 :=
    fun i hi => signed_neg_at_digits_buf0 input 8 hneg hi
  exact ⟨⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
      hW, hC, hbuf, hcode⟩, hS, hN⟩

theorem signed_steps_le (front n : Nat) (hn : n < 65536) (hf : front ≤ 40) :
    front + placeAllSteps n + signedTail n ≤ 1433 := by
  have h1 := placeAllSteps_le_of_word n hn
  have h2 := signedTail_le n
  omega

theorem signed_digits_ndig1_done {s : Machine}
    (hat : atDigitsDefault s)
    (hSlo0 : 0 < (s.mem.get 19).toNat)
    (hShi0 : (s.mem.get 19).toNat < 32768)
    (hn : (s.mem.get 17).toNat < 10) :
    let n := (s.mem.get 17).toNat
    let sD := runN s (placeAllSteps n + 389)
    sD.pc = 32768 ∧
    sD.halted = true ∧
    (machineBuf sD 8).map UInt16.toNat = (snprintfSpec [45, 48 + n] 8).1 ∧
    (machineLen sD).toNat = 2 := by
  intro n sD
  have ⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
        hW, hC, hbuf, hcode⟩ := hat
  have hp := digits_to_p3_done (s := s) hpc hh hZ hONE hTEN hC100 hC1000
    hC10000 (digits_hcode_place hcode)
  have ⟨hpcP, hhP, hZP, hQ0, hQ1, hQ2, hQ3, hones, hQ4, hpres⟩ := hp
  let sP := runN s (placeAllSteps n)
  have hrun : sD = runN sP 389 :=
    runN_add_eq s (placeAllSteps n) 389 (placeAllSteps n + 389) rfl
  have pl := places_1 hn
  have hONEP : sP.mem.get 3 = 1 :=
    (hpres 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48P : sP.mem.get 8 = 48 :=
    (hpres 8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hK45P : sP.mem.get 9 = 45 :=
    (hpres 9 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK45
  have hK5P : sP.mem.get 2322 = 5 :=
    (hpres 2322 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hSP : sP.mem.get 19 = s.mem.get 19 :=
    hpres 19 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have hSlo : 0 < (sP.mem.get 19).toNat := by rw [hSP]; exact hSlo0
  have hShi : (sP.mem.get 19).toNat < 32768 := by rw [hSP]; exact hShi0
  have hWP : sP.mem.get 14 = 0 :=
    (hpres 14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hW
  have hCP : sP.mem.get 13 = 8 :=
    (hpres 13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hC
  have hClo : 0 < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hChi : (sP.mem.get 13).toNat < 32768 := by rw [hCP, word_toNat_eight]; decide
  have hLlt : (2 : Nat) < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hcodeP := p3_code_from_digits hpres hcode

  have z20 : sP.mem.get 20 = 0 := word_eq_zero (hQ0.trans pl.1)
  have z21 : sP.mem.get 21 = 0 := word_eq_zero (hQ1.trans pl.2.1)
  have z22 : sP.mem.get 22 = 0 := word_eq_zero (hQ2.trans pl.2.2.1)
  have z23 : sP.mem.get 23 = 0 := word_eq_zero (hQ3.trans pl.2.2.2.1)
  have hd := p3_done_signed_ndig1_done (s := sP) hpcP hhP hZP hONEP hK48P
    hK45P hK5P hSlo hShi hWP z20 z21 z22 z23 hClo hChi hLlt hcodeP
  have ⟨hpcD, hhD, hZD, g32, g33, g34, g29, g16, hpresD⟩ := hd
  have onesle : (sP.mem.get 17).toNat ≤ 9 := by rw [hones, pl.2.2.2.2]; omega
  have t32 : (sD.mem.get 32).toNat = 45 := by rw [hrun, g32]; decide
  have t33 : (sD.mem.get 33).toNat = 48 + n := by
    rw [hrun, g33, word_add_48 onesle, hones, pl.2.2.2.2]; omega
  have t34 : (sD.mem.get 34).toNat = 0 := by rw [hrun, g34]; decide
  have z : ∀ i : Nat, i < 8 → s.mem.get (UInt16.ofNat (32 + i)) = 0 := hbuf
  have t35 : (sD.mem.get 35).toNat = 0 := by
    have : (35 : Word) = UInt16.ofNat 35 := rfl
    have hs : s.mem.get 35 = 0 := by rw [this]; exact z 3 (by decide)
    have hP : sP.mem.get 35 = s.mem.get 35 :=
      hpres 35 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 35 = sP.mem.get 35 := by
      rw [hrun]
      exact (hpresD 35
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide))
    rw [hD, hP, hs]; decide
  have t36 : (sD.mem.get 36).toNat = 0 := by
    have : (36 : Word) = UInt16.ofNat 36 := rfl
    have hs : s.mem.get 36 = 0 := by rw [this]; exact z 4 (by decide)
    have hP : sP.mem.get 36 = s.mem.get 36 :=
      hpres 36 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 36 = sP.mem.get 36 := by
      rw [hrun]
      exact (hpresD 36
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide))
    rw [hD, hP, hs]; decide
  have t37 : (sD.mem.get 37).toNat = 0 := by
    have : (37 : Word) = UInt16.ofNat 37 := rfl
    have hs : s.mem.get 37 = 0 := by rw [this]; exact z 5 (by decide)
    have hP : sP.mem.get 37 = s.mem.get 37 :=
      hpres 37 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 37 = sP.mem.get 37 := by
      rw [hrun]
      exact (hpresD 37
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide))
    rw [hD, hP, hs]; decide
  have t38 : (sD.mem.get 38).toNat = 0 := by
    have : (38 : Word) = UInt16.ofNat 38 := rfl
    have hs : s.mem.get 38 = 0 := by rw [this]; exact z 6 (by decide)
    have hP : sP.mem.get 38 = s.mem.get 38 :=
      hpres 38 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 38 = sP.mem.get 38 := by
      rw [hrun]
      exact (hpresD 38
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide))
    rw [hD, hP, hs]; decide
  have t39 : (sD.mem.get 39).toNat = 0 := by
    have : (39 : Word) = UInt16.ofNat 39 := rfl
    have hs : s.mem.get 39 = 0 := by rw [this]; exact z 7 (by decide)
    have hP : sP.mem.get 39 = s.mem.get 39 :=
      hpres 39 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 39 = sP.mem.get 39 := by
      rw [hrun]
      exact (hpresD 39
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide))
    rw [hD, hP, hs]; decide

  have hbufD := machineBuf_map_eight sD 45 (48 + n) 0 0 0 0 0 0
    t32 t33 t34 t35 t36 t37 t38 t39
  have hspec := snprintf_m1 n
  have hlen : (machineLen sD).toNat = 2 := by
    have : machineLen sD = sD.mem.get 16 := by simp [machineLen, addrLen]
    rw [this, hrun, g16]; decide
  refine ⟨?_, ?_, ?_, hlen⟩
  · rw [hrun]; exact hpcD
  · rw [hrun]; exact hhD
  · rw [hbufD, hspec]

theorem signed_digits_ndig2_done {s : Machine}
    (hat : atDigitsDefault s)
    (hSlo0 : 0 < (s.mem.get 19).toNat)
    (hShi0 : (s.mem.get 19).toNat < 32768)
    (hlo : 10 ≤ (s.mem.get 17).toNat)
    (hhi : (s.mem.get 17).toNat < 100) :
    let n := (s.mem.get 17).toNat
    let sD := runN s (placeAllSteps n + 459)
    sD.pc = 32768 ∧
    sD.halted = true ∧
    (machineBuf sD 8).map UInt16.toNat =
      (snprintfSpec [45, 48 + n / 10, 48 + n % 10] 8).1 ∧
    (machineLen sD).toNat = 3 := by
  intro n sD
  have ⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
        hW, hC, hbuf, hcode⟩ := hat
  have hp := digits_to_p3_done (s := s) hpc hh hZ hONE hTEN hC100 hC1000
    hC10000 (digits_hcode_place hcode)
  have ⟨hpcP, hhP, hZP, hQ0, hQ1, hQ2, hQ3, hones, hQ4, hpres⟩ := hp
  let sP := runN s (placeAllSteps n)
  have hrun : sD = runN sP 459 :=
    runN_add_eq s (placeAllSteps n) 459 (placeAllSteps n + 459) rfl
  have pl := places_2 hlo hhi
  have hONEP : sP.mem.get 3 = 1 :=
    (hpres 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48P : sP.mem.get 8 = 48 :=
    (hpres 8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hK45P : sP.mem.get 9 = 45 :=
    (hpres 9 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK45
  have hK5P : sP.mem.get 2322 = 5 :=
    (hpres 2322 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hSP : sP.mem.get 19 = s.mem.get 19 :=
    hpres 19 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have hSlo : 0 < (sP.mem.get 19).toNat := by rw [hSP]; exact hSlo0
  have hShi : (sP.mem.get 19).toNat < 32768 := by rw [hSP]; exact hShi0
  have hWP : sP.mem.get 14 = 0 :=
    (hpres 14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hW
  have hCP : sP.mem.get 13 = 8 :=
    (hpres 13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hC
  have hClo : 0 < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hChi : (sP.mem.get 13).toNat < 32768 := by rw [hCP, word_toNat_eight]; decide
  have hLlt : (3 : Nat) < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hcodeP := p3_code_from_digits hpres hcode

  have z20 : sP.mem.get 20 = 0 := word_eq_zero (hQ0.trans pl.1)
  have z21 : sP.mem.get 21 = 0 := word_eq_zero (hQ1.trans pl.2.1)
  have z22 : sP.mem.get 22 = 0 := word_eq_zero (hQ2.trans pl.2.2.1)
  have hLlo : 0 < (sP.mem.get 23).toNat := by rw [hQ3, pl.2.2.2.1]; exact pl.2.2.2.2.1
  have hLhi : (sP.mem.get 23).toNat ≤ 9 := by rw [hQ3, pl.2.2.2.1]; exact pl.2.2.2.2.2.1
  have hd := p3_done_signed_ndig2_done (s := sP) hpcP hhP hZP hONEP hK48P
    hK45P hK5P hSlo hShi hWP z20 z21 z22 hLlo hLhi hClo hChi hLlt hcodeP
  have ⟨hpcD, hhD, hZD, g32, g33, g34, g35, g29, g16, hpresD⟩ := hd
  have q3le : (sP.mem.get 23).toNat ≤ 9 := hLhi
  have onesle : (sP.mem.get 17).toNat ≤ 9 := by rw [hones]; exact pl.2.2.2.2.2.2
  have t32 : (sD.mem.get 32).toNat = 45 := by rw [hrun, g32]; decide
  have t33 : (sD.mem.get 33).toNat = 48 + n / 10 := by
    rw [hrun, g33, word_add_48 q3le, hQ3, pl.2.2.2.1]; omega
  have t34 : (sD.mem.get 34).toNat = 48 + n % 10 := by
    rw [hrun, g34, word_add_48 onesle, hones]; omega
  have t35 : (sD.mem.get 35).toNat = 0 := by rw [hrun, g35]; decide
  have z : ∀ i : Nat, i < 8 → s.mem.get (UInt16.ofNat (32 + i)) = 0 := hbuf
  have t36 : (sD.mem.get 36).toNat = 0 := by
    have : (36 : Word) = UInt16.ofNat 36 := rfl
    have hs : s.mem.get 36 = 0 := by rw [this]; exact z 4 (by decide)
    have hP : sP.mem.get 36 = s.mem.get 36 :=
      hpres 36 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 36 = sP.mem.get 36 := by
      rw [hrun]
      exact (hpresD 36
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t37 : (sD.mem.get 37).toNat = 0 := by
    have : (37 : Word) = UInt16.ofNat 37 := rfl
    have hs : s.mem.get 37 = 0 := by rw [this]; exact z 5 (by decide)
    have hP : sP.mem.get 37 = s.mem.get 37 :=
      hpres 37 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 37 = sP.mem.get 37 := by
      rw [hrun]
      exact (hpresD 37
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t38 : (sD.mem.get 38).toNat = 0 := by
    have : (38 : Word) = UInt16.ofNat 38 := rfl
    have hs : s.mem.get 38 = 0 := by rw [this]; exact z 6 (by decide)
    have hP : sP.mem.get 38 = s.mem.get 38 :=
      hpres 38 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 38 = sP.mem.get 38 := by
      rw [hrun]
      exact (hpresD 38
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t39 : (sD.mem.get 39).toNat = 0 := by
    have : (39 : Word) = UInt16.ofNat 39 := rfl
    have hs : s.mem.get 39 = 0 := by rw [this]; exact z 7 (by decide)
    have hP : sP.mem.get 39 = s.mem.get 39 :=
      hpres 39 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 39 = sP.mem.get 39 := by
      rw [hrun]
      exact (hpresD 39
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
    rw [hD, hP, hs]; decide

  have hbufD := machineBuf_map_eight sD 45 (48 + n / 10) (48 + n % 10) 0 0 0 0 0
    t32 t33 t34 t35 t36 t37 t38 t39
  have hspec := snprintf_m2 (n / 10) (n % 10)
  have hlen : (machineLen sD).toNat = 3 := by
    have : machineLen sD = sD.mem.get 16 := by simp [machineLen, addrLen]
    rw [this, hrun, g16]; decide
  refine ⟨?_, ?_, ?_, hlen⟩
  · rw [hrun]; exact hpcD
  · rw [hrun]; exact hhD
  · rw [hbufD, hspec]

theorem signed_digits_ndig3_done {s : Machine}
    (hat : atDigitsDefault s)
    (hSlo0 : 0 < (s.mem.get 19).toNat)
    (hShi0 : (s.mem.get 19).toNat < 32768)
    (hlo : 100 ≤ (s.mem.get 17).toNat)
    (hhi : (s.mem.get 17).toNat < 1000) :
    let n := (s.mem.get 17).toNat
    let sD := runN s (placeAllSteps n + 518)
    sD.pc = 32768 ∧
    sD.halted = true ∧
    (machineBuf sD 8).map UInt16.toNat =
      (snprintfSpec [45, 48 + n / 100, 48 + n / 10 % 10, 48 + n % 10] 8).1 ∧
    (machineLen sD).toNat = 4 := by
  intro n sD
  have ⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
        hW, hC, hbuf, hcode⟩ := hat
  have hp := digits_to_p3_done (s := s) hpc hh hZ hONE hTEN hC100 hC1000
    hC10000 (digits_hcode_place hcode)
  have ⟨hpcP, hhP, hZP, hQ0, hQ1, hQ2, hQ3, hones, hQ4, hpres⟩ := hp
  let sP := runN s (placeAllSteps n)
  have hrun : sD = runN sP 518 :=
    runN_add_eq s (placeAllSteps n) 518 (placeAllSteps n + 518) rfl
  have pl := places_3 hlo hhi
  have hONEP : sP.mem.get 3 = 1 :=
    (hpres 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48P : sP.mem.get 8 = 48 :=
    (hpres 8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hK45P : sP.mem.get 9 = 45 :=
    (hpres 9 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK45
  have hK5P : sP.mem.get 2322 = 5 :=
    (hpres 2322 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hSP : sP.mem.get 19 = s.mem.get 19 :=
    hpres 19 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have hSlo : 0 < (sP.mem.get 19).toNat := by rw [hSP]; exact hSlo0
  have hShi : (sP.mem.get 19).toNat < 32768 := by rw [hSP]; exact hShi0
  have hWP : sP.mem.get 14 = 0 :=
    (hpres 14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hW
  have hCP : sP.mem.get 13 = 8 :=
    (hpres 13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hC
  have hClo : 0 < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hChi : (sP.mem.get 13).toNat < 32768 := by rw [hCP, word_toNat_eight]; decide
  have hLlt : (4 : Nat) < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hcodeP := p3_code_from_digits hpres hcode

  have z20 : sP.mem.get 20 = 0 := word_eq_zero (hQ0.trans pl.1)
  have z21 : sP.mem.get 21 = 0 := word_eq_zero (hQ1.trans pl.2.1)
  have hLlo : 0 < (sP.mem.get 22).toNat := by rw [hQ2, pl.2.2.1]; exact pl.2.2.2.1
  have hLhi : (sP.mem.get 22).toNat ≤ 9 := by rw [hQ2, pl.2.2.1]; exact pl.2.2.2.2.1
  have hd := p3_done_signed_ndig3_done (s := sP) hpcP hhP hZP hONEP hK48P
    hK45P hK5P hSlo hShi hWP z20 z21 hLlo hLhi hClo hChi hLlt hcodeP
  have ⟨hpcD, hhD, hZD, g32, g33, g34, g35, g36, g29, g16, hpresD⟩ := hd
  have q2le : (sP.mem.get 22).toNat ≤ 9 := hLhi
  have q3le : (sP.mem.get 23).toNat ≤ 9 := by rw [hQ3]; exact pl.2.2.2.2.2.1
  have onesle : (sP.mem.get 17).toNat ≤ 9 := by rw [hones]; exact pl.2.2.2.2.2.2
  have t32 : (sD.mem.get 32).toNat = 45 := by rw [hrun, g32]; decide
  have t33 : (sD.mem.get 33).toNat = 48 + n / 100 := by
    rw [hrun, g33, word_add_48 q2le, hQ2, pl.2.2.1]; omega
  have t34 : (sD.mem.get 34).toNat = 48 + n / 10 % 10 := by
    rw [hrun, g34, word_add_48 q3le, hQ3]; omega
  have t35 : (sD.mem.get 35).toNat = 48 + n % 10 := by
    rw [hrun, g35, word_add_48 onesle, hones]; omega
  have t36 : (sD.mem.get 36).toNat = 0 := by rw [hrun, g36]; decide
  have z : ∀ i : Nat, i < 8 → s.mem.get (UInt16.ofNat (32 + i)) = 0 := hbuf
  have t37 : (sD.mem.get 37).toNat = 0 := by
    have : (37 : Word) = UInt16.ofNat 37 := rfl
    have hs : s.mem.get 37 = 0 := by rw [this]; exact z 5 (by decide)
    have hP : sP.mem.get 37 = s.mem.get 37 :=
      hpres 37 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 37 = sP.mem.get 37 := by
      rw [hrun]
      exact (hpresD 37
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t38 : (sD.mem.get 38).toNat = 0 := by
    have : (38 : Word) = UInt16.ofNat 38 := rfl
    have hs : s.mem.get 38 = 0 := by rw [this]; exact z 6 (by decide)
    have hP : sP.mem.get 38 = s.mem.get 38 :=
      hpres 38 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 38 = sP.mem.get 38 := by
      rw [hrun]
      exact (hpresD 38
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t39 : (sD.mem.get 39).toNat = 0 := by
    have : (39 : Word) = UInt16.ofNat 39 := rfl
    have hs : s.mem.get 39 = 0 := by rw [this]; exact z 7 (by decide)
    have hP : sP.mem.get 39 = s.mem.get 39 :=
      hpres 39 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 39 = sP.mem.get 39 := by
      rw [hrun]
      exact (hpresD 39
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide

  have hbufD := machineBuf_map_eight sD 45 (48 + n / 100) (48 + n / 10 % 10) (48 + n % 10) 0 0 0 0
    t32 t33 t34 t35 t36 t37 t38 t39
  have hspec := snprintf_m3 (n / 100) (n / 10 % 10) (n % 10)
  have hlen : (machineLen sD).toNat = 4 := by
    have : machineLen sD = sD.mem.get 16 := by simp [machineLen, addrLen]
    rw [this, hrun, g16]; decide
  refine ⟨?_, ?_, ?_, hlen⟩
  · rw [hrun]; exact hpcD
  · rw [hrun]; exact hhD
  · rw [hbufD, hspec]

theorem signed_digits_ndig4_done {s : Machine}
    (hat : atDigitsDefault s)
    (hSlo0 : 0 < (s.mem.get 19).toNat)
    (hShi0 : (s.mem.get 19).toNat < 32768)
    (hlo : 1000 ≤ (s.mem.get 17).toNat)
    (hhi : (s.mem.get 17).toNat < 10000) :
    let n := (s.mem.get 17).toNat
    let sD := runN s (placeAllSteps n + 577)
    sD.pc = 32768 ∧
    sD.halted = true ∧
    (machineBuf sD 8).map UInt16.toNat =
      (snprintfSpec [45, 48 + n / 1000, 48 + n / 100 % 10, 48 + n / 10 % 10, 48 + n % 10] 8).1 ∧
    (machineLen sD).toNat = 5 := by
  intro n sD
  have ⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
        hW, hC, hbuf, hcode⟩ := hat
  have hp := digits_to_p3_done (s := s) hpc hh hZ hONE hTEN hC100 hC1000
    hC10000 (digits_hcode_place hcode)
  have ⟨hpcP, hhP, hZP, hQ0, hQ1, hQ2, hQ3, hones, hQ4, hpres⟩ := hp
  let sP := runN s (placeAllSteps n)
  have hrun : sD = runN sP 577 :=
    runN_add_eq s (placeAllSteps n) 577 (placeAllSteps n + 577) rfl
  have pl := places_4 hlo hhi
  have hONEP : sP.mem.get 3 = 1 :=
    (hpres 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48P : sP.mem.get 8 = 48 :=
    (hpres 8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hK45P : sP.mem.get 9 = 45 :=
    (hpres 9 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK45
  have hK5P : sP.mem.get 2322 = 5 :=
    (hpres 2322 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hSP : sP.mem.get 19 = s.mem.get 19 :=
    hpres 19 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have hSlo : 0 < (sP.mem.get 19).toNat := by rw [hSP]; exact hSlo0
  have hShi : (sP.mem.get 19).toNat < 32768 := by rw [hSP]; exact hShi0
  have hWP : sP.mem.get 14 = 0 :=
    (hpres 14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hW
  have hCP : sP.mem.get 13 = 8 :=
    (hpres 13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hC
  have hClo : 0 < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hChi : (sP.mem.get 13).toNat < 32768 := by rw [hCP, word_toNat_eight]; decide
  have hLlt : (5 : Nat) < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hcodeP := p3_code_from_digits hpres hcode

  have z20 : sP.mem.get 20 = 0 := word_eq_zero (hQ0.trans pl.1)
  have hLlo : 0 < (sP.mem.get 21).toNat := by rw [hQ1, pl.2.1]; exact pl.2.2.1
  have hLhi : (sP.mem.get 21).toNat ≤ 9 := by rw [hQ1, pl.2.1]; exact pl.2.2.2.1
  have hd := p3_done_signed_ndig4_done (s := sP) hpcP hhP hZP hONEP hK48P
    hK45P hK5P hSlo hShi hWP z20 hLlo hLhi hClo hChi hLlt hcodeP
  have ⟨hpcD, hhD, hZD, g32, g33, g34, g35, g36, g37, g29, g16, hpresD⟩ := hd
  have q1le : (sP.mem.get 21).toNat ≤ 9 := hLhi
  have q2le : (sP.mem.get 22).toNat ≤ 9 := by rw [hQ2]; exact pl.2.2.2.2.1
  have q3le : (sP.mem.get 23).toNat ≤ 9 := by rw [hQ3]; exact pl.2.2.2.2.2.1
  have onesle : (sP.mem.get 17).toNat ≤ 9 := by rw [hones]; exact pl.2.2.2.2.2.2
  have t32 : (sD.mem.get 32).toNat = 45 := by rw [hrun, g32]; decide
  have t33 : (sD.mem.get 33).toNat = 48 + n / 1000 := by
    rw [hrun, g33, word_add_48 q1le, hQ1, pl.2.1]; omega
  have t34 : (sD.mem.get 34).toNat = 48 + n / 100 % 10 := by
    rw [hrun, g34, word_add_48 q2le, hQ2]; omega
  have t35 : (sD.mem.get 35).toNat = 48 + n / 10 % 10 := by
    rw [hrun, g35, word_add_48 q3le, hQ3]; omega
  have t36 : (sD.mem.get 36).toNat = 48 + n % 10 := by
    rw [hrun, g36, word_add_48 onesle, hones]; omega
  have t37 : (sD.mem.get 37).toNat = 0 := by rw [hrun, g37]; decide
  have z : ∀ i : Nat, i < 8 → s.mem.get (UInt16.ofNat (32 + i)) = 0 := hbuf
  have t38 : (sD.mem.get 38).toNat = 0 := by
    have : (38 : Word) = UInt16.ofNat 38 := rfl
    have hs : s.mem.get 38 = 0 := by rw [this]; exact z 6 (by decide)
    have hP : sP.mem.get 38 = s.mem.get 38 :=
      hpres 38 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 38 = sP.mem.get 38 := by
      rw [hrun]
      exact (hpresD 38
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide
  have t39 : (sD.mem.get 39).toNat = 0 := by
    have : (39 : Word) = UInt16.ofNat 39 := rfl
    have hs : s.mem.get 39 = 0 := by rw [this]; exact z 7 (by decide)
    have hP : sP.mem.get 39 = s.mem.get 39 :=
      hpres 39 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 39 = sP.mem.get 39 := by
      rw [hrun]
      exact (hpresD 39
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
    rw [hD, hP, hs]; decide

  have hbufD := machineBuf_map_eight sD 45 (48 + n / 1000) (48 + n / 100 % 10)
    (48 + n / 10 % 10) (48 + n % 10) 0 0 0
    t32 t33 t34 t35 t36 t37 t38 t39
  have hspec := snprintf_m4 (n / 1000) (n / 100 % 10) (n / 10 % 10) (n % 10)
  have hlen : (machineLen sD).toNat = 5 := by
    have : machineLen sD = sD.mem.get 16 := by simp [machineLen, addrLen]
    rw [this, hrun, g16]; decide
  refine ⟨?_, ?_, ?_, hlen⟩
  · rw [hrun]; exact hpcD
  · rw [hrun]; exact hhD
  · rw [hbufD, hspec]

theorem signed_digits_ndig5_done {s : Machine}
    (hat : atDigitsDefault s)
    (hSlo0 : 0 < (s.mem.get 19).toNat)
    (hShi0 : (s.mem.get 19).toNat < 32768)
    (hlo : 10000 ≤ (s.mem.get 17).toNat)
    (hhi : (s.mem.get 17).toNat < 100000) :
    let n := (s.mem.get 17).toNat
    let sD := runN s (placeAllSteps n + 636)
    sD.pc = 32768 ∧
    sD.halted = true ∧
    (machineBuf sD 8).map UInt16.toNat =
      (snprintfSpec [45, 48 + n / 10000, 48 + n / 1000 % 10, 48 + n / 100 % 10,
        48 + n / 10 % 10, 48 + n % 10] 8).1 ∧
    (machineLen sD).toNat = 6 := by
  intro n sD
  have ⟨hpc, hh, hZ, hONE, hTEN, hC100, hC1000, hC10000, hK48, hK45, hK5,
        hW, hC, hbuf, hcode⟩ := hat
  have hp := digits_to_p3_done (s := s) hpc hh hZ hONE hTEN hC100 hC1000
    hC10000 (digits_hcode_place hcode)
  have ⟨hpcP, hhP, hZP, hQ0, hQ1, hQ2, hQ3, hones, hQ4, hpres⟩ := hp
  let sP := runN s (placeAllSteps n)
  have hrun : sD = runN sP 636 :=
    runN_add_eq s (placeAllSteps n) 636 (placeAllSteps n + 636) rfl
  have pl := places_5 hlo hhi
  have hONEP : sP.mem.get 3 = 1 :=
    (hpres 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48P : sP.mem.get 8 = 48 :=
    (hpres 8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hK45P : sP.mem.get 9 = 45 :=
    (hpres 9 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK45
  have hK5P : sP.mem.get 2322 = 5 :=
    (hpres 2322 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hSP : sP.mem.get 19 = s.mem.get 19 :=
    hpres 19 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have hSlo : 0 < (sP.mem.get 19).toNat := by rw [hSP]; exact hSlo0
  have hShi : (sP.mem.get 19).toNat < 32768 := by rw [hSP]; exact hShi0
  have hWP : sP.mem.get 14 = 0 :=
    (hpres 14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hW
  have hCP : sP.mem.get 13 = 8 :=
    (hpres 13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hC
  have hClo : 0 < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hChi : (sP.mem.get 13).toNat < 32768 := by rw [hCP, word_toNat_eight]; decide
  have hLlt : (6 : Nat) < (sP.mem.get 13).toNat := by rw [hCP, word_toNat_eight]; decide
  have hcodeP := p3_code_from_digits hpres hcode

  have hLlo : 0 < (sP.mem.get 20).toNat := by rw [hQ0, pl.1]; exact pl.2.1
  have hLhi : (sP.mem.get 20).toNat ≤ 9 := by rw [hQ0, pl.1]; exact pl.2.2.1
  have hd := p3_done_signed_ndig5_done (s := sP) hpcP hhP hZP hONEP hK48P
    hK45P hK5P hSlo hShi hWP hLlo hLhi hClo hChi hLlt hcodeP
  have ⟨hpcD, hhD, hZD, g32, g33, g34, g35, g36, g37, g38, g29, g16, hpresD⟩ := hd
  have q0le : (sP.mem.get 20).toNat ≤ 9 := hLhi
  have q1le : (sP.mem.get 21).toNat ≤ 9 := by rw [hQ1]; exact pl.2.2.2.1
  have q2le : (sP.mem.get 22).toNat ≤ 9 := by rw [hQ2]; exact pl.2.2.2.2.1
  have q3le : (sP.mem.get 23).toNat ≤ 9 := by rw [hQ3]; exact pl.2.2.2.2.2.1
  have onesle : (sP.mem.get 17).toNat ≤ 9 := by rw [hones]; exact pl.2.2.2.2.2.2
  have t32 : (sD.mem.get 32).toNat = 45 := by rw [hrun, g32]; decide
  have t33 : (sD.mem.get 33).toNat = 48 + n / 10000 := by
    rw [hrun, g33, word_add_48 q0le, hQ0, pl.1]; omega
  have t34 : (sD.mem.get 34).toNat = 48 + n / 1000 % 10 := by
    rw [hrun, g34, word_add_48 q1le, hQ1]; omega
  have t35 : (sD.mem.get 35).toNat = 48 + n / 100 % 10 := by
    rw [hrun, g35, word_add_48 q2le, hQ2]; omega
  have t36 : (sD.mem.get 36).toNat = 48 + n / 10 % 10 := by
    rw [hrun, g36, word_add_48 q3le, hQ3]; omega
  have t37 : (sD.mem.get 37).toNat = 48 + n % 10 := by
    rw [hrun, g37, word_add_48 onesle, hones]; omega
  have t38 : (sD.mem.get 38).toNat = 0 := by rw [hrun, g38]; decide
  have z : ∀ i : Nat, i < 8 → s.mem.get (UInt16.ofNat (32 + i)) = 0 := hbuf
  have t39 : (sD.mem.get 39).toNat = 0 := by
    have : (39 : Word) = UInt16.ofNat 39 := rfl
    have hs : s.mem.get 39 = 0 := by rw [this]; exact z 7 (by decide)
    have hP : sP.mem.get 39 = s.mem.get 39 :=
      hpres 39 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hD : sD.mem.get 39 = sP.mem.get 39 := by
      rw [hrun]
      exact (hpresD 39
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide))
    rw [hD, hP, hs]; decide

  have hbufD := machineBuf_map_eight sD 45 (48 + n / 10000) (48 + n / 1000 % 10)
    (48 + n / 100 % 10) (48 + n / 10 % 10) (48 + n % 10) 0 0
    t32 t33 t34 t35 t36 t37 t38 t39
  have hspec := snprintf_m5 (n / 10000) (n / 1000 % 10) (n / 100 % 10)
    (n / 10 % 10) (n % 10)
  have hlen : (machineLen sD).toNat = 6 := by
    have : machineLen sD = sD.mem.get 16 := by simp [machineLen, addrLen]
    rw [this, hrun, g16]; decide
  refine ⟨?_, ?_, ?_, hlen⟩
  · rw [hrun]; exact hpcD
  · rw [hrun]; exact hhD
  · rw [hbufD, hspec]

end IntFmt
