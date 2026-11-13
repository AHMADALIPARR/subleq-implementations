/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Parametric execution of a P0-style 81-cell place loop.
Block lemmas, not end-to-end correctness.
-/

import IntFmt.PlaceImage

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

theorem pc_ofNat_toNat {s : Machine} (base : Nat)
    (hpc : s.pc = UInt16.ofNat base) (hb : base < 65536) :
    s.pc.toNat = base := by
  have : (UInt16.ofNat base).toNat = base :=
    UInt16.toNat_ofNat_of_lt (by
      have hsz : UInt16.size = 65536 := rfl
      rw [hsz]; exact hb)
  simpa [hpc] using this

theorem place_mem {s : Machine} {loopPc cAddr qAddr off : Nat}
    (hoff : off < 81)
    (hsum : loopPc + off < 65536)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get (UInt16.ofNat (loopPc + off)) =
      UInt16.ofNat (placeTemplate loopPc cAddr qAddr off) :=
  (hcode (loopPc + off) (by omega) (by omega)).trans (himg off hoff)

/-- `MOV N T` at the place-loop entry (4 steps). -/
theorem place_loop_mov_N_T {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat loopPc)
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = UInt16.ofNat (loopPc + 12) ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 17 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 17 = s.mem.get 17 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hb : loopPc + 81 < 65536 := by omega
  have hton : s.pc.toNat = loopPc := pc_ofNat_toNat loopPc hpc (by omega)
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (loopPc + off) :=
    word_pc_off loopPc off hpc (by omega)
  have g (off : Nat) (h1 : off < 12) :
      s.mem.get (UInt16.ofNat (loopPc + off)) =
        UInt16.ofNat (placeTemplate loopPc cAddr qAddr off) :=
    place_mem (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := off) (by omega) (by omega)
      himg (fun k hk1 hk2 => hcode k hk1 hk2)
  have m0 : s.mem.get s.pc = 18 := by
    rw [hpc]
    have ht : placeTemplate loopPc cAddr qAddr 0 = 18 := rfl
    exact (g 0 (by decide)).trans (by rw [ht]; rfl)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 1 = 18 := rfl
    exact (g 1 (by decide)).trans (by rw [ht]; rfl)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 2 = loopPc + 3 := rfl
    exact (g 2 (by decide)).trans (by rw [ht])
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 17 := by
    rw [poff 3 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 3 = 17 := rfl
    exact (g 3 (by decide)).trans (by rw [ht]; rfl)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 4 = 0 := rfl
    exact (g 4 (by decide)).trans (by rw [ht]; rfl)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 5 = loopPc + 6 := rfl
    exact (g 5 (by decide)).trans (by rw [ht])
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 6 = 0 := rfl
    exact (g 6 (by decide)).trans (by rw [ht]; rfl)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 7 = 18 := rfl
    exact (g 7 (by decide)).trans (by rw [ht]; rfl)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 8 = loopPc + 9 := rfl
    exact (g 8 (by decide)).trans (by rw [ht])
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 9 = 0 := rfl
    exact (g 9 (by decide)).trans (by rw [ht]; rfl)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 10 = 0 := rfl
    exact (g 10 (by decide)).trans (by rw [ht]; rfl)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 11 = loopPc + 12 := rfl
    exact (g 11 (by decide)).trans (by rw [ht])
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne loopPc i 18 hpc (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne loopPc i 0 hpc (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by
    rw [hton]
    have : loopPc + 81 < (32768 : Nat) := hbound
    omega
  have hpcM0 : 0 < s.pc.toNat := by
    rw [hton]
    omega
  have hmov :=
    runN_MOV (s := s) (src := 17) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = UInt16.ofNat (loopPc + 12) := hmov.1.trans (poff 12 (by decide))
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩


/-- `MOV N T` at the POS arm (`loopPc + 33`), 4 steps to `loopPc + 45`. -/
theorem place_pos_mov_N_T {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 33))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s4 := runN s 4
    s4.pc = UInt16.ofNat (loopPc + 45) ∧
    s4.halted = false ∧
    s4.mem.get 18 = s.mem.get 17 ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 17 = s.mem.get 17 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s4
  have hton : s.pc.toNat = loopPc + 33 :=
    pc_ofNat_toNat (loopPc + 33) hpc (by omega)
  have poff (off : Nat) (hoff : off ≤ 12) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (loopPc + (33 + off)) := by
    have heq : loopPc + 33 + off = loopPc + (33 + off) :=
      Nat.add_assoc loopPc 33 off
    rw [← heq]
    exact word_pc_off (loopPc + 33) off hpc (by omega)
  have g (off : Nat) (h1 : off < 12) :
      s.mem.get (UInt16.ofNat (loopPc + (33 + off))) =
        UInt16.ofNat (placeTemplate loopPc cAddr qAddr (33 + off)) :=
    place_mem (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 33 + off) (by omega) (by omega) himg hcode
  have m0 : s.mem.get s.pc = 18 := by
    rw [hpc]
    have ht : placeTemplate loopPc cAddr qAddr 33 = 18 := rfl
    exact (g 0 (by decide)).trans (by rw [ht]; rfl)
  have m1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 34 = 18 := rfl
    exact (g 1 (by decide)).trans (by rw [ht]; rfl)
  have m2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 35 = loopPc + 36 := rfl
    have hsum : loopPc + 33 + 3 = loopPc + 36 := by omega
    exact (g 2 (by decide)).trans (by rw [ht, hsum])
  have m3 : s.mem.get (s.pc + UInt16.ofNat 3) = 17 := by
    rw [poff 3 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 36 = 17 := rfl
    exact (g 3 (by decide)).trans (by rw [ht]; rfl)
  have m4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 37 = 0 := rfl
    exact (g 4 (by decide)).trans (by rw [ht]; rfl)
  have m5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 38 = loopPc + 39 := rfl
    have hsum : loopPc + 33 + 6 = loopPc + 39 := by omega
    exact (g 5 (by decide)).trans (by rw [ht, hsum])
  have m6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 39 = 0 := rfl
    exact (g 6 (by decide)).trans (by rw [ht]; rfl)
  have m7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 40 = 18 := rfl
    exact (g 7 (by decide)).trans (by rw [ht]; rfl)
  have m8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 41 = loopPc + 42 := rfl
    have hsum : loopPc + 33 + 9 = loopPc + 42 := by omega
    exact (g 8 (by decide)).trans (by rw [ht, hsum])
  have m9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 42 = 0 := rfl
    exact (g 9 (by decide)).trans (by rw [ht]; rfl)
  have m10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 43 = 0 := rfl
    exact (g 10 (by decide)).trans (by rw [ht]; rfl)
  have m11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 44 = loopPc + 45 := rfl
    have hsum : loopPc + 33 + 12 = loopPc + 45 := by omega
    exact (g 11 (by decide)).trans (by rw [ht, hsum])
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne (loopPc + 33) i 18 hpc (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne (loopPc + 33) i 0 hpc (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 12 ≤ 32768 := by
    rw [hton]; omega
  have hpcM0 : 0 < s.pc.toNat := by
    rw [hton]; omega
  have hmov :=
    runN_MOV (s := s) (src := 17) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  have hs4pc : s4.pc = UInt16.ofNat (loopPc + 45) :=
    hmov.1.trans (poff 12 (by decide))
  exact ⟨hs4pc, hmov.2.1, hmov.2.2.1, hmov.2.2.2.1, hmov.2.2.2.2.1, hmov.2.2.2.2.2⟩


theorem word_one : (1 : Word) = UInt16.ofNat 1 := rfl
theorem word_two : (2 : Word) = UInt16.ofNat 2 := rfl
theorem word_three : (3 : Word) = UInt16.ofNat 3 := rfl

/-- The three instruction cells at `loopPc + off`. -/
theorem place_enc {s : Machine} {loopPc cAddr qAddr off : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + off))
    (hoff : off + 2 < 81)
    (hbound : loopPc + 81 < (32768 : Nat))
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = UInt16.ofNat (placeTemplate loopPc cAddr qAddr off) ∧
    s.mem.get (s.pc + 1) = UInt16.ofNat (placeTemplate loopPc cAddr qAddr (off + 1)) ∧
    s.mem.get (s.pc + 2) = UInt16.ofNat (placeTemplate loopPc cAddr qAddr (off + 2)) := by
  have g (d : Nat) (hd : d < 3) :
      s.mem.get (UInt16.ofNat (loopPc + (off + d))) =
        UInt16.ofNat (placeTemplate loopPc cAddr qAddr (off + d)) :=
    place_mem (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := off + d) (by omega) (by omega) himg hcode
  have hp0 : s.mem.get s.pc = UInt16.ofNat (placeTemplate loopPc cAddr qAddr off) := by
    rw [hpc]
    have : loopPc + off = loopPc + (off + 0) := by omega
    rw [this]
    exact g 0 (by decide)
  have poff (d : Nat) (hd : d ≤ 2) :
      s.pc + UInt16.ofNat d = UInt16.ofNat (loopPc + (off + d)) := by
    have heq : loopPc + off + d = loopPc + (off + d) := Nat.add_assoc loopPc off d
    rw [← heq]
    exact word_pc_off (loopPc + off) d hpc (by omega)
  have hp1 : s.mem.get (s.pc + 1) =
      UInt16.ofNat (placeTemplate loopPc cAddr qAddr (off + 1)) := by
    rw [word_one, poff 1 (by decide)]
    exact g 1 (by decide)
  have hp2 : s.mem.get (s.pc + 2) =
      UInt16.ofNat (placeTemplate loopPc cAddr qAddr (off + 2)) := by
    rw [word_two, poff 2 (by decide)]
    exact g 2 (by decide)
  exact ⟨hp0, hp1, hp2⟩

/-- `s.pc + 3` when `s.pc = ofNat (loopPc + off)`. -/
theorem place_pc_add3 {s : Machine} (base : Nat)
    (hpc : s.pc = UInt16.ofNat base)
    (hsum : base + 3 < 65536) :
    s.pc + 3 = UInt16.ofNat (base + 3) := by
  rw [word_three]
  exact word_pc_off base 3 hpc hsum

/-- Lift an unchanged-memory hypothesis across the 81-cell code window. -/
theorem place_hcode_pres {s s' : Machine} {loopPc : Nat}
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hpres : ∀ a, a ≠ 18 → a ≠ 0 → s'.mem.get a = s.mem.get a)
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (k : Nat) (h1 : loopPc ≤ k) (h2 : k < loopPc + 81) :
    s'.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
  (hpres (UInt16.ofNat k)
    (ofNat_ne k 18 (by omega) (by decide) (by omega))
    (ofNat_ne k 0 (by omega) (by decide) (by omega))).trans
    (hcode k h1 h2)


/-- INC T at LE0 (`loopPc + 18`), 3 steps to `loopPc + 27`. -/
theorem place_le0_inc_T {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 18))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = UInt16.ofNat (loopPc + 27) ∧
    s3.halted = false ∧
    s3.mem.get 18 = s.mem.get 18 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hton : s.pc.toNat = loopPc + 18 :=
    pc_ofNat_toNat (loopPc + 18) hpc (by omega)
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (loopPc + (18 + off)) := by
    have heq : loopPc + 18 + off = loopPc + (18 + off) :=
      Nat.add_assoc loopPc 18 off
    rw [← heq]
    exact word_pc_off (loopPc + 18) off hpc (by omega)
  have g (off : Nat) (h1 : off < 9) :
      s.mem.get (UInt16.ofNat (loopPc + (18 + off))) =
        UInt16.ofNat (placeTemplate loopPc cAddr qAddr (18 + off)) :=
    place_mem (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 18 + off) (by omega) (by omega) himg hcode
  have i0 : s.mem.get s.pc = 3 := by
    rw [hpc]
    have ht : placeTemplate loopPc cAddr qAddr 18 = 3 := rfl
    exact (g 0 (by decide)).trans (by rw [ht]; rfl)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 19 = 0 := rfl
    exact (g 1 (by decide)).trans (by rw [ht]; rfl)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 20 = loopPc + 21 := rfl
    have hsum : loopPc + 18 + 3 = loopPc + 21 := by omega
    exact (g 2 (by decide)).trans (by rw [ht, hsum])
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 21 = 0 := rfl
    exact (g 3 (by decide)).trans (by rw [ht]; rfl)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 18 := by
    rw [poff 4 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 22 = 18 := rfl
    exact (g 4 (by decide)).trans (by rw [ht]; rfl)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 23 = loopPc + 24 := rfl
    have hsum : loopPc + 18 + 6 = loopPc + 24 := by omega
    exact (g 5 (by decide)).trans (by rw [ht, hsum])
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 24 = 0 := rfl
    exact (g 6 (by decide)).trans (by rw [ht]; rfl)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 25 = 0 := rfl
    exact (g 7 (by decide)).trans (by rw [ht]; rfl)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 26 = loopPc + 27 := rfl
    have hsum : loopPc + 18 + 9 = loopPc + 27 := by omega
    exact (g 8 (by decide)).trans (by rw [ht, hsum])
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne (loopPc + 18) i 18 hpc (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne (loopPc + 18) i 0 hpc (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by
    rw [hton]; omega
  have hpcM0 : 0 < s.pc.toNat := by
    rw [hton]; omega
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = UInt16.ofNat (loopPc + 27) :=
    hinc.1.trans (poff 9 (by decide))
  have hT : s3.mem.get 18 = s.mem.get 18 + 1 := by
    have : s.mem.get 18 + s.mem.get 3 = s.mem.get 18 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hT, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- INC T at LE (`loopPc + 54`), 3 steps to `loopPc + 63`. -/
theorem place_le_inc_T {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 54))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s3 := runN s 3
    s3.pc = UInt16.ofNat (loopPc + 63) ∧
    s3.halted = false ∧
    s3.mem.get 18 = s.mem.get 18 + 1 ∧
    s3.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s3.mem.get a = s.mem.get a) := by
  intro s3
  have hton : s.pc.toNat = loopPc + 54 :=
    pc_ofNat_toNat (loopPc + 54) hpc (by omega)
  have poff (off : Nat) (hoff : off ≤ 9) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (loopPc + (54 + off)) := by
    have heq : loopPc + 54 + off = loopPc + (54 + off) :=
      Nat.add_assoc loopPc 54 off
    rw [← heq]
    exact word_pc_off (loopPc + 54) off hpc (by omega)
  have g (off : Nat) (h1 : off < 9) :
      s.mem.get (UInt16.ofNat (loopPc + (54 + off))) =
        UInt16.ofNat (placeTemplate loopPc cAddr qAddr (54 + off)) :=
    place_mem (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 54 + off) (by omega) (by omega) himg hcode
  have i0 : s.mem.get s.pc = 3 := by
    rw [hpc]
    have ht : placeTemplate loopPc cAddr qAddr 54 = 3 := rfl
    exact (g 0 (by decide)).trans (by rw [ht]; rfl)
  have i1 : s.mem.get (s.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 55 = 0 := rfl
    exact (g 1 (by decide)).trans (by rw [ht]; rfl)
  have i2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 56 = loopPc + 57 := rfl
    have hsum : loopPc + 54 + 3 = loopPc + 57 := by omega
    exact (g 2 (by decide)).trans (by rw [ht, hsum])
  have i3 : s.mem.get (s.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 57 = 0 := rfl
    exact (g 3 (by decide)).trans (by rw [ht]; rfl)
  have i4 : s.mem.get (s.pc + UInt16.ofNat 4) = 18 := by
    rw [poff 4 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 58 = 18 := rfl
    exact (g 4 (by decide)).trans (by rw [ht]; rfl)
  have i5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 59 = loopPc + 60 := rfl
    have hsum : loopPc + 54 + 6 = loopPc + 60 := by omega
    exact (g 5 (by decide)).trans (by rw [ht, hsum])
  have i6 : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 60 = 0 := rfl
    exact (g 6 (by decide)).trans (by rw [ht]; rfl)
  have i7 : s.mem.get (s.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 61 = 0 := rfl
    exact (g 7 (by decide)).trans (by rw [ht]; rfl)
  have i8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 62 = loopPc + 63 := rfl
    have hsum : loopPc + 54 + 9 = loopPc + 63 := by omega
    exact (g 8 (by decide)).trans (by rw [ht, hsum])
  have hcodeD : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne (loopPc + 54) i 18 hpc (by omega) (by decide) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne (loopPc + 54) i 0 hpc (by omega) (by decide) (by omega)
  have hpcM : s.pc.toNat + 9 ≤ 32768 := by
    rw [hton]; omega
  have hpcM0 : 0 < s.pc.toNat := by
    rw [hton]; omega
  have hinc :=
    runN_ADD (s := s) (src := 3) (dst := 18)
      hh hpcM hpcM0 hZ (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  have hs3pc : s3.pc = UInt16.ofNat (loopPc + 63) :=
    hinc.1.trans (poff 9 (by decide))
  have hT : s3.mem.get 18 = s.mem.get 18 + 1 := by
    have : s.mem.get 18 + s.mem.get 3 = s.mem.get 18 + 1 := by
      rw [hONE]
    exact hinc.2.2.1.trans this
  exact ⟨hs3pc, hinc.2.1, hT, hinc.2.2.2.1, hinc.2.2.2.2⟩

/-- JLEZ T LE0 at loopPc+12. -/
theorem place_enc_jlez_12 {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 12))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = UInt16.ofNat (loopPc + 18) := by
  have enc :=
    place_enc (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 12) hpc (by omega) hbound himg hcode
  have ht0 : placeTemplate loopPc cAddr qAddr 12 = 0 := rfl
  have ht1 : placeTemplate loopPc cAddr qAddr 13 = 18 := rfl
  have ht2 : placeTemplate loopPc cAddr qAddr 14 = loopPc + 18 := rfl
  exact ⟨enc.1.trans (by rw [ht0]; rfl), enc.2.1.trans (by rw [ht1]; rfl), enc.2.2.trans (by rw [ht2])⟩

/-- JMP POS at loopPc+15. -/
theorem place_enc_jmp_15 {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 15))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = UInt16.ofNat (loopPc + 33) := by
  have enc :=
    place_enc (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 15) hpc (by omega) hbound himg hcode
  have ht0 : placeTemplate loopPc cAddr qAddr 15 = 0 := rfl
  have ht1 : placeTemplate loopPc cAddr qAddr 16 = 0 := rfl
  have ht2 : placeTemplate loopPc cAddr qAddr 17 = loopPc + 33 := rfl
  exact ⟨enc.1.trans (by rw [ht0]; rfl), enc.2.1.trans (by rw [ht1]; rfl), enc.2.2.trans (by rw [ht2])⟩

/-- JLEZ T GE at loopPc+27. -/
theorem place_enc_jlez_27 {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 27))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = UInt16.ofNat (loopPc + 66) := by
  have enc :=
    place_enc (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 27) hpc (by omega) hbound himg hcode
  have ht0 : placeTemplate loopPc cAddr qAddr 27 = 0 := rfl
  have ht1 : placeTemplate loopPc cAddr qAddr 28 = 18 := rfl
  have ht2 : placeTemplate loopPc cAddr qAddr 29 = loopPc + 66 := rfl
  exact ⟨enc.1.trans (by rw [ht0]; rfl), enc.2.1.trans (by rw [ht1]; rfl), enc.2.2.trans (by rw [ht2])⟩

/-- JMP DONE at loopPc+30. -/
theorem place_enc_jmp_30 {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 30))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = UInt16.ofNat (loopPc + 81) := by
  have enc :=
    place_enc (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 30) hpc (by omega) hbound himg hcode
  have ht0 : placeTemplate loopPc cAddr qAddr 30 = 0 := rfl
  have ht1 : placeTemplate loopPc cAddr qAddr 31 = 0 := rfl
  have ht2 : placeTemplate loopPc cAddr qAddr 32 = loopPc + 81 := rfl
  exact ⟨enc.1.trans (by rw [ht0]; rfl), enc.2.1.trans (by rw [ht1]; rfl), enc.2.2.trans (by rw [ht2])⟩

/-- SUB C T at loopPc+45. -/
theorem place_enc_sub_45 {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 45))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = UInt16.ofNat cAddr ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = UInt16.ofNat (loopPc + 48) := by
  have enc :=
    place_enc (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 45) hpc (by omega) hbound himg hcode
  have ht0 : placeTemplate loopPc cAddr qAddr 45 = cAddr := rfl
  have ht1 : placeTemplate loopPc cAddr qAddr 46 = 18 := rfl
  have ht2 : placeTemplate loopPc cAddr qAddr 47 = loopPc + 48 := rfl
  exact ⟨enc.1.trans (by rw [ht0]), enc.2.1.trans (by rw [ht1]; rfl), enc.2.2.trans (by rw [ht2])⟩

/-- JLEZ T LE at loopPc+48. -/
theorem place_enc_jlez_48 {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 48))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = UInt16.ofNat (loopPc + 54) := by
  have enc :=
    place_enc (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 48) hpc (by omega) hbound himg hcode
  have ht0 : placeTemplate loopPc cAddr qAddr 48 = 0 := rfl
  have ht1 : placeTemplate loopPc cAddr qAddr 49 = 18 := rfl
  have ht2 : placeTemplate loopPc cAddr qAddr 50 = loopPc + 54 := rfl
  exact ⟨enc.1.trans (by rw [ht0]; rfl), enc.2.1.trans (by rw [ht1]; rfl), enc.2.2.trans (by rw [ht2])⟩

/-- JMP GE at loopPc+51. -/
theorem place_enc_jmp_51 {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 51))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = UInt16.ofNat (loopPc + 66) := by
  have enc :=
    place_enc (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 51) hpc (by omega) hbound himg hcode
  have ht0 : placeTemplate loopPc cAddr qAddr 51 = 0 := rfl
  have ht1 : placeTemplate loopPc cAddr qAddr 52 = 0 := rfl
  have ht2 : placeTemplate loopPc cAddr qAddr 53 = loopPc + 66 := rfl
  exact ⟨enc.1.trans (by rw [ht0]; rfl), enc.2.1.trans (by rw [ht1]; rfl), enc.2.2.trans (by rw [ht2])⟩

/-- JLEZ T DONE at loopPc+63. -/
theorem place_enc_jlez_63 {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 63))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 18 ∧
    s.mem.get (s.pc + 2) = UInt16.ofNat (loopPc + 81) := by
  have enc :=
    place_enc (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 63) hpc (by omega) hbound himg hcode
  have ht0 : placeTemplate loopPc cAddr qAddr 63 = 0 := rfl
  have ht1 : placeTemplate loopPc cAddr qAddr 64 = 18 := rfl
  have ht2 : placeTemplate loopPc cAddr qAddr 65 = loopPc + 81 := rfl
  exact ⟨enc.1.trans (by rw [ht0]; rfl), enc.2.1.trans (by rw [ht1]; rfl), enc.2.2.trans (by rw [ht2])⟩

/-- SUB C N at loopPc+66. -/
theorem place_enc_sub_66 {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 66))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = UInt16.ofNat cAddr ∧
    s.mem.get (s.pc + 1) = 17 ∧
    s.mem.get (s.pc + 2) = UInt16.ofNat (loopPc + 69) := by
  have enc :=
    place_enc (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 66) hpc (by omega) hbound himg hcode
  have ht0 : placeTemplate loopPc cAddr qAddr 66 = cAddr := rfl
  have ht1 : placeTemplate loopPc cAddr qAddr 67 = 17 := rfl
  have ht2 : placeTemplate loopPc cAddr qAddr 68 = loopPc + 69 := rfl
  exact ⟨enc.1.trans (by rw [ht0]), enc.2.1.trans (by rw [ht1]; rfl), enc.2.2.trans (by rw [ht2])⟩

/-- JMP loopPc at loopPc+78. -/
theorem place_enc_jmp_78 {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 78))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    s.mem.get s.pc = 0 ∧
    s.mem.get (s.pc + 1) = 0 ∧
    s.mem.get (s.pc + 2) = UInt16.ofNat loopPc := by
  have enc :=
    place_enc (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 78) hpc (by omega) hbound himg hcode
  have ht0 : placeTemplate loopPc cAddr qAddr 78 = 0 := rfl
  have ht1 : placeTemplate loopPc cAddr qAddr 79 = 0 := rfl
  have ht2 : placeTemplate loopPc cAddr qAddr 80 = loopPc := rfl
  exact ⟨enc.1.trans (by rw [ht0]; rfl), enc.2.1.trans (by rw [ht1]; rfl), enc.2.2.trans (by rw [ht2])⟩


/-- `SUB C T` at `loopPc + 45` (fall through to `loopPc + 48`). -/
theorem place_sub_C_T {s : Machine} {loopPc cAddr qAddr cVal : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 45))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hcAddr : cAddr < 32)
    (hcVal : cVal < 65536)
    (hC : s.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    step s =
      { s with
        mem := s.mem.set 18 (s.mem.get 18 - UInt16.ofNat cVal)
        pc := UInt16.ofNat (loopPc + 48) } := by
  have enc :=
    place_enc_sub_45 (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hpc hbase hbound himg hcode
  have hton : s.pc.toNat = loopPc + 45 :=
    pc_ofNat_toNat (loopPc + 45) hpc (by omega)
  have hpc0 : s.pc.toNat < 32768 := by omega
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have h3 := place_pc_add3 (loopPc + 45) hpc (by omega)
    have hsum : loopPc + 45 + 3 = loopPc + 48 := by omega
    rw [enc.2.2, h3, hsum]
  have hna : UInt16.ofNat cAddr ≠ (0xFFFF : Word) :=
    ofNat_ne cAddr 0xFFFF (by omega) (by decide) (by omega)
  have hsub :=
    step_SUB (s := s) (a := UInt16.ofNat cAddr) (b := 18)
      hh hpc0 enc.1 enc.2.1 hc hna (by decide)
  have hpc' : s.pc + 3 = UInt16.ofNat (loopPc + 48) :=
    place_pc_add3 (loopPc + 45) hpc (by omega)
  have hmem : s.mem.get 18 - s.mem.get (UInt16.ofNat cAddr) =
      s.mem.get 18 - UInt16.ofNat cVal := by
    rw [hC]
  rw [hsub, hpc', hmem]

/-- `P*_GE` body: `SUB C N`, `INC Q`, `JMP loopPc` (5 steps). -/
theorem place_ge_body {s : Machine} {loopPc cAddr qAddr cVal : Nat}
    (hpc : s.pc = UInt16.ofNat (loopPc + 66))
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcAddr : cAddr < 32)
    (hqAddr : 20 ≤ qAddr)
    (hqAddr2 : qAddr < 32)
    (hcVal : 0 < cVal)
    (hcVal2 : cVal < 65536)
    (hC : s.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal)
    (hNge : cVal ≤ (s.mem.get 17).toNat)
    (hQ : (s.mem.get (UInt16.ofNat qAddr)).toNat + 1 < 65536)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s5 := runN s 5
    let n := s.mem.get 17
    let q := s.mem.get (UInt16.ofNat qAddr)
    s5.pc = UInt16.ofNat loopPc ∧
    s5.halted = false ∧
    s5.mem.get 0 = 0 ∧
    s5.mem.get 17 = n - UInt16.ofNat cVal ∧
    s5.mem.get (UInt16.ofNat qAddr) = q + 1 ∧
    (s5.mem.get 17).toNat = n.toNat - cVal ∧
    (s5.mem.get (UInt16.ofNat qAddr)).toNat = q.toNat + 1 ∧
    (∀ a, a ≠ 17 → a ≠ UInt16.ofNat qAddr → a ≠ 0 → s5.mem.get a = s.mem.get a) := by
  intro s5 n q
  have encS :=
    place_enc_sub_66 (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hpc hbase hbound himg hcode
  have hton0 : s.pc.toNat = loopPc + 66 :=
    pc_ofNat_toNat (loopPc + 66) hpc (by omega)
  have hpc0 : s.pc.toNat < 32768 := by omega
  have hc : s.mem.get (s.pc + 2) = s.pc + 3 := by
    have h3 := place_pc_add3 (loopPc + 66) hpc (by omega)
    have hsum : loopPc + 66 + 3 = loopPc + 69 := by omega
    rw [encS.2.2, h3, hsum]
  have hna : UInt16.ofNat cAddr ≠ (0xFFFF : Word) :=
    ofNat_ne cAddr 0xFFFF (by omega) (by decide) (by omega)
  have hsub :=
    step_SUB (s := s) (a := UInt16.ofNat cAddr) (b := 17)
      hh hpc0 encS.1 encS.2.1 hc hna (by decide)
  have hs1pc : (step s).pc = UInt16.ofNat (loopPc + 69) := by
    have h3 := place_pc_add3 (loopPc + 66) hpc (by omega)
    have hsum : loopPc + 66 + 3 = loopPc + 69 := by omega
    rw [hsub, h3, hsum]
  have hs1h : (step s).halted = false := by rw [hsub]; exact hh
  have hs1N : (step s).mem.get 17 = n - UInt16.ofNat cVal := by
    rw [hsub]
    have : s.mem.get 17 - s.mem.get (UInt16.ofNat cAddr) = n - UInt16.ofNat cVal := by
      simp [n, hC]
    exact (Mem.get_set_eq s.mem 17 (s.mem.get 17 - s.mem.get (UInt16.ofNat cAddr))).trans this
  have hs1Z : (step s).mem.get 0 = 0 := by
    rw [hsub]
    exact (Mem.get_set_ne s.mem 17 0
      (s.mem.get 17 - s.mem.get (UInt16.ofNat cAddr)) (by decide)).trans hZ
  have hs1ONE : (step s).mem.get 3 = 1 := by
    rw [hsub]
    exact (Mem.get_set_ne s.mem 17 3
      (s.mem.get 17 - s.mem.get (UInt16.ofNat cAddr)) (by decide)).trans hONE
  have hneQ17 : UInt16.ofNat qAddr ≠ (17 : Word) :=
    ofNat_ne qAddr 17 (by omega) (by decide) (by omega)
  have hs1Q : (step s).mem.get (UInt16.ofNat qAddr) = q := by
    rw [hsub]
    exact (Mem.get_set_ne s.mem 17 (UInt16.ofNat qAddr)
      (s.mem.get 17 - s.mem.get (UInt16.ofNat cAddr)) hneQ17).trans
      (rfl : s.mem.get (UInt16.ofNat qAddr) = q)
  have g1 (k : Nat) (h1 : loopPc ≤ k) (h2 : k < loopPc + 81) :
      (step s).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    rw [hsub]
    have hne : UInt16.ofNat k ≠ 17 :=
      ofNat_ne k 17 (by omega) (by decide) (by omega)
    exact (Mem.get_set_ne s.mem 17 (UInt16.ofNat k)
      (s.mem.get 17 - s.mem.get (UInt16.ofNat cAddr)) hne).trans
      (hcode k h1 h2)
  -- INC Q at loopPc+69
  let s1 := step s
  have hp1 : s1.pc = UInt16.ofNat (loopPc + 69) := hs1pc
  have hton1 : s1.pc.toNat = loopPc + 69 :=
    pc_ofNat_toNat (loopPc + 69) hp1 (by omega)
  have poff (off : Nat) (hoff : off ≤ 9) :
      s1.pc + UInt16.ofNat off = UInt16.ofNat (loopPc + (69 + off)) := by
    have heq : loopPc + 69 + off = loopPc + (69 + off) :=
      Nat.add_assoc loopPc 69 off
    rw [← heq]
    exact word_pc_off (loopPc + 69) off hp1 (by omega)
  have gI (off : Nat) (h1 : off < 9) :
      s1.mem.get (UInt16.ofNat (loopPc + (69 + off))) =
        UInt16.ofNat (placeTemplate loopPc cAddr qAddr (69 + off)) :=
    place_mem (s := s1) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (off := 69 + off) (by omega) (by omega) himg g1
  have i0 : s1.mem.get s1.pc = 3 := by
    rw [hp1]
    have ht : placeTemplate loopPc cAddr qAddr 69 = 3 := rfl
    exact (gI 0 (by decide)).trans (by rw [ht]; rfl)
  have i1 : s1.mem.get (s1.pc + UInt16.ofNat 1) = 0 := by
    rw [poff 1 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 70 = 0 := rfl
    exact (gI 1 (by decide)).trans (by rw [ht]; rfl)
  have i2 : s1.mem.get (s1.pc + UInt16.ofNat 2) = s1.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 71 = loopPc + 72 := rfl
    have hsum : loopPc + 69 + 3 = loopPc + 72 := by omega
    exact (gI 2 (by decide)).trans (by rw [ht, hsum])
  have i3 : s1.mem.get (s1.pc + UInt16.ofNat 3) = 0 := by
    rw [poff 3 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 72 = 0 := rfl
    exact (gI 3 (by decide)).trans (by rw [ht]; rfl)
  have i4 : s1.mem.get (s1.pc + UInt16.ofNat 4) = UInt16.ofNat qAddr := by
    rw [poff 4 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 73 = qAddr := rfl
    exact (gI 4 (by decide)).trans (by rw [ht])
  have i5 : s1.mem.get (s1.pc + UInt16.ofNat 5) = s1.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 74 = loopPc + 75 := rfl
    have hsum : loopPc + 69 + 6 = loopPc + 75 := by omega
    exact (gI 5 (by decide)).trans (by rw [ht, hsum])
  have i6 : s1.mem.get (s1.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 75 = 0 := rfl
    exact (gI 6 (by decide)).trans (by rw [ht]; rfl)
  have i7 : s1.mem.get (s1.pc + UInt16.ofNat 7) = 0 := by
    rw [poff 7 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 76 = 0 := rfl
    exact (gI 7 (by decide)).trans (by rw [ht]; rfl)
  have i8 : s1.mem.get (s1.pc + UInt16.ofNat 8) = s1.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have ht : placeTemplate loopPc cAddr qAddr 77 = loopPc + 78 := rfl
    have hsum : loopPc + 69 + 9 = loopPc + 78 := by omega
    exact (gI 8 (by decide)).trans (by rw [ht, hsum])
  have hcodeD : ∀ i : Nat, i < 9 → s1.pc + UInt16.ofNat i ≠ UInt16.ofNat qAddr := by
    intro i hi
    exact pc_off_ne (loopPc + 69) i qAddr hp1 (by omega) (by omega) (by omega)
  have hcodeZ : ∀ i : Nat, i < 9 → s1.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne (loopPc + 69) i 0 hp1 (by omega) (by decide) (by omega)
  have hpc1b : s1.pc.toNat + 9 ≤ 32768 := by rw [hton1]; omega
  have hpc10 : 0 < s1.pc.toNat := by rw [hton1]; omega
  have hqZ : UInt16.ofNat qAddr ≠ (0 : Word) :=
    ofNat_ne qAddr 0 (by omega) (by decide) (by omega)
  have hqN : UInt16.ofNat qAddr ≠ (0xFFFF : Word) :=
    ofNat_ne qAddr 0xFFFF (by omega) (by decide) (by omega)
  have hinc :=
    runN_ADD (s := s1) (src := 3) (dst := UInt16.ofNat qAddr)
      hs1h hpc1b hpc10 hs1Z hqZ (by decide) hqN
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD hcodeZ
  let s4 := runN s1 3
  have hs4pc : s4.pc = UInt16.ofNat (loopPc + 78) :=
    hinc.1.trans (poff 9 (by decide))
  have hs4h : s4.halted = false := hinc.2.1
  have hs4Q : s4.mem.get (UInt16.ofNat qAddr) = q + 1 := by
    have : s1.mem.get (UInt16.ofNat qAddr) + s1.mem.get 3 = q + 1 := by
      rw [hs1Q, hs1ONE]
    exact hinc.2.2.1.trans this
  have hs4Z : s4.mem.get 0 = 0 := hinc.2.2.2.1
  have hpres4 := hinc.2.2.2.2
  have hs4N : s4.mem.get 17 = n - UInt16.ofNat cVal :=
    (hpres4 17 (ofNat_ne 17 qAddr (by decide) (by omega) (by omega)) (by decide)).trans hs1N
  have g4 (k : Nat) (h1 : loopPc ≤ k) (h2 : k < loopPc + 81) :
      s4.mem.get (UInt16.ofNat k) = intfmtImage[k]! :=
    (hpres4 (UInt16.ofNat k)
      (ofNat_ne k qAddr (by omega) (by omega) (by omega))
      (ofNat_ne k 0 (by omega) (by decide) (by omega))).trans
      (g1 k h1 h2)
  -- JMP loopPc at loopPc+78
  have encJ :=
    place_enc_jmp_78 (s := s4) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs4pc hbase hbound himg g4
  have hton4 : s4.pc.toNat = loopPc + 78 :=
    pc_ofNat_toNat (loopPc + 78) hs4pc (by omega)
  have hpc4 : s4.pc.toNat < 32768 := by omega
  have hjmp :=
    step_JMP (s := s4) (dest := UInt16.ofNat loopPc) hs4h hpc4 hs4Z
      encJ.1 encJ.2.1 encJ.2.2
  have hrun : s5 = step s4 := by
    have h5 : runN s 5 = runN s1 4 := runN_succ_go s 4 hh hpc0
    have h4 : runN s1 4 = runN s4 1 := runN_add_eq s1 3 1 4 (by decide)
    have h1 := runN_one s4 hs4h hpc4
    exact h5.trans (h4.trans h1)
  have hs5pc : s5.pc = UInt16.ofNat loopPc := by rw [hrun, hjmp]
  have hs5h : s5.halted = false := by rw [hrun, hjmp]; exact hs4h
  have hs5Z : s5.mem.get 0 = 0 := by rw [hrun, hjmp]; exact hs4Z
  have hs5N : s5.mem.get 17 = n - UInt16.ofNat cVal := by rw [hrun, hjmp]; exact hs4N
  have hs5Q : s5.mem.get (UInt16.ofNat qAddr) = q + 1 := by rw [hrun, hjmp]; exact hs4Q
  have hNton : (s5.mem.get 17).toNat = n.toNat - cVal := by
    rw [hs5N]
    have hCton : (UInt16.ofNat cVal).toNat = cVal := word_ofNat_toNat cVal hcVal2
    have hn : n = s.mem.get 17 := rfl
    have hge : (UInt16.ofNat cVal).toNat ≤ n.toNat := by
      rw [hCton]; exact hNge
    have := word_sub_ge n (UInt16.ofNat cVal) hge
    simpa [hCton] using this
  have hQton : (s5.mem.get (UInt16.ofNat qAddr)).toNat = q.toNat + 1 := by
    rw [hs5Q]
    exact word_add_one_toNat q hQ
  have hpres : ∀ a, a ≠ 17 → a ≠ UInt16.ofNat qAddr → a ≠ 0 →
      s5.mem.get a = s.mem.get a := by
    intro a ha17 haQ ha0
    have h1 : s5.mem.get a = s1.mem.get a := by
      rw [hrun, hjmp]
      exact hpres4 a haQ ha0
    have h0 : s1.mem.get a = s.mem.get a := by
      rw [show s1 = step s from rfl, hsub]
      exact Mem.get_set_ne s.mem 17 a
        (s.mem.get 17 - s.mem.get (UInt16.ofNat cAddr)) ha17
    exact h1.trans h0
  exact ⟨hs5pc, hs5h, hs5Z, hs5N, hs5Q, hNton, hQton, hpres⟩


/-- From the loop entry, a positive `N` with a clear high bit
(`0 < N < 32768`) falls through to POS in 6 steps. `N` is unchanged. -/
theorem place_goto_pos {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat loopPc)
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hN0 : 0 < (s.mem.get 17).toNat)
    (hNhi : (s.mem.get 17).toNat < 32768)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s6 := runN s 6
    s6.pc = UInt16.ofNat (loopPc + 33) ∧
    s6.halted = false ∧
    s6.mem.get 18 = s.mem.get 17 ∧
    s6.mem.get 17 = s.mem.get 17 ∧
    s6.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a) := by
  intro s6
  have hmov :=
    place_loop_mov_N_T (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hpc hbase hbound hh hZ himg hcode
  let s4 := runN s 4
  have hs4pc : s4.pc = UInt16.ofNat (loopPc + 12) := hmov.1
  have hs4h := hmov.2.1
  have hT4 : s4.mem.get 18 = s.mem.get 17 := hmov.2.2.1
  have hZ4 := hmov.2.2.2.1
  have hpres4 := hmov.2.2.2.2.2
  have g4 :=
    place_hcode_pres (s := s) (s' := s4) (loopPc := loopPc)
      hbase hbound hpres4 hcode
  have enc :=
    place_enc_jlez_12 (s := s4) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs4pc hbase hbound himg g4
  have hton4 : s4.pc.toNat = loopPc + 12 :=
    pc_ofNat_toNat (loopPc + 12) hs4pc (by omega)
  have hpc4 : s4.pc.toNat < 32768 := by omega
  have hjlez :=
    step_JLEZ (s := s4) (x := 18) (dest := UInt16.ofNat (loopPc + 18))
      hs4h hpc4 hZ4 enc.1 enc.2.1 enc.2.2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hT4]; exact le0_pos hN0 hNhi
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := s4.pc + 3 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then UInt16.ofNat (loopPc + 18) else s4.pc + 3) = s4.pc + 3 := by
      simp [hle]
    rw [hjlez, hif]
  have hs5pc : (step s4).pc = UInt16.ofNat (loopPc + 15) := by
    have h3 := place_pc_add3 (loopPc + 12) hs4pc (by omega)
    have hsum : loopPc + 12 + 3 = loopPc + 15 := by omega
    rw [hs5eq, h3, hsum]
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by rw [hs5eq]; exact hZ4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact hpres4 a ha18 ha0
  have g5 :=
    place_hcode_pres (s := s) (s' := step s4) (loopPc := loopPc)
      hbase hbound hpres5 hcode
  have encJ :=
    place_enc_jmp_15 (s := step s4) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs5pc hbase hbound himg g5
  have hton5 : (step s4).pc.toNat = loopPc + 15 :=
    pc_ofNat_toNat (loopPc + 15) hs5pc (by omega)
  have hpc5 : (step s4).pc.toNat < 32768 := by omega
  have hjmp :=
    step_JMP (s := step s4) (dest := UInt16.ofNat (loopPc + 33))
      hs5h hpc5 hs5Z encJ.1 encJ.2.1 encJ.2.2
  have hrun : s6 = step (step s4) := by
    have h6 : runN s 6 = runN s4 2 := runN_add_eq s 4 2 6 (by decide)
    have h2 := runN_2_steps s4 hs4h hpc4 hs5h hpc5
    exact h6.trans h2
  have hs6pc : s6.pc = UInt16.ofNat (loopPc + 33) := by rw [hrun, hjmp]
  have hs6h : s6.halted = false := by rw [hrun, hjmp]; exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    have hmem : (step (step s4)).mem = (step s4).mem := by rw [hjmp]
    rw [hrun, hmem, hs5eq]; exact hZ4
  have hs6T : s6.mem.get 18 = s.mem.get 17 := by
    have hmem : (step (step s4)).mem = (step s4).mem := by rw [hjmp]
    rw [hrun, hmem, hs5eq]; exact hT4
  have hs6N : s6.mem.get 17 = s.mem.get 17 := by
    have hmem : (step (step s4)).mem = (step s4).mem := by rw [hjmp]
    rw [hrun, hmem, hs5eq]; exact hmov.2.2.2.2.1
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have hmem : (step (step s4)).mem = (step s4).mem := by rw [hjmp]
    rw [hrun, hmem]
    exact hpres5 a ha18 ha0
  exact ⟨hs6pc, hs6h, hs6T, hs6N, hs6Z, hpres⟩

/-- `N` has the high bit set (`N.toNat ≥ 32768`) at the loop entry: the
LE0 arm reaches GE in 9 steps without changing `N` or `Q`. -/
theorem place_to_ge_hi {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat loopPc)
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hN : 32768 ≤ (s.mem.get 17).toNat)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s9 := runN s 9
    s9.pc = UInt16.ofNat (loopPc + 66) ∧
    s9.halted = false ∧
    s9.mem.get 17 = s.mem.get 17 ∧
    s9.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a) := by
  intro s9
  have hmov :=
    place_loop_mov_N_T (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hpc hbase hbound hh hZ himg hcode
  let s4 := runN s 4
  have hs4pc : s4.pc = UInt16.ofNat (loopPc + 12) := hmov.1
  have hs4h := hmov.2.1
  have hT4 : s4.mem.get 18 = s.mem.get 17 := hmov.2.2.1
  have hZ4 := hmov.2.2.2.1
  have hpres4 := hmov.2.2.2.2.2
  have g4 :=
    place_hcode_pres (s := s) (s' := s4) (loopPc := loopPc)
      hbase hbound hpres4 hcode
  have enc :=
    place_enc_jlez_12 (s := s4) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs4pc hbase hbound himg g4
  have hton4 : s4.pc.toNat = loopPc + 12 :=
    pc_ofNat_toNat (loopPc + 12) hs4pc (by omega)
  have hpc4 : s4.pc.toNat < 32768 := by omega
  have hjlez :=
    step_JLEZ (s := s4) (x := 18) (dest := UInt16.ofNat (loopPc + 18))
      hs4h hpc4 hZ4 enc.1 enc.2.1 enc.2.2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = true := by
    have : le0 (s4.mem.get 18) = true := by
      rw [hT4]; exact le0_hi hN
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := UInt16.ofNat (loopPc + 18) } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then UInt16.ofNat (loopPc + 18) else s4.pc + 3) =
          UInt16.ofNat (loopPc + 18) := by
      simp [hle]
    rw [hjlez, hif]
  have hs5pc : (step s4).pc = UInt16.ofNat (loopPc + 18) := by rw [hs5eq]
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by rw [hs5eq]; exact hZ4
  have hs5ONE : (step s4).mem.get 3 = 1 := by
    rw [hs5eq]; exact (hpres4 3 (by decide) (by decide)).trans hONE
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact hpres4 a ha18 ha0
  have hT5 : (step s4).mem.get 18 = s.mem.get 17 := by
    rw [hs5eq]; exact hT4
  let s5 := step s4
  have g5 :=
    place_hcode_pres (s := s) (s' := s5) (loopPc := loopPc)
      hbase hbound hpres5 hcode
  have hinc :=
    place_le0_inc_T (s := s5) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs5pc hbase hbound hs5h hs5Z hs5ONE himg g5
  let s8 := runN s5 3
  have hs8pc : s8.pc = UInt16.ofNat (loopPc + 27) := hinc.1
  have hs8h := hinc.2.1
  have hT8 : s8.mem.get 18 = s.mem.get 17 + 1 := hinc.2.2.1.trans (by rw [hT5])
  have hZ8 := hinc.2.2.2.1
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres5 a ha18 ha0)
  have g8 :=
    place_hcode_pres (s := s) (s' := s8) (loopPc := loopPc)
      hbase hbound hpres8 hcode
  have enc2 :=
    place_enc_jlez_27 (s := s8) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs8pc hbase hbound himg g8
  have hton8 : s8.pc.toNat = loopPc + 27 :=
    pc_ofNat_toNat (loopPc + 27) hs8pc (by omega)
  have hpc8 : s8.pc.toNat < 32768 := by omega
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := UInt16.ofNat (loopPc + 66))
      hs8h hpc8 hZ8 enc2.1 enc2.2.1 enc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = true := by
    have : le0 (s8.mem.get 18) = true := by
      rw [hT8]
      by_cases hmax : (s.mem.get 17).toNat = 65535
      · have hw : s.mem.get 17 + 1 = 0 := word_add_one_wrap (s.mem.get 17) hmax
        rw [hw]; exact le0_zero
      · have hbd : (s.mem.get 17).toNat + 1 < 65536 := by
          have hlt := UInt16.toNat_lt_size (s.mem.get 17)
          have : UInt16.size = 65536 := rfl
          omega
        have hton := word_add_one_toNat (s.mem.get 17) hbd
        have hhi : 32768 ≤ (s.mem.get 17 + 1).toNat := by
          rw [hton]; omega
        exact le0_hi hhi
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := UInt16.ofNat (loopPc + 66) } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then UInt16.ofNat (loopPc + 66) else s8.pc + 3) =
          UInt16.ofNat (loopPc + 66) := by
      simp [hle2]
    rw [hjlez2, hif]
  have hrun : s9 = step s8 := by
    have h9 : runN s 9 = runN s4 5 := runN_add_eq s 4 5 9 (by decide)
    have h5 : runN s4 5 = runN s5 4 := runN_succ_go s4 4 hs4h hpc4
    have h4 : runN s5 4 = runN s8 1 := runN_add_eq s5 3 1 4 (by decide)
    have h1 := runN_one s8 hs8h hpc8
    exact h9.trans (h5.trans (h4.trans h1))
  have hs9pc : s9.pc = UInt16.ofNat (loopPc + 66) := by rw [hrun, hs9eq]
  have hs9h : s9.halted = false := by rw [hrun, hs9eq]; exact hs8h
  have hs9Z : s9.mem.get 0 = 0 := by rw [hrun, hs9eq]; exact hZ8
  have hs9N : s9.mem.get 17 = s.mem.get 17 := by
    rw [hrun, hs9eq]; exact hpres8 17 (by decide) (by decide)
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hs9eq]
    exact hpres8 a ha18 ha0
  exact ⟨hs9pc, hs9h, hs9N, hs9Z, hpres⟩

/-- `N = 0` at the loop entry: the LE0 arm exits to DONE in 10 steps
without changing `N` or `Q`. -/
theorem place_exit_zero {s : Machine} {loopPc cAddr qAddr : Nat}
    (hpc : s.pc = UInt16.ofNat loopPc)
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hN : s.mem.get 17 = 0)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s10 := runN s 10
    s10.pc = UInt16.ofNat (loopPc + 81) ∧
    s10.halted = false ∧
    s10.mem.get 17 = 0 ∧
    s10.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a) := by
  intro s10
  have hmov :=
    place_loop_mov_N_T (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hpc hbase hbound hh hZ himg hcode
  let s4 := runN s 4
  have hs4pc : s4.pc = UInt16.ofNat (loopPc + 12) := hmov.1
  have hs4h := hmov.2.1
  have hT4 : s4.mem.get 18 = 0 := hmov.2.2.1.trans hN
  have hZ4 := hmov.2.2.2.1
  have hpres4 := hmov.2.2.2.2.2
  have g4 :=
    place_hcode_pres (s := s) (s' := s4) (loopPc := loopPc)
      hbase hbound hpres4 hcode
  have enc :=
    place_enc_jlez_12 (s := s4) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs4pc hbase hbound himg g4
  have hton4 : s4.pc.toNat = loopPc + 12 :=
    pc_ofNat_toNat (loopPc + 12) hs4pc (by omega)
  have hpc4 : s4.pc.toNat < 32768 := by omega
  have hjlez :=
    step_JLEZ (s := s4) (x := 18) (dest := UInt16.ofNat (loopPc + 18))
      hs4h hpc4 hZ4 enc.1 enc.2.1 enc.2.2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = true := by
    have : le0 (s4.mem.get 18) = true := by
      rw [hT4]; exact le0_zero
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := UInt16.ofNat (loopPc + 18) } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18
          then UInt16.ofNat (loopPc + 18) else s4.pc + 3) =
          UInt16.ofNat (loopPc + 18) := by
      simp [hle]
    rw [hjlez, hif]
  have hs5pc : (step s4).pc = UInt16.ofNat (loopPc + 18) := by rw [hs5eq]
  have hs5h : (step s4).halted = false := by rw [hs5eq]; exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by rw [hs5eq]; exact hZ4
  have hs5ONE : (step s4).mem.get 3 = 1 := by
    rw [hs5eq]; exact (hpres4 3 (by decide) (by decide)).trans hONE
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact hpres4 a ha18 ha0
  have hT5 : (step s4).mem.get 18 = 0 := by rw [hs5eq]; exact hT4
  let s5 := step s4
  have g5 :=
    place_hcode_pres (s := s) (s' := s5) (loopPc := loopPc)
      hbase hbound hpres5 hcode
  have hinc :=
    place_le0_inc_T (s := s5) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs5pc hbase hbound hs5h hs5Z hs5ONE himg g5
  let s8 := runN s5 3
  have hs8pc : s8.pc = UInt16.ofNat (loopPc + 27) := hinc.1
  have hs8h := hinc.2.1
  have hT8 : s8.mem.get 18 = (1 : Word) := by
    have : (0 : Word) + 1 = 1 := rfl
    exact (hinc.2.2.1.trans (by rw [hT5])).trans this
  have hZ8 := hinc.2.2.2.1
  have hpres8 : ∀ a, a ≠ 18 → a ≠ 0 → s8.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres5 a ha18 ha0)
  have g8 :=
    place_hcode_pres (s := s) (s' := s8) (loopPc := loopPc)
      hbase hbound hpres8 hcode
  have enc2 :=
    place_enc_jlez_27 (s := s8) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs8pc hbase hbound himg g8
  have hton8 : s8.pc.toNat = loopPc + 27 :=
    pc_ofNat_toNat (loopPc + 27) hs8pc (by omega)
  have hpc8 : s8.pc.toNat < 32768 := by omega
  have hjlez2 :=
    step_JLEZ (s := s8) (x := 18) (dest := UInt16.ofNat (loopPc + 66))
      hs8h hpc8 hZ8 enc2.1 enc2.2.1 enc2.2.2 (by decide)
  have hle2 : (s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18) = false := by
    have : le0 (s8.mem.get 18) = false := by
      rw [hT8]
      exact le0_pos (by decide : 0 < (1 : Word).toNat)
        (by decide : (1 : Word).toNat < 32768)
    simpa [le0] using this
  have hs9eq : step s8 = { s8 with pc := s8.pc + 3 } := by
    have hif :
        (if s8.mem.get 18 = 0 || 0x8000 ≤ s8.mem.get 18
          then UInt16.ofNat (loopPc + 66) else s8.pc + 3) = s8.pc + 3 := by
      simp [hle2]
    rw [hjlez2, hif]
  have hs9pc : (step s8).pc = UInt16.ofNat (loopPc + 30) := by
    have h3 := place_pc_add3 (loopPc + 27) hs8pc (by omega)
    have hsum : loopPc + 27 + 3 = loopPc + 30 := by omega
    rw [hs9eq, h3, hsum]
  have hs9h : (step s8).halted = false := by rw [hs9eq]; exact hs8h
  have hs9Z : (step s8).mem.get 0 = 0 := by rw [hs9eq]; exact hZ8
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → (step s8).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs9eq]
    exact hpres8 a ha18 ha0
  have g9 :=
    place_hcode_pres (s := s) (s' := step s8) (loopPc := loopPc)
      hbase hbound hpres9 hcode
  have encJ :=
    place_enc_jmp_30 (s := step s8) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs9pc hbase hbound himg g9
  have hton9 : (step s8).pc.toNat = loopPc + 30 :=
    pc_ofNat_toNat (loopPc + 30) hs9pc (by omega)
  have hpc9 : (step s8).pc.toNat < 32768 := by omega
  have hjmp :=
    step_JMP (s := step s8) (dest := UInt16.ofNat (loopPc + 81))
      hs9h hpc9 hs9Z encJ.1 encJ.2.1 encJ.2.2
  have hrun : s10 = step (step s8) := by
    have h10 : runN s 10 = runN s4 6 := runN_add_eq s 4 6 10 (by decide)
    have h6 : runN s4 6 = runN s5 5 := runN_succ_go s4 5 hs4h hpc4
    have h5 : runN s5 5 = runN s8 2 := runN_add_eq s5 3 2 5 (by decide)
    have h2 := runN_2_steps s8 hs8h hpc8 hs9h hpc9
    exact h10.trans (h6.trans (h5.trans h2))
  have hs10pc : s10.pc = UInt16.ofNat (loopPc + 81) := by rw [hrun, hjmp]
  have hs10h : s10.halted = false := by rw [hrun, hjmp]; exact hs9h
  have hs10Z : s10.mem.get 0 = 0 := by
    have hmem : (step (step s8)).mem = (step s8).mem := by rw [hjmp]
    rw [hrun, hmem, hs9eq]; exact hZ8
  have hs10N : s10.mem.get 17 = 0 := by
    have hmem : (step (step s8)).mem = (step s8).mem := by rw [hjmp]
    rw [hrun, hmem, hs9eq]
    exact (hpres8 17 (by decide) (by decide)).trans hN
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have hmem : (step (step s8)).mem = (step s8).mem := by rw [hjmp]
    rw [hrun, hmem]
    exact hpres9 a ha18 ha0
  exact ⟨hs10pc, hs10h, hs10N, hs10Z, hpres⟩


/-- `0 < N < c` at the loop entry: the POS/LE arm exits to DONE in 16
steps without changing `N` or `Q`. -/
theorem place_exit_small {s : Machine} {loopPc cAddr qAddr cVal : Nat}
    (hpc : s.pc = UInt16.ofNat loopPc)
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcAddr0 : 0 < cAddr)
    (hcAddr : cAddr < 16)
    (hcVal : 0 < cVal)
    (hcVal2 : cVal ≤ 32768)
    (hC : s.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal)
    (hN0 : 0 < (s.mem.get 17).toNat)
    (hN : (s.mem.get 17).toNat < cVal)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s16 := runN s 16
    s16.pc = UInt16.ofNat (loopPc + 81) ∧
    s16.halted = false ∧
    s16.mem.get 17 = s.mem.get 17 ∧
    s16.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a) := by
  intro s16
  have hNhi : (s.mem.get 17).toNat < 32768 :=
    Nat.lt_of_lt_of_le hN hcVal2
  have hgo :=
    place_goto_pos (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hpc hbase hbound hh hZ hN0 hNhi himg hcode
  let s6 := runN s 6
  have hs6pc : s6.pc = UInt16.ofNat (loopPc + 33) := hgo.1
  have hs6h := hgo.2.1
  have hZ6 := hgo.2.2.2.2.1
  have hpres6 := hgo.2.2.2.2.2
  have hs6ONE : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have hs6C : s6.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal :=
    (hpres6 (UInt16.ofNat cAddr)
      (ofNat_ne cAddr 18 (by omega) (by decide) (by omega))
      (ofNat_ne cAddr 0 (by omega) (by decide) (by omega))).trans hC
  have g6 :=
    place_hcode_pres (s := s) (s' := s6) (loopPc := loopPc)
      hbase hbound hpres6 hcode
  have hmov :=
    place_pos_mov_N_T (s := s6) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs6pc hbase hbound hs6h hZ6 himg g6
  let s10 := runN s6 4
  have hs10pc : s10.pc = UInt16.ofNat (loopPc + 45) := hmov.1
  have hs10h := hmov.2.1
  have hT10 : s10.mem.get 18 = s.mem.get 17 :=
    hmov.2.2.1.trans (hgo.2.2.2.1)
  have hZ10 := hmov.2.2.2.1
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hmov.2.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hs10C : s10.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal :=
    (hpres10 (UInt16.ofNat cAddr)
      (ofNat_ne cAddr 18 (by omega) (by decide) (by omega))
      (ofNat_ne cAddr 0 (by omega) (by decide) (by omega))).trans hC
  have hs10ONE : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have g10 :=
    place_hcode_pres (s := s) (s' := s10) (loopPc := loopPc)
      hbase hbound hpres10 hcode
  have hcAddr32 : cAddr < 32 := Nat.lt_trans hcAddr (by decide)
  have hcValb : cVal < 65536 := Nat.lt_of_le_of_lt hcVal2 (by decide)
  have hsub :=
    place_sub_C_T (s := s10) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (cVal := cVal) hs10pc hbase hbound hs10h hcAddr32 hcValb hs10C himg g10
  have hs11pc : (step s10).pc = UInt16.ofNat (loopPc + 48) := by rw [hsub]
  have hs11h : (step s10).halted = false := by rw [hsub]; exact hs10h
  have hs11Z : (step s10).mem.get 0 = 0 := by
    rw [hsub]
    exact (Mem.get_set_ne s10.mem 18 0 (s10.mem.get 18 - UInt16.ofNat cVal)
      (by decide)).trans hZ10
  have hT11 : (step s10).mem.get 18 = s.mem.get 17 - UInt16.ofNat cVal := by
    rw [hsub]
    exact (Mem.get_set_eq s10.mem 18 (s10.mem.get 18 - UInt16.ofNat cVal)).trans
      (by rw [hT10])
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → (step s10).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hsub]
    exact (Mem.get_set_ne s10.mem 18 a (s10.mem.get 18 - UInt16.ofNat cVal) ha18).trans
      (hpres10 a ha18 ha0)
  have hs11ONE : (step s10).mem.get 3 = 1 :=
    (hpres11 3 (by decide) (by decide)).trans hONE
  have g11 :=
    place_hcode_pres (s := s) (s' := step s10) (loopPc := loopPc)
      hbase hbound hpres11 hcode
  have enc :=
    place_enc_jlez_48 (s := step s10) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs11pc hbase hbound himg g11
  have hton11 : (step s10).pc.toNat = loopPc + 48 :=
    pc_ofNat_toNat (loopPc + 48) hs11pc (by omega)
  have hpc11 : (step s10).pc.toNat < 32768 := by omega
  have hjlez :=
    step_JLEZ (s := step s10) (x := 18) (dest := UInt16.ofNat (loopPc + 54))
      hs11h hpc11 hs11Z enc.1 enc.2.1 enc.2.2 (by decide)
  have hCton : (UInt16.ofNat cVal).toNat = cVal := word_ofNat_toNat cVal hcValb
  have hTwrap : 32768 ≤ (s.mem.get 17 - UInt16.ofNat cVal).toNat := by
    have := word_sub_lt (s.mem.get 17) (UInt16.ofNat cVal)
      (by simpa [hCton] using hN)
    omega
  have hle : ((step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18) = true := by
    have : le0 ((step s10).mem.get 18) = true := by
      rw [hT11]; exact le0_hi hTwrap
    simpa [le0] using this
  have hs12eq : step (step s10) = { step s10 with pc := UInt16.ofNat (loopPc + 54) } := by
    have hif :
        (if (step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18
          then UInt16.ofNat (loopPc + 54) else (step s10).pc + 3) =
          UInt16.ofNat (loopPc + 54) := by
      simp [hle]
    rw [hjlez, hif]
  have hs12pc : (step (step s10)).pc = UInt16.ofNat (loopPc + 54) := by rw [hs12eq]
  have hs12h : (step (step s10)).halted = false := by rw [hs12eq]; exact hs11h
  have hs12Z : (step (step s10)).mem.get 0 = 0 := by rw [hs12eq]; exact hs11Z
  have hs12ONE : (step (step s10)).mem.get 3 = 1 := by
    rw [hs12eq]; exact hs11ONE
  have hT12 : (step (step s10)).mem.get 18 = s.mem.get 17 - UInt16.ofNat cVal := by
    rw [hs12eq]; exact hT11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → (step (step s10)).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs12eq]
    exact hpres11 a ha18 ha0
  let s12 := step (step s10)
  have g12 :=
    place_hcode_pres (s := s) (s' := s12) (loopPc := loopPc)
      hbase hbound hpres12 hcode
  have hinc :=
    place_le_inc_T (s := s12) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs12pc hbase hbound hs12h hs12Z hs12ONE himg g12
  let s15 := runN s12 3
  have hs15pc : s15.pc = UInt16.ofNat (loopPc + 63) := hinc.1
  have hs15h := hinc.2.1
  have hT15 : s15.mem.get 18 = (s.mem.get 17 - UInt16.ofNat cVal) + 1 :=
    hinc.2.2.1.trans (by rw [hT12])
  have hZ15 := hinc.2.2.2.1
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres12 a ha18 ha0)
  have g15 :=
    place_hcode_pres (s := s) (s' := s15) (loopPc := loopPc)
      hbase hbound hpres15 hcode
  have enc2 :=
    place_enc_jlez_63 (s := s15) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs15pc hbase hbound himg g15
  have hton15 : s15.pc.toNat = loopPc + 63 :=
    pc_ofNat_toNat (loopPc + 63) hs15pc (by omega)
  have hpc15 : s15.pc.toNat < 32768 := by omega
  have hjlez2 :=
    step_JLEZ (s := s15) (x := 18) (dest := UInt16.ofNat (loopPc + 81))
      hs15h hpc15 hZ15 enc2.1 enc2.2.1 enc2.2.2 (by decide)
  have hle2 : (s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18) = true := by
    have : le0 (s15.mem.get 18) = true := by
      rw [hT15]
      by_cases hmax : (s.mem.get 17 - UInt16.ofNat cVal).toNat = 65535
      · have hw : (s.mem.get 17 - UInt16.ofNat cVal) + 1 = 0 :=
          word_add_one_wrap (s.mem.get 17 - UInt16.ofNat cVal) hmax
        rw [hw]; exact le0_zero
      · have hbd : (s.mem.get 17 - UInt16.ofNat cVal).toNat + 1 < 65536 := by
          have hlt := UInt16.toNat_lt_size (s.mem.get 17 - UInt16.ofNat cVal)
          have : UInt16.size = 65536 := rfl
          omega
        have hton := word_add_one_toNat (s.mem.get 17 - UInt16.ofNat cVal) hbd
        have hhi : 32768 ≤ ((s.mem.get 17 - UInt16.ofNat cVal) + 1).toNat := by
          rw [hton]
          have hx := word_sub_lt (s.mem.get 17) (UInt16.ofNat cVal)
            (by simpa [hCton] using hN)
          omega
        exact le0_hi hhi
    simpa [le0] using this
  have hs16eq : step s15 = { s15 with pc := UInt16.ofNat (loopPc + 81) } := by
    have hif :
        (if s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18
          then UInt16.ofNat (loopPc + 81) else s15.pc + 3) =
          UInt16.ofNat (loopPc + 81) := by
      simp [hle2]
    rw [hjlez2, hif]
  have hton10 : s10.pc.toNat = loopPc + 45 :=
    pc_ofNat_toNat (loopPc + 45) hs10pc (by omega)
  have hpc10 : s10.pc.toNat < 32768 := by omega
  have hrun : s16 = step s15 := by
    have h16 : runN s 16 = runN s6 10 := runN_add_eq s 6 10 16 (by decide)
    have h10 : runN s6 10 = runN s10 6 := runN_add_eq s6 4 6 10 (by decide)
    have h6 : runN s10 6 = runN (step s10) 5 := runN_succ_go s10 5 hs10h hpc10
    have h5 : runN (step s10) 5 = runN s12 4 := runN_succ_go (step s10) 4 hs11h hpc11
    have h4 : runN s12 4 = runN s15 1 := runN_add_eq s12 3 1 4 (by decide)
    have h1 := runN_one s15 hs15h hpc15
    exact h16.trans (h10.trans (h6.trans (h5.trans (h4.trans h1))))
  have hs16pc : s16.pc = UInt16.ofNat (loopPc + 81) := by rw [hrun, hs16eq]
  have hs16h : s16.halted = false := by rw [hrun, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by rw [hrun, hs16eq]; exact hZ15
  have hs16N : s16.mem.get 17 = s.mem.get 17 := by
    rw [hrun, hs16eq]; exact hpres15 17 (by decide) (by decide)
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hs16eq]
    exact hpres15 a ha18 ha0
  exact ⟨hs16pc, hs16h, hs16N, hs16Z, hpres⟩

/-- `c < N < 32768` at the loop entry: the POS arm reaches GE in 13
steps without changing `N` or `Q`. -/
theorem place_to_ge_mid {s : Machine} {loopPc cAddr qAddr cVal : Nat}
    (hpc : s.pc = UInt16.ofNat loopPc)
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hcAddr0 : 0 < cAddr)
    (hcAddr : cAddr < 16)
    (hcVal : 0 < cVal)
    (hcVal2 : cVal < 65536)
    (hC : s.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal)
    (hN1 : cVal < (s.mem.get 17).toNat)
    (hN2 : (s.mem.get 17).toNat < 32768)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s13 := runN s 13
    s13.pc = UInt16.ofNat (loopPc + 66) ∧
    s13.halted = false ∧
    s13.mem.get 17 = s.mem.get 17 ∧
    s13.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a) := by
  intro s13
  have hN0 : 0 < (s.mem.get 17).toNat := Nat.lt_trans hcVal hN1
  have hgo :=
    place_goto_pos (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hpc hbase hbound hh hZ hN0 hN2 himg hcode
  let s6 := runN s 6
  have hs6pc : s6.pc = UInt16.ofNat (loopPc + 33) := hgo.1
  have hs6h := hgo.2.1
  have hZ6 := hgo.2.2.2.2.1
  have hpres6 := hgo.2.2.2.2.2
  have g6 :=
    place_hcode_pres (s := s) (s' := s6) (loopPc := loopPc)
      hbase hbound hpres6 hcode
  have hmov :=
    place_pos_mov_N_T (s := s6) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs6pc hbase hbound hs6h hZ6 himg g6
  let s10 := runN s6 4
  have hs10pc : s10.pc = UInt16.ofNat (loopPc + 45) := hmov.1
  have hs10h := hmov.2.1
  have hT10 : s10.mem.get 18 = s.mem.get 17 :=
    hmov.2.2.1.trans (hgo.2.2.2.1)
  have hZ10 := hmov.2.2.2.1
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hmov.2.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hs10C : s10.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal :=
    (hpres10 (UInt16.ofNat cAddr)
      (ofNat_ne cAddr 18 (by omega) (by decide) (by omega))
      (ofNat_ne cAddr 0 (by omega) (by decide) (by omega))).trans hC
  have g10 :=
    place_hcode_pres (s := s) (s' := s10) (loopPc := loopPc)
      hbase hbound hpres10 hcode
  have hcAddr32 : cAddr < 32 := Nat.lt_trans hcAddr (by decide)
  have hsub :=
    place_sub_C_T (s := s10) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (cVal := cVal) hs10pc hbase hbound hs10h hcAddr32 hcVal2 hs10C himg g10
  have hs11pc : (step s10).pc = UInt16.ofNat (loopPc + 48) := by rw [hsub]
  have hs11h : (step s10).halted = false := by rw [hsub]; exact hs10h
  have hs11Z : (step s10).mem.get 0 = 0 := by
    rw [hsub]
    exact (Mem.get_set_ne s10.mem 18 0 (s10.mem.get 18 - UInt16.ofNat cVal)
      (by decide)).trans hZ10
  have hT11 : (step s10).mem.get 18 = s.mem.get 17 - UInt16.ofNat cVal := by
    rw [hsub]
    exact (Mem.get_set_eq s10.mem 18 (s10.mem.get 18 - UInt16.ofNat cVal)).trans
      (by rw [hT10])
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → (step s10).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hsub]
    exact (Mem.get_set_ne s10.mem 18 a (s10.mem.get 18 - UInt16.ofNat cVal) ha18).trans
      (hpres10 a ha18 ha0)
  have g11 :=
    place_hcode_pres (s := s) (s' := step s10) (loopPc := loopPc)
      hbase hbound hpres11 hcode
  have enc :=
    place_enc_jlez_48 (s := step s10) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs11pc hbase hbound himg g11
  have hton11 : (step s10).pc.toNat = loopPc + 48 :=
    pc_ofNat_toNat (loopPc + 48) hs11pc (by omega)
  have hpc11 : (step s10).pc.toNat < 32768 := by omega
  have hjlez :=
    step_JLEZ (s := step s10) (x := 18) (dest := UInt16.ofNat (loopPc + 54))
      hs11h hpc11 hs11Z enc.1 enc.2.1 enc.2.2 (by decide)
  have hCton : (UInt16.ofNat cVal).toNat = cVal := word_ofNat_toNat cVal hcVal2
  have hTnat : ((step s10).mem.get 18).toNat = (s.mem.get 17).toNat - cVal := by
    rw [hT11]
    have hge := word_sub_ge (s.mem.get 17) (UInt16.ofNat cVal)
      (Nat.le_of_lt (by simpa [hCton] using hN1))
    simpa [hCton] using hge
  have hle : ((step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18) = false := by
    have : le0 ((step s10).mem.get 18) = false := by
      have hpos : 0 < ((step s10).mem.get 18).toNat := by
        rw [hTnat]; omega
      have hhi : ((step s10).mem.get 18).toNat < 32768 := by
        rw [hTnat]; omega
      exact le0_pos hpos hhi
    simpa [le0] using this
  have hs12eq : step (step s10) = { step s10 with pc := (step s10).pc + 3 } := by
    have hif :
        (if (step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18
          then UInt16.ofNat (loopPc + 54) else (step s10).pc + 3) =
          (step s10).pc + 3 := by
      simp [hle]
    rw [hjlez, hif]
  have hs12pc : (step (step s10)).pc = UInt16.ofNat (loopPc + 51) := by
    have h3 := place_pc_add3 (loopPc + 48) hs11pc (by omega)
    have hsum : loopPc + 48 + 3 = loopPc + 51 := by omega
    rw [hs12eq, h3, hsum]
  have hs12h : (step (step s10)).halted = false := by rw [hs12eq]; exact hs11h
  have hs12Z : (step (step s10)).mem.get 0 = 0 := by rw [hs12eq]; exact hs11Z
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → (step (step s10)).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs12eq]
    exact hpres11 a ha18 ha0
  have g12 :=
    place_hcode_pres (s := s) (s' := step (step s10)) (loopPc := loopPc)
      hbase hbound hpres12 hcode
  have encJ :=
    place_enc_jmp_51 (s := step (step s10)) (loopPc := loopPc) (cAddr := cAddr)
      (qAddr := qAddr) hs12pc hbase hbound himg g12
  have hton12 : (step (step s10)).pc.toNat = loopPc + 51 :=
    pc_ofNat_toNat (loopPc + 51) hs12pc (by omega)
  have hpc12 : (step (step s10)).pc.toNat < 32768 := by omega
  have hjmp :=
    step_JMP (s := step (step s10)) (dest := UInt16.ofNat (loopPc + 66))
      hs12h hpc12 hs12Z encJ.1 encJ.2.1 encJ.2.2
  have hton10 : s10.pc.toNat = loopPc + 45 :=
    pc_ofNat_toNat (loopPc + 45) hs10pc (by omega)
  have hpc10 : s10.pc.toNat < 32768 := by omega
  have hrun : s13 = step (step (step s10)) := by
    have h13 : runN s 13 = runN s6 7 := runN_add_eq s 6 7 13 (by decide)
    have h7 : runN s6 7 = runN s10 3 := runN_add_eq s6 4 3 7 (by decide)
    have h3 := runN_3_steps s10 hs10h hpc10 hs11h hpc11 hs12h hpc12
    exact h13.trans (h7.trans h3)
  have hs13pc : s13.pc = UInt16.ofNat (loopPc + 66) := by rw [hrun, hjmp]
  have hs13h : s13.halted = false := by rw [hrun, hjmp]; exact hs12h
  have hs13Z : s13.mem.get 0 = 0 := by
    have hmem : (step (step (step s10))).mem = (step (step s10)).mem := by rw [hjmp]
    rw [hrun, hmem, hs12eq]; exact hs11Z
  have hs13N : s13.mem.get 17 = s.mem.get 17 := by
    have hmem : (step (step (step s10))).mem = (step (step s10)).mem := by rw [hjmp]
    rw [hrun, hmem, hs12eq]; exact hpres11 17 (by decide) (by decide)
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    have hmem : (step (step (step s10))).mem = (step (step s10)).mem := by rw [hjmp]
    rw [hrun, hmem]
    exact hpres12 a ha18 ha0
  exact ⟨hs13pc, hs13h, hs13N, hs13Z, hpres⟩


/-- `N = c` at the loop entry: the LE arm falls through to GE in 16
steps without changing `N` or `Q`. -/
theorem place_to_ge_eq {s : Machine} {loopPc cAddr qAddr cVal : Nat}
    (hpc : s.pc = UInt16.ofNat loopPc)
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcAddr0 : 0 < cAddr)
    (hcAddr : cAddr < 16)
    (hcVal : 0 < cVal)
    (hcVal2 : cVal < 32768)
    (hC : s.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal)
    (hN : s.mem.get 17 = UInt16.ofNat cVal)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s16 := runN s 16
    s16.pc = UInt16.ofNat (loopPc + 66) ∧
    s16.halted = false ∧
    s16.mem.get 17 = UInt16.ofNat cVal ∧
    s16.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a) := by
  intro s16
  have hcValb : cVal < 65536 := Nat.lt_trans hcVal2 (by decide)
  have hNton : (s.mem.get 17).toNat = cVal := by
    have hCton : (UInt16.ofNat cVal).toNat = cVal := word_ofNat_toNat cVal hcValb
    simpa [hN] using hCton
  have hN0 : 0 < (s.mem.get 17).toNat := by omega
  have hNhi : (s.mem.get 17).toNat < 32768 := by omega
  have hgo :=
    place_goto_pos (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hpc hbase hbound hh hZ hN0 hNhi himg hcode
  let s6 := runN s 6
  have hs6pc : s6.pc = UInt16.ofNat (loopPc + 33) := hgo.1
  have hs6h := hgo.2.1
  have hZ6 := hgo.2.2.2.2.1
  have hpres6 := hgo.2.2.2.2.2
  have g6 :=
    place_hcode_pres (s := s) (s' := s6) (loopPc := loopPc)
      hbase hbound hpres6 hcode
  have hmov :=
    place_pos_mov_N_T (s := s6) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs6pc hbase hbound hs6h hZ6 himg g6
  let s10 := runN s6 4
  have hs10pc : s10.pc = UInt16.ofNat (loopPc + 45) := hmov.1
  have hs10h := hmov.2.1
  have hT10 : s10.mem.get 18 = UInt16.ofNat cVal :=
    (hmov.2.2.1.trans (hgo.2.2.2.1)).trans hN
  have hZ10 := hmov.2.2.2.1
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → s10.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hmov.2.2.2.2.2 a ha18 ha0).trans (hpres6 a ha18 ha0)
  have hs10C : s10.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal :=
    (hpres10 (UInt16.ofNat cAddr)
      (ofNat_ne cAddr 18 (by omega) (by decide) (by omega))
      (ofNat_ne cAddr 0 (by omega) (by decide) (by omega))).trans hC
  have hs10ONE : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have g10 :=
    place_hcode_pres (s := s) (s' := s10) (loopPc := loopPc)
      hbase hbound hpres10 hcode
  have hcAddr32 : cAddr < 32 := Nat.lt_trans hcAddr (by decide)
  have hsub :=
    place_sub_C_T (s := s10) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (cVal := cVal) hs10pc hbase hbound hs10h hcAddr32 hcValb hs10C himg g10
  have hs11pc : (step s10).pc = UInt16.ofNat (loopPc + 48) := by rw [hsub]
  have hs11h : (step s10).halted = false := by rw [hsub]; exact hs10h
  have hs11Z : (step s10).mem.get 0 = 0 := by
    rw [hsub]
    exact (Mem.get_set_ne s10.mem 18 0 (s10.mem.get 18 - UInt16.ofNat cVal)
      (by decide)).trans hZ10
  have hT11 : (step s10).mem.get 18 = 0 := by
    rw [hsub]
    have : s10.mem.get 18 - UInt16.ofNat cVal = (0 : Word) := by
      rw [hT10]; simp
    exact (Mem.get_set_eq s10.mem 18 (s10.mem.get 18 - UInt16.ofNat cVal)).trans this
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → (step s10).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hsub]
    exact (Mem.get_set_ne s10.mem 18 a (s10.mem.get 18 - UInt16.ofNat cVal) ha18).trans
      (hpres10 a ha18 ha0)
  have hs11ONE : (step s10).mem.get 3 = 1 :=
    (hpres11 3 (by decide) (by decide)).trans hONE
  have g11 :=
    place_hcode_pres (s := s) (s' := step s10) (loopPc := loopPc)
      hbase hbound hpres11 hcode
  have enc :=
    place_enc_jlez_48 (s := step s10) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs11pc hbase hbound himg g11
  have hton11 : (step s10).pc.toNat = loopPc + 48 :=
    pc_ofNat_toNat (loopPc + 48) hs11pc (by omega)
  have hpc11 : (step s10).pc.toNat < 32768 := by omega
  have hjlez :=
    step_JLEZ (s := step s10) (x := 18) (dest := UInt16.ofNat (loopPc + 54))
      hs11h hpc11 hs11Z enc.1 enc.2.1 enc.2.2 (by decide)
  have hle : ((step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18) = true := by
    have : le0 ((step s10).mem.get 18) = true := by
      rw [hT11]; exact le0_zero
    simpa [le0] using this
  have hs12eq : step (step s10) = { step s10 with pc := UInt16.ofNat (loopPc + 54) } := by
    have hif :
        (if (step s10).mem.get 18 = 0 || 0x8000 ≤ (step s10).mem.get 18
          then UInt16.ofNat (loopPc + 54) else (step s10).pc + 3) =
          UInt16.ofNat (loopPc + 54) := by
      simp [hle]
    rw [hjlez, hif]
  have hs12pc : (step (step s10)).pc = UInt16.ofNat (loopPc + 54) := by rw [hs12eq]
  have hs12h : (step (step s10)).halted = false := by rw [hs12eq]; exact hs11h
  have hs12Z : (step (step s10)).mem.get 0 = 0 := by rw [hs12eq]; exact hs11Z
  have hs12ONE : (step (step s10)).mem.get 3 = 1 := by rw [hs12eq]; exact hs11ONE
  have hT12 : (step (step s10)).mem.get 18 = 0 := by rw [hs12eq]; exact hT11
  have hpres12 : ∀ a, a ≠ 18 → a ≠ 0 → (step (step s10)).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs12eq]
    exact hpres11 a ha18 ha0
  let s12 := step (step s10)
  have g12 :=
    place_hcode_pres (s := s) (s' := s12) (loopPc := loopPc)
      hbase hbound hpres12 hcode
  have hinc :=
    place_le_inc_T (s := s12) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs12pc hbase hbound hs12h hs12Z hs12ONE himg g12
  let s15 := runN s12 3
  have hs15pc : s15.pc = UInt16.ofNat (loopPc + 63) := hinc.1
  have hs15h := hinc.2.1
  have hT15 : s15.mem.get 18 = 1 := by
    have : s12.mem.get 18 + 1 = (0 : Word) + 1 := by rw [hT12]
    exact hinc.2.2.1.trans this
  have hZ15 := hinc.2.2.2.1
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres12 a ha18 ha0)
  have g15 :=
    place_hcode_pres (s := s) (s' := s15) (loopPc := loopPc)
      hbase hbound hpres15 hcode
  have enc2 :=
    place_enc_jlez_63 (s := s15) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      hs15pc hbase hbound himg g15
  have hton15 : s15.pc.toNat = loopPc + 63 :=
    pc_ofNat_toNat (loopPc + 63) hs15pc (by omega)
  have hpc15 : s15.pc.toNat < 32768 := by omega
  have hjlez2 :=
    step_JLEZ (s := s15) (x := 18) (dest := UInt16.ofNat (loopPc + 81))
      hs15h hpc15 hZ15 enc2.1 enc2.2.1 enc2.2.2 (by decide)
  have hle2 : (s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18) = false := by
    have : le0 (s15.mem.get 18) = false := by
      rw [hT15]; exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs16eq : step s15 = { s15 with pc := s15.pc + 3 } := by
    have hif :
        (if s15.mem.get 18 = 0 || 0x8000 ≤ s15.mem.get 18
          then UInt16.ofNat (loopPc + 81) else s15.pc + 3) = s15.pc + 3 := by
      simp [hle2]
    rw [hjlez2, hif]
  have hs16pc' : (step s15).pc = UInt16.ofNat (loopPc + 66) := by
    have h3 := place_pc_add3 (loopPc + 63) hs15pc (by omega)
    have hsum : loopPc + 63 + 3 = loopPc + 66 := by omega
    rw [hs16eq, h3, hsum]
  have hton10 : s10.pc.toNat = loopPc + 45 :=
    pc_ofNat_toNat (loopPc + 45) hs10pc (by omega)
  have hpc10 : s10.pc.toNat < 32768 := by omega
  have hrun : s16 = step s15 := by
    have h16 : runN s 16 = runN s6 10 := runN_add_eq s 6 10 16 (by decide)
    have h10 : runN s6 10 = runN s10 6 := runN_add_eq s6 4 6 10 (by decide)
    have h6 : runN s10 6 = runN (step s10) 5 := runN_succ_go s10 5 hs10h hpc10
    have h5 : runN (step s10) 5 = runN s12 4 := runN_succ_go (step s10) 4 hs11h hpc11
    have h4 : runN s12 4 = runN s15 1 := runN_add_eq s12 3 1 4 (by decide)
    have h1 := runN_one s15 hs15h hpc15
    exact h16.trans (h10.trans (h6.trans (h5.trans (h4.trans h1))))
  have hs16pc : s16.pc = UInt16.ofNat (loopPc + 66) := by rw [hrun, hs16pc']
  have hs16h : s16.halted = false := by rw [hrun, hs16eq]; exact hs15h
  have hs16Z : s16.mem.get 0 = 0 := by rw [hrun, hs16eq]; exact hZ15
  have hs16N : s16.mem.get 17 = UInt16.ofNat cVal := by
    rw [hrun, hs16eq]; exact (hpres15 17 (by decide) (by decide)).trans hN
  have hpres : ∀ a, a ≠ 18 → a ≠ 0 → s16.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hs16eq]
    exact hpres15 a ha18 ha0
  exact ⟨hs16pc, hs16h, hs16N, hs16Z, hpres⟩

/-- All `N ≥ c` compare arms reach GE in `placeCmpSteps c N` steps,
leaving `N` and `Q` unchanged. -/
theorem place_to_ge {s : Machine} {loopPc cAddr qAddr cVal : Nat}
    (hpc : s.pc = UInt16.ofNat loopPc)
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcAddr0 : 0 < cAddr)
    (hcAddr : cAddr < 16)
    (hcVal : 0 < cVal)
    (hcVal2 : cVal < 32768)
    (hC : s.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal)
    (hN : cVal ≤ (s.mem.get 17).toNat)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let n := (s.mem.get 17).toNat
    let sk := runN s (placeCmpSteps cVal n)
    sk.pc = UInt16.ofNat (loopPc + 66) ∧
    sk.halted = false ∧
    sk.mem.get 17 = s.mem.get 17 ∧
    sk.mem.get 0 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → sk.mem.get a = s.mem.get a) := by
  intro n sk
  have hcLe : cVal ≤ 32768 := Nat.le_of_lt hcVal2
  by_cases hhi : 32768 ≤ n
  · have hst : placeCmpSteps cVal n = 9 := placeCmpSteps_hi hhi hcLe
    have hge :=
      place_to_ge_hi (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
        hpc hbase hbound hh hZ hONE (by exact hhi) himg hcode
    have hsk : sk = runN s 9 := by simp [sk, hst]
    rw [hsk]
    exact hge
  · by_cases heq : n = cVal
    · have hst : placeCmpSteps cVal n = 16 := by rw [heq, placeCmpSteps_eq hcVal2]
      have hcValb : cVal < 65536 := Nat.lt_trans hcVal2 (by decide)
      have hW : s.mem.get 17 = UInt16.ofNat cVal :=
        word_eq_of_toNat (s.mem.get 17) cVal hcValb (heq ▸ (rfl : n = (s.mem.get 17).toNat).symm)
      have hge :=
        place_to_ge_eq (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
          (cVal := cVal) hpc hbase hbound hh hZ hONE hcAddr0 hcAddr hcVal hcVal2 hC hW himg hcode
      have hsk : sk = runN s 16 := by simp [sk, hst]
      rw [hsk]
      refine ⟨hge.1, hge.2.1, hge.2.2.1.trans hW.symm, hge.2.2.2.1, hge.2.2.2.2⟩
    · have h2 : n < 32768 := Nat.lt_of_not_ge hhi
      have h1 : cVal < n := Nat.lt_of_le_of_ne hN (Ne.symm heq)
      have hst : placeCmpSteps cVal n = 13 := placeCmpSteps_mid h1 h2
      have hcValb : cVal < 65536 := Nat.lt_trans hcVal2 (by decide)
      have hge :=
        place_to_ge_mid (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
          (cVal := cVal) hpc hbase hbound hh hZ hcAddr0 hcAddr hcVal hcValb hC h1 h2 himg hcode
      have hsk : sk = runN s 13 := by simp [sk, hst]
      rw [hsk]
      exact hge


/-- One full place-loop iteration: compare diamond plus the GE body,
returning to the loop entry with `N` decreased by `c` and `Q` increased
by 1. Reconstructs the same magnitude. -/
theorem place_one_iter {s : Machine} {loopPc cAddr qAddr cVal : Nat}
    (hpc : s.pc = UInt16.ofNat loopPc)
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcAddr0 : 0 < cAddr)
    (hcAddr : cAddr < 16)
    (hqAddr : 20 ≤ qAddr)
    (hqAddr2 : qAddr < 32)
    (hcVal : 0 < cVal)
    (hcVal2 : cVal < 32768)
    (hC : s.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal)
    (hN : cVal ≤ (s.mem.get 17).toNat)
    (hQ : (s.mem.get (UInt16.ofNat qAddr)).toNat + 1 < 65536)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let n := (s.mem.get 17).toNat
    let q := (s.mem.get (UInt16.ofNat qAddr)).toNat
    let s1 := runN s (placeCmpSteps cVal n + 5)
    s1.pc = UInt16.ofNat loopPc ∧
    s1.halted = false ∧
    s1.mem.get 0 = 0 ∧
    s1.mem.get 3 = 1 ∧
    s1.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal ∧
    (s1.mem.get 17).toNat = n - cVal ∧
    (s1.mem.get (UInt16.ofNat qAddr)).toNat = q + 1 ∧
    q * cVal + n = (s1.mem.get (UInt16.ofNat qAddr)).toNat * cVal + (s1.mem.get 17).toNat ∧
    (∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]!) ∧
    (∀ a, a ≠ 17 → a ≠ UInt16.ofNat qAddr → a ≠ 18 → a ≠ 0 →
      s1.mem.get a = s.mem.get a) := by
  intro n q s1
  have hcValb : cVal < 65536 := Nat.lt_trans hcVal2 (by decide)
  have hto :=
    place_to_ge (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (cVal := cVal) hpc hbase hbound hh hZ hONE hcAddr0 hcAddr hcVal hcVal2 hC hN himg hcode
  let sk := runN s (placeCmpSteps cVal n)
  have hskpc : sk.pc = UInt16.ofNat (loopPc + 66) := hto.1
  have hskh : sk.halted = false := hto.2.1
  have hskN : sk.mem.get 17 = s.mem.get 17 := hto.2.2.1
  have hskZ : sk.mem.get 0 = 0 := hto.2.2.2.1
  have hpresk := hto.2.2.2.2
  have hskONE : sk.mem.get 3 = 1 :=
    (hpresk 3 (by decide) (by decide)).trans hONE
  have hskC : sk.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal :=
    (hpresk (UInt16.ofNat cAddr)
      (ofNat_ne cAddr 18 (by omega) (by decide) (by omega))
      (ofNat_ne cAddr 0 (by omega) (by decide) (by omega))).trans hC
  have hskQ : sk.mem.get (UInt16.ofNat qAddr) = s.mem.get (UInt16.ofNat qAddr) :=
    hpresk (UInt16.ofNat qAddr)
      (ofNat_ne qAddr 18 (by omega) (by decide) (by omega))
      (ofNat_ne qAddr 0 (by omega) (by decide) (by omega))
  have gsk :=
    place_hcode_pres (s := s) (s' := sk) (loopPc := loopPc)
      hbase hbound hpresk hcode
  have hNge : cVal ≤ (sk.mem.get 17).toNat := by rw [hskN]; exact hN
  have hQsk : (sk.mem.get (UInt16.ofNat qAddr)).toNat + 1 < 65536 := by
    rw [hskQ]; exact hQ
  have hcAddr32 : cAddr < 32 := Nat.lt_trans hcAddr (by decide)
  have hbody :=
    place_ge_body (s := sk) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
      (cVal := cVal) hskpc hbase hbound hskh hskZ hskONE hcAddr32 hqAddr hqAddr2
      hcVal hcValb hskC hNge hQsk himg gsk
  have hrun : s1 = runN sk 5 :=
    runN_add s (placeCmpSteps cVal n) 5
  have hs1pc : s1.pc = UInt16.ofNat loopPc := by rw [hrun]; exact hbody.1
  have hs1h : s1.halted = false := by rw [hrun]; exact hbody.2.1
  have hs1Z : s1.mem.get 0 = 0 := by rw [hrun]; exact hbody.2.2.1
  have hs1Nton : (s1.mem.get 17).toNat = n - cVal := by
    rw [hrun]
    have : (sk.mem.get 17).toNat = n := by rw [hskN]
    exact hbody.2.2.2.2.2.1.trans (by rw [this])
  have hs1Qton : (s1.mem.get (UInt16.ofNat qAddr)).toNat = q + 1 := by
    rw [hrun]
    have : (sk.mem.get (UInt16.ofNat qAddr)).toNat = q := by rw [hskQ]
    exact hbody.2.2.2.2.2.2.1.trans (by rw [this])
  have hpresB := hbody.2.2.2.2.2.2.2
  have hs1ONE : s1.mem.get 3 = 1 := by
    rw [hrun]
    exact (hpresB 3 (by decide)
      (ofNat_ne 3 qAddr (by decide) (by omega) (by omega)) (by decide)).trans hskONE
  have hs1C : s1.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal := by
    rw [hrun]
    exact (hpresB (UInt16.ofNat cAddr)
      (ofNat_ne cAddr 17 (by omega) (by decide) (by omega))
      (ofNat_ne cAddr qAddr (by omega) (by omega) (by omega))
      (ofNat_ne cAddr 0 (by omega) (by decide) (by omega))).trans hskC
  have hinv : q * cVal + n =
      (s1.mem.get (UInt16.ofNat qAddr)).toNat * cVal + (s1.mem.get 17).toNat := by
    rw [hs1Qton, hs1Nton, Nat.add_mul q 1 cVal, Nat.one_mul, Nat.add_assoc,
      Nat.add_sub_of_le hN]
  have hcode1 (k : Nat) (h1 : loopPc ≤ k) (h2 : k < loopPc + 81) :
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    rw [hrun]
    have hne17 : UInt16.ofNat k ≠ 17 :=
      ofNat_ne k 17 (by omega) (by decide) (by omega)
    have hneQ : UInt16.ofNat k ≠ UInt16.ofNat qAddr :=
      ofNat_ne k qAddr (by omega) (by omega) (by omega)
    have hne0 : UInt16.ofNat k ≠ 0 :=
      ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresB (UInt16.ofNat k) hne17 hneQ hne0).trans
      ((hpresk (UInt16.ofNat k)
          (ofNat_ne k 18 (by omega) (by decide) (by omega)) hne0).trans
        (hcode k h1 h2))
  have hpres : ∀ a, a ≠ 17 → a ≠ UInt16.ofNat qAddr → a ≠ 18 → a ≠ 0 →
      s1.mem.get a = s.mem.get a := by
    intro a ha17 haQ ha18 ha0
    rw [hrun]
    exact (hpresB a ha17 haQ ha0).trans (hpresk a ha18 ha0)
  exact ⟨hs1pc, hs1h, hs1Z, hs1ONE, hs1C, hs1Nton, hs1Qton, hinv, hcode1, hpres⟩

/-- The place-loop reconstruction invariant: after `placeSteps c N` steps
the machine is at the loop exit with remainder `N < c` and
`Q * c + N` equal to the entry magnitude. -/
theorem place_loop_gen (loopPc cAddr qAddr cVal n : Nat)
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hcAddr0 : 0 < cAddr)
    (hcAddr : cAddr < 16)
    (hqAddr : 20 ≤ qAddr)
    (hqAddr2 : qAddr < 32)
    (hcVal : 0 < cVal)
    (hcVal2 : cVal < 32768)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o)) :
    ∀ (s : Machine),
      s.pc = UInt16.ofNat loopPc →
      s.halted = false →
      s.mem.get 0 = 0 →
      s.mem.get 3 = 1 →
      s.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal →
      (s.mem.get 17).toNat = n →
      (s.mem.get (UInt16.ofNat qAddr)).toNat + n / cVal < 65536 →
      (∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
        s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) →
      let q := (s.mem.get (UInt16.ofNat qAddr)).toNat
      let s' := runN s (placeSteps cVal n)
      s'.pc = UInt16.ofNat (loopPc + 81) ∧
      s'.halted = false ∧
      s'.mem.get 0 = 0 ∧
      (s'.mem.get 17).toNat < cVal ∧
      q * cVal + n = (s'.mem.get (UInt16.ofNat qAddr)).toNat * cVal + (s'.mem.get 17).toNat ∧
      (∀ a, a ≠ 17 → a ≠ UInt16.ofNat qAddr → a ≠ 18 → a ≠ 0 →
        s'.mem.get a = s.mem.get a) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s hpc hh hZ hONE hC hn hQ hcode
    intro q s'
    by_cases hlt : n < cVal
    · by_cases h0 : n = 0
      · subst h0
        have hW : s.mem.get 17 = 0 :=
          word_eq_of_toNat (s.mem.get 17) 0 (by decide) hn
        have hex :=
          place_exit_zero (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
            hpc hbase hbound hh hZ hONE hW himg hcode
        have hs' : s' = runN s 10 := by
          simp [s', placeSteps_zero hcVal]
        rw [hs']
        have hltN : ((runN s 10).mem.get 17).toNat < cVal := by
          have : (runN s 10).mem.get 17 = 0 := hex.2.2.1
          simp [this]
          exact hcVal
        have hinv0 :
            q * cVal + 0 =
              ((runN s 10).mem.get (UInt16.ofNat qAddr)).toNat * cVal +
                ((runN s 10).mem.get 17).toNat := by
          have hQ0 : (runN s 10).mem.get (UInt16.ofNat qAddr) =
              s.mem.get (UInt16.ofNat qAddr) :=
            hex.2.2.2.2 (UInt16.ofNat qAddr)
              (ofNat_ne qAddr 18 (by omega) (by decide) (by omega))
              (ofNat_ne qAddr 0 (by omega) (by decide) (by omega))
          have hN0 : (runN s 10).mem.get 17 = 0 := hex.2.2.1
          rw [hQ0, hN0]
          have : (s.mem.get (UInt16.ofNat qAddr)).toNat = q := rfl
          simp [this]
        have hpres0 : ∀ a, a ≠ 17 → a ≠ UInt16.ofNat qAddr → a ≠ 18 → a ≠ 0 →
            (runN s 10).mem.get a = s.mem.get a := by
          intro a ha17 haQ ha18 ha0
          exact hex.2.2.2.2 a ha18 ha0
        exact ⟨hex.1, hex.2.1, hex.2.2.2.1, hltN, hinv0, hpres0⟩
      · have hpos : 0 < n := Nat.pos_of_ne_zero h0
        have hNpos : 0 < (s.mem.get 17).toNat := by rw [hn]; exact hpos
        have hNlt : (s.mem.get 17).toNat < cVal := by rw [hn]; exact hlt
        have hcLe : cVal ≤ 32768 := Nat.le_of_lt hcVal2
        have hex :=
          place_exit_small (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
            (cVal := cVal) hpc hbase hbound hh hZ hONE hcAddr0 hcAddr hcVal hcLe
            hC hNpos hNlt himg hcode
        have hs' : s' = runN s 16 := by
          simp [s', placeSteps_small hpos hlt]
        rw [hs']
        have hltN : ((runN s 16).mem.get 17).toNat < cVal := by
          have : (runN s 16).mem.get 17 = s.mem.get 17 := hex.2.2.1
          rw [this, hn]; exact hlt
        have hinv0 :
            q * cVal + n =
              ((runN s 16).mem.get (UInt16.ofNat qAddr)).toNat * cVal +
                ((runN s 16).mem.get 17).toNat := by
          have hQ0 : (runN s 16).mem.get (UInt16.ofNat qAddr) =
              s.mem.get (UInt16.ofNat qAddr) :=
            hex.2.2.2.2 (UInt16.ofNat qAddr)
              (ofNat_ne qAddr 18 (by omega) (by decide) (by omega))
              (ofNat_ne qAddr 0 (by omega) (by decide) (by omega))
          have hNs : (runN s 16).mem.get 17 = s.mem.get 17 := hex.2.2.1
          rw [hQ0, hNs, hn]
        have hpres0 : ∀ a, a ≠ 17 → a ≠ UInt16.ofNat qAddr → a ≠ 18 → a ≠ 0 →
            (runN s 16).mem.get a = s.mem.get a := by
          intro a ha17 haQ ha18 ha0
          exact hex.2.2.2.2 a ha18 ha0
        exact ⟨hex.1, hex.2.1, hex.2.2.2.1, hltN, hinv0, hpres0⟩
    · have hge : cVal ≤ n := Nat.le_of_not_lt hlt
      have hNge : cVal ≤ (s.mem.get 17).toNat := by rw [hn]; exact hge
      have hQ1 : (s.mem.get (UInt16.ofNat qAddr)).toNat + 1 < 65536 := by
        have : 1 ≤ n / cVal := Nat.div_pos hge hcVal
        omega
      have hone :=
        place_one_iter (s := s) (loopPc := loopPc) (cAddr := cAddr) (qAddr := qAddr)
          (cVal := cVal) hpc hbase hbound hh hZ hONE hcAddr0 hcAddr hqAddr hqAddr2
          hcVal hcVal2 hC hNge hQ1 himg hcode
      rw [hn] at hone
      have hsteps := placeSteps_ge hcVal hge
      have hrun : s' = runN (runN s (placeCmpSteps cVal n + 5))
          (placeSteps cVal (n - cVal)) := by
        have hadd :=
          runN_add s (placeCmpSteps cVal n + 5) (placeSteps cVal (n - cVal))
        have : placeSteps cVal n =
            placeCmpSteps cVal n + 5 + placeSteps cVal (n - cVal) := hsteps
        simp [s', this, hadd]
      have hs1pc : (runN s (placeCmpSteps cVal n + 5)).pc = UInt16.ofNat loopPc := hone.1
      have hs1h : (runN s (placeCmpSteps cVal n + 5)).halted = false := hone.2.1
      have hs1Z : (runN s (placeCmpSteps cVal n + 5)).mem.get 0 = 0 := hone.2.2.1
      have hs1ONE : (runN s (placeCmpSteps cVal n + 5)).mem.get 3 = 1 := hone.2.2.2.1
      have hs1C : (runN s (placeCmpSteps cVal n + 5)).mem.get (UInt16.ofNat cAddr) =
          UInt16.ofNat cVal := hone.2.2.2.2.1
      have hs1N : ((runN s (placeCmpSteps cVal n + 5)).mem.get 17).toNat = n - cVal :=
        hone.2.2.2.2.2.1
      have hs1Q : ((runN s (placeCmpSteps cVal n + 5)).mem.get (UInt16.ofNat qAddr)).toNat =
          q + 1 := hone.2.2.2.2.2.2.1
      have hinv1 := hone.2.2.2.2.2.2.2.1
      have hcode1 := hone.2.2.2.2.2.2.2.2.1
      have hpres1 := hone.2.2.2.2.2.2.2.2.2
      have hQ1n :
          ((runN s (placeCmpSteps cVal n + 5)).mem.get (UInt16.ofNat qAddr)).toNat +
            (n - cVal) / cVal < 65536 := by
        have hdiv : (n - cVal) / cVal + 1 = n / cVal :=
          (Nat.div_eq_sub_div hcVal hge).symm
        rw [hs1Q]
        omega
      have ihn :=
        ih (n - cVal) (by omega) (runN s (placeCmpSteps cVal n + 5))
          hs1pc hs1h hs1Z hs1ONE hs1C hs1N hQ1n hcode1
      rw [hrun]
      have hpc' :
          (runN (runN s (placeCmpSteps cVal n + 5)) (placeSteps cVal (n - cVal))).pc =
            UInt16.ofNat (loopPc + 81) := ihn.1
      have hh' :
          (runN (runN s (placeCmpSteps cVal n + 5)) (placeSteps cVal (n - cVal))).halted =
            false := ihn.2.1
      have hZ' :
          (runN (runN s (placeCmpSteps cVal n + 5)) (placeSteps cVal (n - cVal))).mem.get 0 =
            0 := ihn.2.2.1
      have hlt' :
          ((runN (runN s (placeCmpSteps cVal n + 5)) (placeSteps cVal (n - cVal))).mem.get 17).toNat <
            cVal := ihn.2.2.2.1
      have hinv' :
          ((runN s (placeCmpSteps cVal n + 5)).mem.get (UInt16.ofNat qAddr)).toNat * cVal +
            (n - cVal) =
          ((runN (runN s (placeCmpSteps cVal n + 5)) (placeSteps cVal (n - cVal))).mem.get
              (UInt16.ofNat qAddr)).toNat * cVal +
            ((runN (runN s (placeCmpSteps cVal n + 5)) (placeSteps cVal (n - cVal))).mem.get 17).toNat :=
        ihn.2.2.2.2.1
      have hpres' :
          ∀ a, a ≠ 17 → a ≠ UInt16.ofNat qAddr → a ≠ 18 → a ≠ 0 →
            (runN (runN s (placeCmpSteps cVal n + 5)) (placeSteps cVal (n - cVal))).mem.get a =
              (runN s (placeCmpSteps cVal n + 5)).mem.get a :=
        ihn.2.2.2.2.2
      have hinvF :
          q * cVal + n =
            ((runN (runN s (placeCmpSteps cVal n + 5)) (placeSteps cVal (n - cVal))).mem.get
                (UInt16.ofNat qAddr)).toNat * cVal +
              ((runN (runN s (placeCmpSteps cVal n + 5)) (placeSteps cVal (n - cVal))).mem.get 17).toNat := by
        have hL : q * cVal + n =
            ((runN s (placeCmpSteps cVal n + 5)).mem.get (UInt16.ofNat qAddr)).toNat * cVal +
              ((runN s (placeCmpSteps cVal n + 5)).mem.get 17).toNat := hinv1
        rw [hs1N] at hL
        exact hL.trans hinv'
      have hpresF : ∀ a, a ≠ 17 → a ≠ UInt16.ofNat qAddr → a ≠ 18 → a ≠ 0 →
          (runN (runN s (placeCmpSteps cVal n + 5)) (placeSteps cVal (n - cVal))).mem.get a =
            s.mem.get a := by
        intro a ha17 haQ ha18 ha0
        exact (hpres' a ha17 haQ ha18 ha0).trans (hpres1 a ha17 haQ ha18 ha0)
      exact ⟨hpc', hh', hZ', hlt', hinvF, hpresF⟩

/-- Package of `place_loop_gen` at the current machine's `N`. -/
theorem place_loop {s : Machine} {loopPc cAddr qAddr cVal : Nat}
    (hpc : s.pc = UInt16.ofNat loopPc)
    (hbase : 32 ≤ loopPc)
    (hbound : loopPc + 81 < (32768 : Nat))
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hcAddr0 : 0 < cAddr)
    (hcAddr : cAddr < 16)
    (hqAddr : 20 ≤ qAddr)
    (hqAddr2 : qAddr < 32)
    (hcVal : 0 < cVal)
    (hcVal2 : cVal < 32768)
    (hC : s.mem.get (UInt16.ofNat cAddr) = UInt16.ofNat cVal)
    (hQ : (s.mem.get (UInt16.ofNat qAddr)).toNat + (s.mem.get 17).toNat / cVal < 65536)
    (himg : ∀ o : Nat, o < 81 →
      intfmtImage[loopPc + o]! = UInt16.ofNat (placeTemplate loopPc cAddr qAddr o))
    (hcode : ∀ k : Nat, loopPc ≤ k → k < loopPc + 81 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let n := (s.mem.get 17).toNat
    let q := (s.mem.get (UInt16.ofNat qAddr)).toNat
    let s' := runN s (placeSteps cVal n)
    s'.pc = UInt16.ofNat (loopPc + 81) ∧
    s'.halted = false ∧
    s'.mem.get 0 = 0 ∧
    (s'.mem.get 17).toNat < cVal ∧
    q * cVal + n = (s'.mem.get (UInt16.ofNat qAddr)).toNat * cVal + (s'.mem.get 17).toNat ∧
    (∀ a, a ≠ 17 → a ≠ UInt16.ofNat qAddr → a ≠ 18 → a ≠ 0 →
      s'.mem.get a = s.mem.get a) :=
  place_loop_gen loopPc cAddr qAddr cVal (s.mem.get 17).toNat
    hbase hbound hcAddr0 hcAddr hqAddr hqAddr2 hcVal hcVal2 himg
    s hpc hh hZ hONE hC rfl hQ hcode

/-- `P1_LOOP` reconstruction invariant (place 1000, `Q1`). -/
theorem p1_loop {s : Machine}
    (hpc : s.pc = 270)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hC : s.mem.get 6 = 1000)
    (hQ : (s.mem.get 21).toNat + (s.mem.get 17).toNat / 1000 < 65536)
    (hcode : ∀ k : Nat, 270 ≤ k → k < 351 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let n := (s.mem.get 17).toNat
    let q := (s.mem.get 21).toNat
    let s' := runN s (placeSteps 1000 n)
    s'.pc = 351 ∧
    s'.halted = false ∧
    s'.mem.get 0 = 0 ∧
    (s'.mem.get 17).toNat < 1000 ∧
    q * 1000 + n = (s'.mem.get 21).toNat * 1000 + (s'.mem.get 17).toNat ∧
    (∀ a, a ≠ 17 → a ≠ 21 → a ≠ 18 → a ≠ 0 → s'.mem.get a = s.mem.get a) := by
  intro n q s'
  have hp : s.pc = UInt16.ofNat 270 :=
    hpc.trans (rfl : (270 : Word) = UInt16.ofNat 270)
  have hCw : s.mem.get (UInt16.ofNat 6) = UInt16.ofNat 1000 := by
    have : (6 : Word) = UInt16.ofNat 6 := rfl
    have : (1000 : Word) = UInt16.ofNat 1000 := rfl
    simpa [this] using (hC : s.mem.get 6 = 1000)
  have hQw : (s.mem.get (UInt16.ofNat 21)).toNat + (s.mem.get 17).toNat / 1000 < 65536 := by
    have : (21 : Word) = UInt16.ofNat 21 := rfl
    simpa [this] using hQ
  have h :=
    place_loop (s := s) (loopPc := 270) (cAddr := 6) (qAddr := 21) (cVal := 1000)
      hp (by decide) (by decide) hh hZ hONE (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hCw hQw p1_image hcode
  have hpc' : s'.pc = (351 : Word) := by
    have : UInt16.ofNat (270 + 81) = (351 : Word) := rfl
    exact h.1.trans this
  have hQeq : s'.mem.get 21 = s'.mem.get (UInt16.ofNat 21) := by
    have : (21 : Word) = UInt16.ofNat 21 := rfl
    simp [this]
  have hw : (21 : Word) = UInt16.ofNat 21 := rfl
  refine ⟨hpc', h.2.1, h.2.2.1, h.2.2.2.1, ?inv, ?pres⟩
  · have hq : q = (s.mem.get (UInt16.ofNat 21)).toNat := by simp [q, hw]
    have hn : n = (s.mem.get 17).toNat := rfl
    have hs' : s' = runN s (placeSteps 1000 n) := rfl
    rw [hq, hn, hs']
    simpa [hw] using h.2.2.2.2.1
  · intro a ha17 haA ha18 ha0
    have haA' : a ≠ UInt16.ofNat 21 := by simpa [hw] using haA
    exact h.2.2.2.2.2 a ha17 haA' ha18 ha0

/-- `P2_LOOP` reconstruction invariant (place 100, `Q2`). -/
theorem p2_loop {s : Machine}
    (hpc : s.pc = 351)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hC : s.mem.get 5 = 100)
    (hQ : (s.mem.get 22).toNat + (s.mem.get 17).toNat / 100 < 65536)
    (hcode : ∀ k : Nat, 351 ≤ k → k < 432 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let n := (s.mem.get 17).toNat
    let q := (s.mem.get 22).toNat
    let s' := runN s (placeSteps 100 n)
    s'.pc = 432 ∧
    s'.halted = false ∧
    s'.mem.get 0 = 0 ∧
    (s'.mem.get 17).toNat < 100 ∧
    q * 100 + n = (s'.mem.get 22).toNat * 100 + (s'.mem.get 17).toNat ∧
    (∀ a, a ≠ 17 → a ≠ 22 → a ≠ 18 → a ≠ 0 → s'.mem.get a = s.mem.get a) := by
  intro n q s'
  have hp : s.pc = UInt16.ofNat 351 :=
    hpc.trans (rfl : (351 : Word) = UInt16.ofNat 351)
  have hCw : s.mem.get (UInt16.ofNat 5) = UInt16.ofNat 100 := by
    have : (5 : Word) = UInt16.ofNat 5 := rfl
    have : (100 : Word) = UInt16.ofNat 100 := rfl
    simpa [this] using (hC : s.mem.get 5 = 100)
  have hQw : (s.mem.get (UInt16.ofNat 22)).toNat + (s.mem.get 17).toNat / 100 < 65536 := by
    have : (22 : Word) = UInt16.ofNat 22 := rfl
    simpa [this] using hQ
  have h :=
    place_loop (s := s) (loopPc := 351) (cAddr := 5) (qAddr := 22) (cVal := 100)
      hp (by decide) (by decide) hh hZ hONE (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hCw hQw p2_image hcode
  have hpc' : s'.pc = (432 : Word) := by
    have : UInt16.ofNat (351 + 81) = (432 : Word) := rfl
    exact h.1.trans this
  have hw : (22 : Word) = UInt16.ofNat 22 := rfl
  refine ⟨hpc', h.2.1, h.2.2.1, h.2.2.2.1, ?inv, ?pres⟩
  · have hq : q = (s.mem.get (UInt16.ofNat 22)).toNat := by simp [q, hw]
    have hn : n = (s.mem.get 17).toNat := rfl
    have hs' : s' = runN s (placeSteps 100 n) := rfl
    rw [hq, hn, hs']
    simpa [hw] using h.2.2.2.2.1
  · intro a ha17 haA ha18 ha0
    have haA' : a ≠ UInt16.ofNat 22 := by simpa [hw] using haA
    exact h.2.2.2.2.2 a ha17 haA' ha18 ha0

/-- `P3_LOOP` reconstruction invariant (place 10, `Q3`). -/
theorem p3_loop {s : Machine}
    (hpc : s.pc = 432)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hC : s.mem.get 4 = 10)
    (hQ : (s.mem.get 23).toNat + (s.mem.get 17).toNat / 10 < 65536)
    (hcode : ∀ k : Nat, 432 ≤ k → k < 513 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let n := (s.mem.get 17).toNat
    let q := (s.mem.get 23).toNat
    let s' := runN s (placeSteps 10 n)
    s'.pc = 513 ∧
    s'.halted = false ∧
    s'.mem.get 0 = 0 ∧
    (s'.mem.get 17).toNat < 10 ∧
    q * 10 + n = (s'.mem.get 23).toNat * 10 + (s'.mem.get 17).toNat ∧
    (∀ a, a ≠ 17 → a ≠ 23 → a ≠ 18 → a ≠ 0 → s'.mem.get a = s.mem.get a) := by
  intro n q s'
  have hp : s.pc = UInt16.ofNat 432 :=
    hpc.trans (rfl : (432 : Word) = UInt16.ofNat 432)
  have hCw : s.mem.get (UInt16.ofNat 4) = UInt16.ofNat 10 := by
    have : (4 : Word) = UInt16.ofNat 4 := rfl
    have : (10 : Word) = UInt16.ofNat 10 := rfl
    simpa [this] using (hC : s.mem.get 4 = 10)
  have hQw : (s.mem.get (UInt16.ofNat 23)).toNat + (s.mem.get 17).toNat / 10 < 65536 := by
    have : (23 : Word) = UInt16.ofNat 23 := rfl
    simpa [this] using hQ
  have h :=
    place_loop (s := s) (loopPc := 432) (cAddr := 4) (qAddr := 23) (cVal := 10)
      hp (by decide) (by decide) hh hZ hONE (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hCw hQw p3_image hcode
  have hpc' : s'.pc = (513 : Word) := by
    have : UInt16.ofNat (432 + 81) = (513 : Word) := rfl
    exact h.1.trans this
  have hw : (23 : Word) = UInt16.ofNat 23 := rfl
  refine ⟨hpc', h.2.1, h.2.2.1, h.2.2.2.1, ?inv, ?pres⟩
  · have hq : q = (s.mem.get (UInt16.ofNat 23)).toNat := by simp [q, hw]
    have hn : n = (s.mem.get 17).toNat := rfl
    have hs' : s' = runN s (placeSteps 10 n) := rfl
    rw [hq, hn, hs']
    simpa [hw] using h.2.2.2.2.1
  · intro a ha17 haA ha18 ha0
    have haA' : a ≠ UInt16.ofNat 23 := by simpa [hw] using haA
    exact h.2.2.2.2.2 a ha17 haA' ha18 ha0

end IntFmt
