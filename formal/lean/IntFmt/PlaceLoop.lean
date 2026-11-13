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

end IntFmt
