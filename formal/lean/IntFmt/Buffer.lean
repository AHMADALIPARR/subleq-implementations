/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Milestones 3 and 4: buffer safety and output length (snprintf-style).
Capacity 0 writes nothing; capacity c>0 writes at most c-1 payload bytes
and NUL-terminates; the returned length is always the untruncated size.
-/

namespace IntFmt

/-- snprintf-style write: returns `(buffer, requiredLength)`.
The buffer has length `cap`. Every write index is `< cap`. -/
def snprintfSpec (payload : List Nat) (cap : Nat) : List Nat × Nat :=
  if cap = 0 then
    ([], payload.length)
  else
    let room := cap - 1
    let taken := payload.take room
    -- taken ++ [0] ++ padding zeros to length `cap`
    let buf := taken ++ [0] ++ List.replicate (cap - taken.length - 1) 0
    (buf, payload.length)

theorem snprintf_length (payload : List Nat) (cap : Nat) :
    (snprintfSpec payload cap).2 = payload.length := by
  unfold snprintfSpec
  split <;> rfl

theorem snprintf_buf_length (payload : List Nat) (cap : Nat) :
    (snprintfSpec payload cap).1.length = cap := by
  unfold snprintfSpec
  split
  · -- cap = 0
    rename_i h
    simp [h]
  · rename_i hc
    simp [List.length_append, List.length_replicate, List.length_take]
    have : (payload.take (cap - 1)).length ≤ cap - 1 := List.length_take_le _ _
    omega

theorem snprintf_cap0 (payload : List Nat) :
    snprintfSpec payload 0 = ([], payload.length) := rfl

theorem snprintf_cap1 (payload : List Nat) :
    snprintfSpec payload 1 = ([0], payload.length) := by
  unfold snprintfSpec
  simp

theorem snprintf_index_lt_cap (payload : List Nat) (cap : Nat) (i : Nat)
    (hi : i < (snprintfSpec payload cap).1.length) :
    i < cap := by
  have := snprintf_buf_length payload cap
  omega


/-- Milestone 4 (general NUL lemma): if `cap > 0`, a NUL is written at
index `min payload.length (cap-1)` — i.e. at the payload end when it
fits, otherwise at the last byte of the buffer. -/
theorem snprintf_nul (payload : List Nat) (cap : Nat) (hcap : 0 < cap) :
    (snprintfSpec payload cap).1[min payload.length (cap - 1)]? = some 0 := by
  unfold snprintfSpec
  have hne : cap ≠ 0 := Nat.ne_of_gt hcap
  simp [hne]
  have hidx :
      min payload.length (cap - 1) = (payload.take (cap - 1)).length := by
    rw [List.length_take, Nat.min_comm]
  rw [hidx]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

end IntFmt
