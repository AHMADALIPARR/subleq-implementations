/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Helpers for composing named `parse_lineXXX` / `image_chunkXXX` lemmas
with `parseDecText_append` and `extract_split`, without reducing the
2323-cell image literal or the full `.dec` text.
-/

import IntFmt.ParseFacts

namespace IntFmt

set_option maxHeartbeats 400000
set_option maxRecDepth 20000

theorem ws_cat (s t : String)
    (hs : listEndsWS s.toList) (ht : listEndsWS t.toList) :
    listEndsWS (s ++ t).toList := by
  rw [toList_append]
  exact listEndsWS_append _ _ hs ht

theorem parse_append_eq (s t : String) (cs ds : Array UInt16)
    (hs : listEndsWS s.toList)
    (hps : parseDecText s = cs)
    (hpt : parseDecText t = ds) :
    parseDecText (s ++ t) = cs ++ ds :=
  (parseDecText_append s t hs).trans
    ((congrArg (fun a => a ++ parseDecText t) hps).trans
      (congrArg (fun a => cs ++ a) hpt))

theorem size_ge {n : Nat} (h : n ≤ 2323) : n ≤ intfmtImage.size := by
  rw [intfmtImage_size]
  exact h

theorem extract_append_eq (s mid e : Nat) (left right : Array UInt16)
    (hsm : s ≤ mid) (hme : mid ≤ e) (he : e ≤ 2323)
    (hl : intfmtImage.extract s mid = left)
    (hr : intfmtImage.extract mid e = right) :
    intfmtImage.extract s e = left ++ right := by
  have hs := extract_split intfmtImage s mid e hsm hme (size_ge he)
  have hL := congrArg (fun a => a ++ intfmtImage.extract mid e) hl
  have hR := congrArg (fun a => left ++ a) hr
  exact (hs.symm.trans hL).trans hR

theorem extract_all :
    intfmtImage.extract 0 2323 = intfmtImage := by
  have : 2323 = intfmtImage.size := intfmtImage_size.symm
  rw [this]
  simpa using (Array.extract_size (xs := intfmtImage))

end IntFmt
