/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Kernel identity of the parsed `.dec` text with the assembled image.

`intfmtDecText` is the concatenation of the generated newline-terminated
line literals (not `include_str`). `check-image.sh`, hooked as a
`lake build` extraDep target (`checkArtifact`), binds those literals to
the official assembled artifact and its SHA-256.
-/

import IntFmt.DecBindA
import IntFmt.DecBindB
import IntFmt.DecBindC

namespace IntFmt

set_option maxHeartbeats 0

def intfmtDecText : String := decTextA ++ decTextB ++ decTextC

theorem extract_intfmtImage_all :
    intfmtImage.extract 0 2323 = intfmtImage := by
  have : 2323 = intfmtImage.size := intfmtImage_size.symm
  rw [this]
  simpa using (Array.extract_size (xs := intfmtImage))

theorem parseDecText_intfmtDecText :
    parseDecText intfmtDecText = intfmtImage := by
  have hAB : listEndsWS (decTextA ++ decTextB).toList := by
    rw [toList_append]
    exact listEndsWS_append _ _ ws_textA ws_textB
  have hsz : 2323 ≤ intfmtImage.size := by
    rw [intfmtImage_size]
    decide
  have hsplit := extract_split3 intfmtImage 800 1600 2323
    (by decide) (by decide) hsz
  rw [intfmtDecText]
  rw [parseDecText_append (decTextA ++ decTextB) decTextC hAB]
  rw [parseDecText_append decTextA decTextB ws_textA]
  rw [parse_textA, parse_textB, parse_textC]
  rw [← image_textA, ← image_textB, ← image_textC, hsplit, extract_intfmtImage_all]

theorem program_identity_parsed :
    parseDecText intfmtDecText = intfmtImage ∧
    intfmtImage.size = 2323 :=
  ⟨parseDecText_intfmtDecText, intfmtImage_size⟩

end IntFmt
