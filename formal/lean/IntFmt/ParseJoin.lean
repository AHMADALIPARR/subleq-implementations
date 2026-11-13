/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Kernel identity `parseDecText intfmtDecText = intfmtImage`, obtained
by composing the named per-line `parse_lineXXX` / `image_chunkXXX`
lemmas through `parseDecText_append` and `extract_split`.
`intfmtDecText` is the concatenation of the generated newline-terminated
line literals (not `include_str`). `checkArtifact` binds those literals
to the official assembled artifact and its SHA-256.
-/

import IntFmt.ParseJoinA
import IntFmt.ParseJoinB
import IntFmt.ParseJoinC

namespace IntFmt

set_option maxHeartbeats 800000
set_option maxRecDepth 20000

@[irreducible] def intfmtDecTextAB : String := joinAText ++ joinBText
@[irreducible] def intfmtImageAB : Array UInt16 := joinAImage ++ joinBImage

private theorem ws_AB : listEndsWS intfmtDecTextAB.toList := by
  unfold intfmtDecTextAB
  exact ws_cat joinAText joinBText ws_joinA ws_joinB

private theorem parse_AB :
    parseDecText intfmtDecTextAB = intfmtImageAB := by
  have h := parse_append_eq joinAText joinBText joinAImage joinBImage
    ws_joinA parse_joinA parse_joinB
  unfold intfmtDecTextAB intfmtImageAB
  exact h

private theorem extract_AB :
    intfmtImage.extract 0 1600 = intfmtImageAB := by
  have h := extract_append_eq 0 800 1600 joinAImage joinBImage
    (by decide) (by decide) (by decide)
    extract_joinA extract_joinB
  unfold intfmtImageAB
  exact h

/-- Concatenation of every generated `.dec` line literal. -/
@[irreducible] def intfmtDecText : String := intfmtDecTextAB ++ joinCText

@[irreducible] def intfmtImageJoined : Array UInt16 :=
  intfmtImageAB ++ joinCImage

private theorem parse_joined :
    parseDecText intfmtDecText = intfmtImageJoined := by
  have h := parse_append_eq intfmtDecTextAB joinCText
    intfmtImageAB joinCImage ws_AB parse_AB parse_joinC
  unfold intfmtDecText intfmtImageJoined
  exact h

private theorem extract_joined :
    intfmtImage.extract 0 2323 = intfmtImageJoined := by
  have h := extract_append_eq 0 1600 2323 intfmtImageAB joinCImage
    (by decide) (by decide) (by decide)
    extract_AB extract_joinC
  unfold intfmtImageJoined
  exact h

/-- The parser of the generated line literals yields the assembled image. -/
theorem parseDecText_intfmtDecText :
    parseDecText intfmtDecText = intfmtImage :=
  parse_joined.trans (extract_joined.symm.trans extract_all)

theorem program_identity_parsed :
    parseDecText intfmtDecText = intfmtImage ∧
    intfmtImage.size = 2323 :=
  ⟨parseDecText_intfmtDecText, intfmtImage_size⟩

end IntFmt
