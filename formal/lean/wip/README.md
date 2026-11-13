Work-in-progress drafts, not part of `lake build`.

The kernel theorem `parseDecText intfmtDecText = intfmtImage` now lives
in `IntFmt/ParseJoin.lean` (and `ParseJoinA/B/C.lean`), composing the
named chunk lemmas in small groups. The earlier 50-line `catStrings`
composition in this directory exceeded the kernel memory budget and is
kept only as a historical draft.
