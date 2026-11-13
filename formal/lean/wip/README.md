Work-in-progress composition of per-line parse/image lemmas into
`parseDecText intfmtDecText = intfmtImage`. The individual line lemmas
in `IntFmt/DecChunks*.lean` and `IntFmt/DecBindData*.lean` kernel-check;
assembling all 146 chunks in one module exceeded the box memory budget
(~13 GiB) during kernel elaboration. These files are not part of
`lake build`.
