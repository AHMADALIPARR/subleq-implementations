<!--
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only
-->

# Legacy Goldcrest microcode (not on the trusted path)

These files are the previous Rosette layer, moved here unchanged from
`racket/microcode.rkt`, `racket/model.rkt`, `racket/riscv.rkt`, and
`racket/verify.rkt`. They are a research artifact derived from
ics-jku/goldcrest-microcode-verification. They are **not** part of the
trusted verification claim for the directive machine.

The trusted harness is `racket/microcode/` (`make verify-microcode`). It
checks SUBLEQ sequences against the directive machine in
`semantics/subleq-spec.md`. Nothing in this directory is an input to that
claim, and a passing run here is not evidence about Lean, Racket, Factor,
or Forth.

`make verify` and `make metrics` still run `riscv.rkt` so the old command
keeps working. They are not part of the milestone 1 acceptance criteria.

## Licence notices

The four Racket files were moved byte-for-byte. Their headers are the
headers they had in `racket/`: `SPDX-License-Identifier: AGPL-3.0-only AND MIT`,
the ICS copyright line, the upstream origin, and the pointer to
`LICENSES/MIT-goldcrest.txt`. That MIT text is still at
`LICENSES/MIT-goldcrest.txt`. This move does not relicense them.

`racket/disassemble.rkt` was not moved. Its only change is the module path
of this directory's `model.rkt`, which it still loads. It remains a
Goldcrest-derived tool and is not on the trusted path either.
