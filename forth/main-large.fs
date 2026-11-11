\ Copyright (C) Ahmad <ahmedparr93@gmail.com>
\ SPDX-License-Identifier: AGPL-3.0-only

\ forth/main.fs with a larger machine: 4,000,000 memory cells and
\ 1,000,000 input words (the SHA-256 image is about 434,000 cells).
\ Usage: gforth -m 64M forth/main-large.fs INPUT-FILE
\ Everything else (semantics, output format) is forth/subleq.fs + forth/main.fs.

4000000 constant mem-capacity
1000000 constant in-capacity
s" main.fs" included
