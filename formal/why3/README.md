# formal/why3/ — optional independent path

Why3 is **not** the authoritative proof layer. The official proofs live
in `formal/lean/`. `intfmt.mlw` is a WhyML sketch of the same
specification (unsigned magnitude for `-32768`, saturating / bounded
snprintf, repeated-subtraction divmod).

Why3 and its SMT provers (Alt-Ergo, CVC5, etc.) were **not installed**
on the build host (`why3: not found`; no `opam`). No Why3 proof session
was run, and no Why3 results should be invented. If Why3 is installed
later:

```
why3 prove formal/why3/intfmt.mlw
```
