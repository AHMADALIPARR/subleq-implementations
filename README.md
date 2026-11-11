# SUBLEQ Implementations

Collection of SUBLEQ (Subtract and Branch if Less or Equal) virtual machine implementations and related code extracted and organized from various sources.

## Languages / Targets

- **Forth**: Simple stack-based VM word
- **Factor**: Sequence-based step function
- **Racket**: Full interpreter with step limit and halt conditions
- **Rosette / Racket**: Formal model, microcode, and disassembler for a SUBLEQ-based RISC-V implementation
- **NASM**: x86 assembly implementation of the core step
- **Microcode**: Gate-level description of subtractor, flags, and branch logic (plus ATS2 verified primitive)
- **RISC-V**: SUBLEQ sequences implementing RISC-V arithmetic, jumps, branches, bit logic, and shifting operations

## Structure

- `forth/` - Forth implementation
- `factor/` - Factor implementation
- `racket/` - Racket interpreter + Rosette formal model (`model.rkt`, `microcode.rkt`, `disassemble.rkt`, `riscv.rkt`, `oisc-add.rkt`)
- `nasm/` - NASM assembly
- `microcode/` - Low-level gate and flag logic
- `riscv/` - SUBLEQ-based RISC-V instruction implementations (source form)
- `examples/` - Example SUBLEQ programs (loops, etc.)

### Simple OISC experiment

`racket/oisc-add.rkt` is a deliberately limited first verification experiment. It defines the SUBLEQ semantics explicitly, then symbolically verifies a four-instruction program that computes `output = A + B` (checking the result, exit PC, and source preservation).

Run it with:

```bash
racket racket/oisc-add.rkt
```

These are educational / experimental snippets for exploring one-instruction-set computing and formal verification with Rosette.

## License

GNU Affero General Public License v3 (AGPLv3). See the [LICENSE](LICENSE) file for the full text.
