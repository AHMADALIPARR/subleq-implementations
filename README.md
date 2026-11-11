# SUBLEQ Implementations

Collection of SUBLEQ (Subtract and Branch if Less or Equal) virtual machine implementations and related code extracted and organized from various sources.

## Languages / Targets

- **Forth**: Simple stack-based VM word
- **Factor**: Sequence-based step function
- **Racket**: Full interpreter with step limit and halt conditions
- **NASM**: x86 assembly implementation of the core step
- **Microcode**: Gate-level description of subtractor, flags, and branch logic (plus ATS2 verified primitive)
- **RISC-V**: SUBLEQ sequences implementing RISC-V arithmetic, jumps, branches, bit logic, and shifting operations

## Structure

- `forth/` - Forth implementation
- `factor/` - Factor implementation
- `racket/` - Racket implementation
- `nasm/` - NASM assembly
- `microcode/` - Low-level gate and flag logic
- `riscv/` - SUBLEQ-based RISC-V instruction implementations
- `examples/` - Example SUBLEQ programs (loops, etc.)

These are educational / experimental snippets for exploring one-instruction-set computing.

## License

MIT
