# Copyright (C) Ahmad <ahmedparr93@gmail.com>
# SPDX-License-Identifier: AGPL-3.0-only

# Makefile for SUBLEQ Implementations
# Supports formal verification with Racket/Rosette, Lean 4 proofs, and
# differential testing of the Racket, Factor, Forth and Lean machines.

.PHONY: help install-rosette install-deps verify clean metrics oisc \
        test test-racket test-forth test-factor lean lean-check differential all \
        test-factor-fault lean-fault lean-fault-check \
        macros sha256 killer-app bench \
        verify-microcode verify-microcode-mutations

RACKET ?= racket
RACO ?= raco
FACTOR ?= factor
GFORTH ?= gforth
LAKE ?= lake
XLEN ?= 32
RANDOM_PROGRAMS ?= 200
SEED ?= 20261110

help:
	@echo "SUBLEQ Formal Verification Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  install-deps      - Install system packages (cmake, g++, make, git)"
	@echo "  install-rosette   - Install Rosette via raco"
	@echo "  verify-microcode  - Directive-machine Rosette harness (trusted path)"
	@echo "  verify-microcode-mutations - Each injected fault must exit 1"
	@echo "  verify            - Legacy Goldcrest Rosette checks (not trusted)"
	@echo "  oisc              - Run the simple OISC ADD/SUB experiment"
	@echo "  metrics           - Legacy Goldcrest timing run (not trusted)"
	@echo "  test-racket       - rackunit tests (racket/subleq.rkt, racket/subleq-original.rkt, racket/test-subleq.rkt)"
	@echo "  test-forth        - Forth unit tests (gforth): directive machine + fault model"
	@echo "  test-factor       - Factor unit tests: directive machine + fault model"
	@echo "  lean              - Build the Lean 4 project (proofs + executable)"
	@echo "  lean-check        - Reject proof escape hatches / non-standard axioms"
	@echo "  lean-fault        - Build the fault-model Lean project (lean-fault/, its own toolchain)"
	@echo "  lean-fault-check  - Elaborate lean-fault theorems; reject escape hatches / non-standard axioms"
	@echo "  differential      - Compare all four machines on fixtures + random programs"
	@echo "  macros            - Measure and check every sasm macro on both machines (table)"
	@echo "  sha256            - SHA-256 in SUBLEQ vs NIST vectors (racket, forth, factor, lean, original)"
	@echo "  killer-app        - Keystream program: the directive machine vs the original SUBLEQ"
	@echo "  bench             - Instruction counts and wall clock (writes verification-results/bench.md)"
	@echo "  test              - test-*, verify, verify-microcode, mutation self-test, oisc, lean-check, lean-fault-check, differential, sha256, killer-app"
	@echo "  clean             - Remove build artifacts"
	@echo "  all               - install-deps install-rosette verify-microcode verify"

all: install-deps install-rosette verify-microcode verify

install-deps:
	sudo apt-get update
	sudo apt-get install -y cmake g++ make git

install-rosette:
	$(RACO) pkg install --auto --skip-installed rosette

verify-microcode:
	@echo "=== Directive-machine microcode verification ==="
	$(RACKET) racket/microcode/verify.rkt

verify-microcode-mutations:
	@echo "=== Microcode mutation self-test (each fault must exit 1) ==="
	$(RACKET) racket/microcode/verify.rkt --mutation-self-test

# Quarantined Goldcrest harness. Not part of the directive-machine claim.
verify:
	@echo "=== Legacy Goldcrest Rosette checks (not on the trusted path) ==="
	$(RACKET) racket/microcode-legacy/riscv.rkt

oisc:
	@echo "=== Simple OISC ADD/SUB experiment ==="
	$(RACKET) racket/oisc-add.rkt

metrics:
	@echo "=== SUBLEQ RISC-V Formal Verification ==="
	@echo "Start: $$(date -u +%Y-%m-%dT%H:%M:%SZ)"
	@START=$$(date +%s); \
	$(RACKET) racket/microcode-legacy/riscv.rkt; STATUS=$$?; \
	END=$$(date +%s); \
	DURATION=$$((END - START)); \
	echo "=== Metrics ==="; \
	echo "Duration (seconds): $$DURATION"; \
	echo "End: $$(date -u +%Y-%m-%dT%H:%M:%SZ)"; \
	echo "Racket version: $$($(RACKET) --version)"; \
	echo "Exit status: $$STATUS"; \
	exit $$STATUS

test-racket:
	$(RACO) test racket/subleq.rkt racket/subleq-original.rkt \
	  asm/macro-table.rkt programs/sha256.rkt programs/keystream.rkt \
	  racket/test-subleq.rkt

test-forth:
	$(GFORTH) forth/test-subleq.fs
	$(GFORTH) forth/subleq-fault.fs forth/test-subleq-fault.fs < /dev/null

test-factor: test-factor-fault
	$(FACTOR) factor/subleq-tests.factor

# Fault-model tests (factor/test-subleq.factor, from PR #4). That file prints
# PASS/FAIL lines and always exits 0, so the PASS lines are counted here.
test-factor-fault:
	@out=$$($(FACTOR) -e='USE: parser "factor/subleq-fault.factor" run-file "factor/test-subleq.factor" run-file' 2>&1); st=$$?; \
	  printf '%s\n' "$$out"; \
	  want=$$(grep -c '\[ "PASS: ' factor/test-subleq.factor); \
	  got=$$(printf '%s\n' "$$out" | grep -c '^PASS: '); \
	  if [ $$st -ne 0 ] || printf '%s\n' "$$out" | grep -q 'FAIL' || [ "$$got" -ne "$$want" ]; then \
	    echo "factor fault-model tests: FAILED (exit $$st, $$got of $$want PASS)"; exit 1; fi; \
	  echo "factor fault-model tests: $$got of $$want PASS"

lean:
	cd lean && $(LAKE) build

lean-check: lean
	scripts/check-lean-trusted.sh

# Fault-model Lean project (from PR #4), built on its own toolchain
# (lean-fault/lean-toolchain). lake build only builds Main and Subleq, so the
# theorems are elaborated explicitly.
lean-fault:
	cd lean-fault && $(LAKE) build && $(LAKE) env lean Subleq/Theorems.lean

lean-fault-check: lean-fault
	scripts/check-lean-fault-trusted.sh

differential: lean
	FACTOR=$(FACTOR) GFORTH=$(GFORTH) RACKET=$(RACKET) \
	  $(RACKET) verification/differential.rkt --random $(RANDOM_PROGRAMS) --seed $(SEED)

BENCH_ENV = FACTOR=$(FACTOR) GFORTH=$(GFORTH) RACKET=$(RACKET)

macros:
	$(RACKET) asm/macro-table.rkt

sha256: lean
	$(BENCH_ENV) $(RACKET) bench/sha256-vectors.rkt

killer-app: lean
	$(BENCH_ENV) $(RACKET) bench/killer-app.rkt

bench: lean

bench-scripts:
	@echo "Benchmark scripts live in scripts/bench/"
	@echo "  ./scripts/bench/run-all.sh [--repeat N] [--only engines]"
	@echo "  ./scripts/bench/verify-microcode.sh"
	@echo "  ./scripts/bench/differential.sh [N]"
	@echo "  ./scripts/bench/crypto.sh"

	$(BENCH_ENV) $(RACKET) bench/bench.rkt > verification-results/bench.md; \
	  status=$$?; cat verification-results/bench.md; exit $$status

test: test-racket test-forth test-factor verify verify-microcode \
      verify-microcode-mutations oisc lean-check lean-fault-check \
      differential sha256 killer-app

clean:
	rm -rf verification-results lean/.lake lean-fault/.lake racket/compiled verification/compiled \
	  asm/compiled programs/compiled bench/compiled \
	  racket/microcode/compiled racket/microcode-legacy/compiled
	@echo "Cleaned."

ibx:
	@echo "=== IBX-1 butterfly (Racket reference) ==="
	$(RACKET) programs/ibx.rkt

ibx-subleq:
	@echo "=== IBX-1 butterfly on directive SUBLEQ ==="
	$(RACKET) programs/ibx-subleq.rkt

subleq-dis:
	@echo "=== SUBLEQ disassembler ==="
	$(CC) -std=c11 -O2 -o tools/subleq-dis tools/subleq-dis.c
	@echo "built tools/subleq-dis"

disasm-racket:
	@echo "=== Racket SUBLEQ disassembler ==="
	$(RACKET) racket/subleq-dis.rkt

firmware-subleq:
	@echo "=== SUBLEQ firmware abstraction demo ==="
	$(RACKET) programs/firmware/subleq-firmware.rkt

firmware-roundtrip:
	@echo "=== SUBLEQ firmware round-trip + invariants ==="
	$(RACKET) programs/firmware/roundtrip.rkt

firmware-decompile:
	@echo "=== Firmware-aware decompiler ==="
	$(RACKET) programs/firmware/decompiler.rkt

firmware-compare:
	@echo "=== Original vs reconstructed firmware execution ==="
	$(RACKET) programs/firmware/compare-exec.rkt

firmware-semantic:
	@echo "=== Firmware semantic equivalence tests ==="
	$(RACKET) programs/firmware/semantic-test.rkt

firmware-prove:
	@echo "=== Prove decompiled ops == SUBLEQ sequences ==="
	$(RACKET) programs/firmware/prove-semantics.rkt
