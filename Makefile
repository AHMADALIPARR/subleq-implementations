# SPDX-License-Identifier: AGPL-3.0-or-later
# Makefile for SUBLEQ Implementations
# Supports formal verification with Racket/Rosette, Lean 4 proofs, and
# differential testing of the Racket, Factor, Forth and Lean machines.

.PHONY: help install-rosette install-deps verify clean metrics oisc \
        test test-racket test-forth test-factor lean lean-check differential all

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
	@echo "  verify            - Run formal verification suite (symbolic Rosette checks)"
	@echo "  oisc              - Run the simple OISC ADD/SUB experiment"
	@echo "  metrics           - Run verification and print timing metrics"
	@echo "  test-racket       - rackunit tests (racket/subleq.rkt, racket/subleq-original.rkt)"
	@echo "  test-forth        - Forth unit tests (gforth)"
	@echo "  test-factor       - Factor unit tests"
	@echo "  lean              - Build the Lean 4 project (proofs + executable)"
	@echo "  lean-check        - Reject proof escape hatches / non-standard axioms"
	@echo "  differential      - Compare all four machines on fixtures + random programs"
	@echo "  test              - All of the above except install-*"
	@echo "  clean             - Remove build artifacts"
	@echo "  all               - install-deps install-rosette verify"

all: install-deps install-rosette verify

install-deps:
	sudo apt-get update
	sudo apt-get install -y cmake g++ make git

install-rosette:
	$(RACO) pkg install --auto --skip-installed rosette

verify:
	@echo "=== Running SUBLEQ formal verification (symbolic) ==="
	$(RACKET) racket/riscv.rkt

oisc:
	@echo "=== Simple OISC ADD/SUB experiment ==="
	$(RACKET) racket/oisc-add.rkt

metrics:
	@echo "=== SUBLEQ RISC-V Formal Verification ==="
	@echo "Start: $$(date -u +%Y-%m-%dT%H:%M:%SZ)"
	@START=$$(date +%s); \
	$(RACKET) racket/riscv.rkt; STATUS=$$?; \
	END=$$(date +%s); \
	DURATION=$$((END - START)); \
	echo "=== Metrics ==="; \
	echo "Duration (seconds): $$DURATION"; \
	echo "End: $$(date -u +%Y-%m-%dT%H:%M:%SZ)"; \
	echo "Racket version: $$($(RACKET) --version)"; \
	echo "Exit status: $$STATUS"; \
	exit $$STATUS

test-racket:
	$(RACO) test racket/subleq.rkt racket/subleq-original.rkt

test-forth:
	$(GFORTH) forth/test-subleq.fs

test-factor:
	$(FACTOR) factor/subleq-tests.factor

lean:
	cd lean && $(LAKE) build

lean-check: lean
	scripts/check-lean-trusted.sh

differential: lean
	FACTOR=$(FACTOR) GFORTH=$(GFORTH) RACKET=$(RACKET) \
	  $(RACKET) verification/differential.rkt --random $(RANDOM_PROGRAMS) --seed $(SEED)

test: test-racket test-forth test-factor verify oisc lean-check differential

clean:
	rm -rf verification-results lean/.lake racket/compiled verification/compiled
	@echo "Cleaned."
