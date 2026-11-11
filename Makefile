# Copyright (C) Ahmad <ahmedparr93@gmail.com>
# SPDX-License-Identifier: AGPL-3.0-only

# Makefile for SUBLEQ Implementations
# Supports formal verification with Racket/Rosette

.PHONY: help install-rosette install-deps verify clean metrics oisc

RACKET ?= racket
RACO ?= raco
XLEN ?= 32

help:
	@echo "SUBLEQ Formal Verification Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  install-deps      - Install system packages (cmake, g++, make, git)"
	@echo "  install-rosette   - Install Rosette via raco"
	@echo "  verify            - Run formal verification suite (symbolic Rosette checks)"
	@echo "  oisc              - Run the simple OISC ADD/SUB experiment"
	@echo "  metrics           - Run verification and print timing metrics"
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
	$(RACKET) racket/riscv.rkt; \
	END=$$(date +%s); \
	DURATION=$$((END - START)); \
	echo "=== Metrics ==="; \
	echo "Duration (seconds): $$DURATION"; \
	echo "End: $$(date -u +%Y-%m-%dT%H:%M:%SZ)"; \
	echo "Racket version: $$($(RACKET) --version)"

clean:
	rm -rf verification-results
	@echo "Cleaned."
