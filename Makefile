# Makefile for SUBLEQ Implementations
# Supports formal verification with Racket/Rosette + Boolector

.PHONY: help install-racket install-rosette install-deps build-boolector verify clean metrics

RACKET ?= racket
RACO ?= raco
XLEN ?= 32

help:
	@echo "SUBLEQ Formal Verification Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  install-deps      - Install system packages (cmake, g++, make, git)"
	@echo "  install-rosette   - Install Rosette and rackunit via raco"
	@echo "  build-boolector   - Clone, build, and install Boolector solver"
	@echo "  verify            - Run formal verification suite"
	@echo "  metrics           - Run verification and print timing metrics"
	@echo "  clean             - Remove build artifacts"
	@echo "  all               - install-deps install-rosette build-boolector verify"

all: install-deps install-rosette build-boolector verify

install-deps:
	sudo apt-get update
	sudo apt-get install -y cmake g++ make git

install-rosette:
	$(RACO) pkg install --auto --skip-installed rosette rackunit

build-boolector:
	git clone --depth 1 https://github.com/boolector/boolector.git || true
	cd boolector && ./contrib/setup-lingeling.sh
	cd boolector && ./contrib/setup-btor2tools.sh
	cd boolector && ./configure.sh
	cd boolector/build && make -j$$(nproc)
	cd boolector/build && sudo make install
	rm -rf boolector
	@echo "Boolector installed."

verify:
	@echo "=== Running SUBLEQ formal verification ==="
	$(RACKET) racket/verify.rkt

metrics:
	@echo "=== SUBLEQ RISC-V Formal Verification ==="
	@echo "Start: $$(date -u +%Y-%m-%dT%H:%M:%SZ)"
	@START=$$(date +%s); \
	$(RACKET) racket/verify.rkt; \
	END=$$(date +%s); \
	DURATION=$$((END - START)); \
	echo "=== Metrics ==="; \
	echo "Duration (seconds): $$DURATION"; \
	echo "End: $$(date -u +%Y-%m-%dT%H:%M:%SZ)"; \
	echo "Racket version: $$($(RACKET) --version)"

clean:
	rm -rf boolector verification-results
	@echo "Cleaned."
