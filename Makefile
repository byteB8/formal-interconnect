# Formal verification of three interconnect blocks with EBMC.
#
#   make prove   unbounded proofs, bounded checks and covers for every block
#   make bugs    seed each bug in bugs/bugs.toml and check it is caught
#   make study   FIFO proof with and without its helper lemma
#   make all     all of the above, and refresh results/
#
# Tool locations default to the no-root installs described in README.md;
# override them with EBMC_BIN=... SPOT_BIN=...

EBMC_BIN ?= $(HOME)/opt/ebmc/usr/bin
SPOT_BIN ?= $(HOME)/opt/spot/bin
export PATH := $(EBMC_BIN):$(SPOT_BIN):$(PATH)

PY := python3

.PHONY: prove bugs study all clean

prove:
	$(PY) scripts/fv.py prove

bugs:
	$(PY) scripts/fv.py bugs

study:
	$(PY) scripts/fv.py study

all:
	$(PY) scripts/fv.py all

clean:
	rm -rf results/cex
