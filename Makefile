# fftadecomp-kit - Makefile
#
# The kit has no repo of its own: it operates on a decomp repo, given as
# DEcomp= (default: current directory) or as an argument.
#
#   make check DEcomp=../fftadecomp
#   make match DEcomp=../fftadecomp ADDR=0x08017514

PYTHON ?= python3
DECOMP ?= .
ROM    ?= baserom.bin
ADDR   ?= 0x08017514
TOOLS   = $(dir $(abspath $(lastword $(MAKEFILE_LIST))))tools

.PHONY: all analyze split check match clean help

all: check

## analyze: ROM -> config/, symbols/, logs/
analyze:
	$(PYTHON) $(TOOLS)/analyze.py $(ROM) $(DECOMP)

## split: analysis -> asm/, files/, symbols/
split:
	$(PYTHON) $(TOOLS)/split.py $(ROM) $(DECOMP)

## check: prove the split reproduces the base ROM byte for byte
check:
	$(PYTHON) $(TOOLS)/rebuild.py $(DECOMP)

## match: compile src/<addr>.c and diff it against the ROM bytes
match:
	$(PYTHON) $(TOOLS)/match.py --root $(DECOMP) $(ADDR)

clean:
	@echo "nothing to clean here - the kit holds no build output"

help:
	@grep -E '^## ' $(MAKEFILE_LIST) | sed 's/^## /  /'