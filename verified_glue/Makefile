# Makefile for verified glue code
#
# Targets:
#   verify    - Type-check and verify F* modules
#   extract   - Extract to C code via KReMLin
#   clean     - Remove generated files
#
# SPDX-License-Identifier: BSD-2-Clause

# F* paths (adjust as needed)
# Note: Karamel has Python 2.7 dependency issues on modern systems
# We use verification-only mode by default

FSTAR = fstar.exe

# Try to find F* in opam or use system PATH
FSTAR_PATH := $(shell eval $$(opam env 2>/dev/null); which $(FSTAR) 2>/dev/null)
ifeq ($(FSTAR_PATH),)
  $(warning F* not found. Run 'opam install fstar' first.)
endif

# KReMLin is optional (extraction only)
KRML = krml
KRML_PATH := $(shell which $(KRML) 2>/dev/null)
KRML_HOME ?= $(shell opam var karamel:share 2>/dev/null || echo "")

# F* options
# Only include KReMLin paths if available
ifneq ($(KRML_HOME),)
FSTAR_INCLUDES = \
  --include $(KRML_HOME)/krmllib \
  --include $(KRML_HOME)/krmllib/obj
else
FSTAR_INCLUDES =
endif

FSTAR_FLAGS = \
  --cache_checked_modules \
  --cache_dir .cache \
  --odir .extract \
  $(FSTAR_INCLUDES)

# Minimal flags for verification without extraction
FSTAR_VERIFY_FLAGS = \
  --cache_checked_modules \
  --cache_dir .cache

# Source files
# Standalone spec (no LowStar dependency - works without KReMLin)
FSTAR_SPEC = ICS.Glue.Spec.fst

# Full sources (require LowStar/KReMLin for extraction)
FSTAR_SOURCES = \
  ICS.Glue.Types.fst \
  ICS.Glue.CAmkES.fsti \
  ICS.Glue.Inbound.fst \
  ICS.Glue.Outbound.fst

# Modules to extract to C
EXTRACT_MODULES = \
  ICS.Glue.Inbound \
  ICS.Glue.Outbound

# KReMLin options
KRML_FLAGS = \
  -skip-linking \
  -skip-compilation \
  -tmpdir extracted \
  -bundle 'ICS.Glue.*' \
  -no-prefix 'ICS.Glue.Inbound' \
  -no-prefix 'ICS.Glue.Outbound'

.PHONY: all verify extract clean check-tools

all: verify

# Check that F* is installed
check-fstar:
	@eval $$(opam env 2>/dev/null); \
	which $(FSTAR) > /dev/null 2>&1 || \
	  (echo "ERROR: F* not found. Run 'opam install fstar' first." && exit 1)

# Check that KReMLin is installed (optional, for extraction)
check-krml:
	@which $(KRML) > /dev/null 2>&1 || \
	  (echo "WARNING: KReMLin not found. Extraction will not work." && \
	   echo "Note: KReMLin has Python 2.7 dependency issues on modern systems.")

# Type-check only (fast, no full verification)
typecheck: check-fstar .cache
	@echo "=== Type-checking F* modules ==="
	@eval $$(opam env); \
	$(FSTAR) $(FSTAR_VERIFY_FLAGS) --lax $(FSTAR_SOURCES)
	@echo "=== Type-check successful ==="

# Verify all F* modules (type-check + proof obligations)
verify: check-fstar .cache
	@echo "=== Verifying F* modules ==="
	@eval $$(opam env); \
	$(FSTAR) $(FSTAR_VERIFY_FLAGS) $(FSTAR_SOURCES)
	@echo "=== Verification successful ==="

# Verify single module (for development)
verify-%: check-fstar .cache
	@echo "=== Verifying $*.fst ==="
	@eval $$(opam env); \
	$(FSTAR) $(FSTAR_VERIFY_FLAGS) $*.fst
	@echo "=== Verification successful ==="

# Verify standalone spec (no KReMLin needed, just F* + Z3)
verify-spec: check-fstar check-z3 .cache
	@echo "=== Verifying standalone specification ==="
	@eval $$(opam env); \
	$(FSTAR) $(FSTAR_VERIFY_FLAGS) $(FSTAR_SPEC)
	@echo "=== Specification verified ==="

# Type-check spec only (no Z3 needed)
typecheck-spec: check-fstar .cache
	@echo "=== Type-checking standalone specification ==="
	@eval $$(opam env); \
	$(FSTAR) $(FSTAR_VERIFY_FLAGS) --lax $(FSTAR_SPEC)
	@echo "=== Type-check successful ==="

# Check Z3 is installed
check-z3:
	@which z3 > /dev/null 2>&1 || which z3-4.8.5 > /dev/null 2>&1 || \
	  (echo "ERROR: Z3 SMT solver not found." && \
	   echo "Install with: sudo apt-get install z3" && \
	   echo "Then: sudo ln -s /usr/bin/z3 /usr/local/bin/z3-4.8.5" && exit 1)

# Extract verified code to C
extract: verify extracted
	@echo "=== Extracting to C ==="
	$(KRML) $(KRML_FLAGS) \
	  $(addprefix .extract/, $(addsuffix .krml, $(EXTRACT_MODULES)))
	@echo "=== Extraction complete. See extracted/ directory ==="

# Create cache directory
.cache:
	mkdir -p .cache

# Create extraction directory
extracted:
	mkdir -p extracted

# Clean generated files
clean:
	rm -rf .cache .extract extracted *.checked *.krml

# Install F* and KReMLin via opam
install-fstar:
	@echo "=== Installing F* and KReMLin via opam ==="
	opam update
	opam install fstar karamel -y
	@echo "=== Installation complete ==="
	@echo "Run 'eval $$(opam env)' to update PATH"

# Interactive F* (for development)
interactive: check-tools
	$(FSTAR) $(FSTAR_FLAGS) --ide $(filter-out $@,$(MAKECMDGOALS))

# Show F* path info
info:
	@echo "FSTAR_HOME: $(FSTAR_HOME)"
	@echo "KRML_HOME: $(KRML_HOME)"
	@echo "FSTAR: $$(which $(FSTAR) 2>/dev/null || echo 'not found')"
	@echo "KRML: $$(which $(KRML) 2>/dev/null || echo 'not found')"

# Help
help:
	@echo "Verified Glue Code Build System"
	@echo ""
	@echo "Targets:"
	@echo "  verify        - Verify F* modules (type-check + proofs)"
	@echo "  extract       - Extract verified code to C"
	@echo "  install-fstar - Install F* and KReMLin via opam"
	@echo "  clean         - Remove generated files"
	@echo "  info          - Show tool paths"
	@echo ""
	@echo "Requirements:"
	@echo "  - opam (OCaml package manager)"
	@echo "  - F* (installed via opam)"
	@echo "  - KReMLin/Karamel (installed via opam)"
