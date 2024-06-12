include Makefile.config

.open:

.PHONY: open

# from https://github.com/seL4/l4v/issues/627
# L4V_ARCH=X64 ../bin/isabelle jedit -d . -l AutoCorres

DEFAULT_FILE = $(CURDIR)/theory/Disassembler.thy

open:
	cd $(ISABELLE_DIR)/autocorres-1.10 \
	&& L4V_ARCH=X64 ../bin/isabelle jedit -d . -l AutoCorres $(DEFAULT_FILE)

