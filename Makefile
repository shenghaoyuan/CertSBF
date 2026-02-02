.open:

.PHONY: open

# from https://github.com/seL4/l4v/issues/627
# L4V_ARCH=X64 ../bin/isabelle jedit -d . -l AutoCorres

DEFAULT_FILE = $(CURDIR)/theory/Interpreter.thy

open:
	isabelle jedit -d . $(DEFAULT_FILE)

