.open:

.PHONY: open code

# from https://github.com/seL4/l4v/issues/627
# L4V_ARCH=X64 ../bin/isabelle jedit -d . -l AutoCorres

DEFAULT_FILE = $(CURDIR)/theory/Interpreter.thy

open:
	isabelle jedit -d . $(DEFAULT_FILE)

code:
	@echo "Analyzing Coq statistics"
	@echo "SBPF Syntax"
	cd theory && cloc --force-lang="OCaml" Mem.thy Val.thy ebpf.thy rBPFCommType.thy rBPFSyntax.thy vm_state.thy
	@echo "SBPF Semantics"
	cd theory && cloc --force-lang="OCaml" Interpreter.thy InterpreterSafety.thy rBPFDecoder.thy
	@echo "SBPF Verifier"
	cd theory && cloc --force-lang="OCaml" vm.thy verifier.thy VerifierSafety.thy
	@echo "SBPF Assembler-Disassembler"
	cd theory && cloc --force-lang="OCaml" Assembler.thy ConsistencyCommProof.thy ConsistencyProof.thy ConsistencyProof1.thy ConsistencyProof2.thy Disassembler.thy
	@echo "SBPF JIT"
	cd theory && cloc --force-lang="OCaml" JIT.thy JITCommType.thy bpfConsistency.thy bpfConsistencyAux.thy rustCommType.thy x86.thy x86CommType.thy
	@echo "SBPF x64 Model"
	cd theory && cloc --force-lang="OCaml" x64Assembler.thy x64Syntax.thy x64Semantics.thy x64Disassembler.thy
	@echo "SBPF x64 Proof"
	cd theory && cloc --force-lang="OCaml" BitsOpMore.thy BitsOpMore2.thy BitsOpMore3.thy BitsOpMore4.thy x64C*.thy x64De*.thy  x64E*.thy  x64P*.thy  x64_*.thy
	@echo "SBPF Executable Semantics"
	cd tests && cloc --force-lang="OCaml" interp_test.ml

