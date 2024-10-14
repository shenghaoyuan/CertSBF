.open:

.PHONY: open generator micro-test clean macro-test code clean

# from https://github.com/seL4/l4v/issues/627
# L4V_ARCH=X64 ../bin/isabelle jedit -d . -l AutoCorres

DEFAULT_FILE = $(CURDIR)/theory/Interpreter.thy

open:
	isabelle jedit -d . $(DEFAULT_FILE)

generator:
	@cd ./tests/rbpf/step_test_random && cargo run -- $(num)


micro-test:
	@cd ./tests/exec_semantics && \
	eval $$(opam env) && \
	ocamlc -c step_test.ml && \
	ocamlfind ocamlc -o step -package yojson -linkpkg step_test.cmo step.ml && \
	./step

macro-test:
	@cd ./tests/exec_semantics && \
	ocamlc -c interp_test.ml && \
	ocamlc -o test interp_test.cmo test.ml && \
	./test

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
	@echo "SBPF Validation  Framework"
	cd tests && cloc exec_semantics/glue.ml rbpf/step_test_random/src/*.rs rbpf/step_test_fixed/src/*.rs
	@echo "SBPF Executable Semantics"
	cd tests/exec_semantics && cloc --force-lang="OCaml" interp_test.ml

clean :
	@echo $@
	find . -name "step" -exec rm {} \;
	find . -name "test" -exec rm {} \;
	find . -name "*\.cmi" -exec rm {} \;
	find . -name "*\.cmo" -exec rm {} \;
