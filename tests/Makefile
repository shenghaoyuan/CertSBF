.open:

.PHONY: test_step


test_step:
	@echo "Step Test"
	ocamlc -c step_test.ml
	ocamlfind ocamlc -o step -package yojson -linkpkg step_test.cmo step.ml
	./step

