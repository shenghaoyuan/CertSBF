.open:

.PHONY: generator
.PHONY: micro-test
.PHONY: clean
.PHONY: macro-test

generator:
	@cd ./rbpf/step_test_random && cargo run -- $(num)


micro-test:
	@cd ./exec_semantics && \
	eval $$(opam env) && \
	ocamlc -c step_test.ml && \
	ocamlfind ocamlc -o step -package yojson -linkpkg step_test.cmo step.ml && \
	./step

macro-test:
	@cd ./exec_semantics && \
	ocamlc -c interp_test.ml && \
	ocamlc -o test interp_test.cmo test.ml && \
	./test

clean:
	@cd ./exec_semantics
	@rm -f *.cmo
	@rm -f *.cmi
	@rm -f step
	@rm -f test

