### interpreter test

```shell
ocamlc -c interp_test.ml
ocamlc -o test interp_test.cmo test.ml
./test
```





### step test

首先将step.ml中的文件路径改为正确的路径

```
let test_cases = read_test_cases "../data/ocaml_in2.json" in
```

ocaml_in2用于单个测试，ocaml_in1用于多个测试

执行以下：

```
opam install ocamlfind
eval $(opam env)

ocamlc -c step_test.ml
ocamlfind ocamlc -o step -package yojson -linkpkg step_test.cmo step.ml
./step
```



