# A complete formal semantics of eBPF instruction set architecture for Solana

# Environments
- Windows 11 + WSL2 (Ubuntu 22.04.3 LTS)
- Ubuntu 22.04.4 LTS

# 1. SBPF ISA Semantics
## 1.1 Install Isabelle/HOL and AFP
- [Isabelle/HOL 2024](https://isabelle.in.tum.de/) (please set your PATH with e.g. `/YOUR-PATH/Isabelle2024`)

- [Isabelle AFP](https://www.isa-afp.org/download/) (unzip the AFP to your PATH, e.g. `/YOUR-PATH/afp`)

```shell

# set PATH 
cd ~
vim. bashrc # export PATH=$PATH:/YOUR-PATH/Isabelle2024/bin:...
source .bashrc

# test isabelle/hol
isabelle version # Isabelle2024

# config AFP
cd /YOUR-PATH/afp/thys
isabelle components -u . # Add AFP to ...

# go to CertSBF folder and open this project in jedit
cd /YOUR-PATH/CertSBF

# adding the following libs when install on WSL2 with Ubuntu 22.04.3 LTS (GNU/Linux 5.15.153.1-microsoft-standard-WSL2 x86_64)
sudo apt-get install libxi6 libxtst6 libxrender1 fontconfig
```

## 1.2 Check the SBPF ISA semantics
```shell
make
```

## 1.3 Link to paper

| Paper      | Code      |
| ------------- | ------------- |
| Syntax (Section 4.1, Fig 4) | [rBPFSyntax.thy](theory/rBPFSyntax.thy#L41) |
| Semantics (Section 4.2) | [step](theory/Interpreter.thy#L510), [interpreter](theory/Interpreter.thy#L608) |

# 2. Validation Framework

## 2.1 Install Rust, OCaml and related packages

First, check the Official [Rust web](https://www.rust-lang.org/tools/install) to install Rust.
The following instructions explains how to install OCaml + packages
```shell
# install opam
add-apt-repository ppa:avsm/ppa
apt update
apt install opam

# install ocaml+coq by opam
opam init
# install ocaml
opam switch create sbpf ocaml-base-compiler.4.14.1

eval $(opam env)

opam switch list
#   switch  compiler      description
->  sbpf     ocaml.4.14.1  sbpf

# Once you get a warning, please do `eval $(opam env)` and restart your computer/VM

# make sure your ocaml is 4.14.1 and from `/home/bob/.opam/sbpf/bin/ocaml`
which ocaml

# install necessary packages
opam install ocamlfind yojson
```

## 2.2 Validate semantics
- **`make macro-test`**: Compiles and runs program-level tests using the Solana official test suite in `tests/rbpf/tests/execution.rs`.
- **`make micro-test`**: Compiles and runs instruction-level tests using the generated cases (100 tests by default).
- **`make generator`**: Generate random instruction test cases (by default: 100).
  - Use `make generator num=X` to specify the number of cases.

## 2.3 Link to paper

| Paper      | Code      |
| ------------- | ------------- |
| Validation Framework (Section 5.1) | isabell/hol: [glue code1](theory/Interpreter.thy#L651) + [glue code2](theory/Interpreter.thy#L683) + [extraction declration](theory/bpf_generator.thy#L15), OCaml: [glue code](tests/exec_semantics/glue.ml), [interpreter_test](tests/exec_semantics/interp_test.ml), [step_test](tests/exec_semantics/step_test.ml) |

# 3. Solana VM applications

## 3.1 Solana Assembler and Disassembler (Section 6.1)

| Paper      | Code      |
| ------------- | ------------- |
| Solana Assembler | [isabell/hol code](theory/Assembler.thy#L227) |
| Solana Disassembler | [isabell/hol code](theory/Disassembler.thy#L515) |
| Consistency Proof (Theorem 6.3) | [isabell/hol code](theory/ConsistencyProof.thy#L8) |


## 3.2 Solana Verifier (Section 6.2)

| Paper      | Code      |
| ------------- | ------------- |
| Solana Verifier | [isabell/hol code](theory/verifier.thy#L235) |
| Solana Verifier Proof (Lemma 6.4) | [isabell/hol code](theory/VerifierSafety.thy#L13) |

## 3.3 Solana x64 JIT Compiler (Section 6.3)

| Paper      | Code      |
| ------------- | ------------- |
| x64 model | [x64 semantics](theory/x64Semantics.thy) |
| x64 equivalence proof | [x64 x64_encode_decode_consistency](theory/x64DecodeProof.thy#L11): has sufficiently provided the infrastructure for proving the Solana JIT correctness |
| Solana JIT | [isabell/hol code](theory/JITCommType.thy#L264) |
| Solana JIT Proof | [isabell/hol code0](theory/bpfConsistencyAux.thy), [isabell/hol code1](theory/bpfConsistencyAux1.thy), [isabell/hol code2](theory/bpfConsistencyAux2.thy), [isabell/hol code3](theory/bpfConsistencyAux3.thy) |


# 4. Code Statistics (Section 7.1)
## 4.1 Install the `cloc` tool
```shell
sudo apt-get install cloc
``` 
## 4.2. Run the following command to get the lines of code 
Note that currently `cloc` doesn't support Isabelle/HOL now, we specify the lanuage to OCaml because both use `(* *)` as comments.
```shell
make code
```