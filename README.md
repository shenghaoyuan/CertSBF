# A complete formal semantics of eBPF instruction set architecture for Solana

# SBPF ISA Semantics
1. install Isabelle/HOL and AFP
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

2. check the SBPF ISA semantics
```shell
make
```

# Validation Framework

1. install OCaml and related packages
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

2. validate semantics
- **`make macro-test`**: Compiles and runs program-level tests using the Solana official test suite in `./test/rbpf/tests/execution.rs`.
- **`make micro-test`**: Compiles and runs instruction-level tests using the generated cases (100 tests by default).
- **`make generator`**: Generate random instruction test cases.
  - Use `make generator num=X` to specify the number of cases.


# Code Statistics
1. install the `cloc` tool
```shell
sudo apt-get install cloc
``` 
2. run the following command to get the lines of code. Note that currently `cloc` doesn't support Isabelle/HOL now, we specify the lanuage to OCaml because both use `(* *)` as comments.
```shell
make code
```


# x64 Reference
As Solana rBPF has a x86_64 JIT compiler which involves of ISA instructions encoding formats, we refer to [x64 Manual](https://cdrdv2.intel.com/v1/dl/getContent/671200), and if you read the comment with `P123` in the isabelle/hol file, which means, the source text description could be found in the x64 Manual `Page 123`. Good Luck~