# CertSBF

# Goal
- [x] formalize rbpf assembler + disassembler, prove the consistency: i.e. `assembler (disassembler bin) = Some bin`, and `disassembler (assembler asm) = Some asm`
- [ ] formalize the rbpf semantics (`interpreter.rs`)
  - [ ] ALU (version control)
  - [ ] JUMP (should be trivial)
  - [ ] MEM (check memory `translate_memory_access`)
  - [ ] CALL / EXIT (BPF-to-BPF Calls `push_frame`)
- [ ] optimize the rbpf interpreter (e.g. `opcode masking`) and prove that the optimization is correct
- [ ] _More: formalize rbpf's verifier, static analysis, memory model, and JIT compiler (correctness proof) ..._

# How to install
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

# adding the following libs when install on WSL
# Ubuntu 22.04.3 LTS (GNU/Linux 5.15.153.1-microsoft-standard-WSL2 x86_64)
sudo apt-get install libxi6 libxtst6 libxrender1 fontconfig

make
```

# x64 Reference
As Solana rBPF has a x86_64 JIT compiler which involves of ISA instructions encoding formats, we refer to [x64 Manual](https://cdrdv2.intel.com/v1/dl/getContent/671200), and if you read the comment with `P123` in the isabelle/hol file, which means, the source text description could be found in the x64 Manual `Page 123`. Good Luck~


# Code Statistics
1. install the `cloc` tool
```shell
sudo apt-get install cloc
``` 
2. run the following command to get the lines of code. Note that currently `cloc` doesn't support Isabelle/HOL now, we specify the lanuage to OCaml because both use `(* *)` as comments.
```shell
make code
```