# CertSBF

# Goal
- [ ] formalize rbpf assembler + disassembler, prove the consistency: i.e. `assembler (disassmbler bin) = Some bin`, and `disassembler (assmbler asm) = Some asm`
- [ ] formalize the rbpf semantics (`interpreter.rs`)
- [ ] optimize the rbpf interpreter (e.g. `opcode masking`) and prove that the optimization is correct
- [ ] _More: formalize rbpf's verifier, static analysis, memory model, and JIT compiler (correctness proof) ..._

# How to install
- [Isabelle/HOL 2024](https://isabelle.in.tum.de/) (please set your PATH with e.g. `/YOUR-PATH/Isabelle2024`)

- [Isabelle AFP](https://www.isa-afp.org/download/)

```shell

# set PATH 
cd ~
vim. bashrc # export PATH=$PATH:/PATH/Isabelle2024/bin:...
source .bashrc

# test isabelle/hol
isabelle version # Isabelle2024

# config AFP
cd /YOUR-PATH/afp/thys
isabelle components -u .

# go to CertSBF folder and open this project in jedit
cd /YOUR-PATH/CertSBF
make
```

# Note
- `static_analysis.rs` is a test for generated jited code
- `static_analysis.rs#276L: self.cfg_nodes.entry(insn.ptr + 1).or_default();` should be removed?
- `static_analysis.rs#311L: std::mem::swap(&mut self.cfg_nodes, &mut cfg_nodes);`, why swap?
- `static_analysis.rs#324L: std::mem::swap(&mut self.cfg_nodes, &mut cfg_nodes);`, now cfg_nodes are empty?
