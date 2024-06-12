# CertSBF

# Goal
- [ ] formalize rbpf assember + disassember, prove the consistency: i.e. `assember (disassmber bin) = Some bin`, and `disassember (assmber asm) = Some asm`
- [ ] formalize the rbpf semantics (`interpreter.rs`)
- [ ] optimize the rbpf interpreter (e.g. `opcode masking`) and prove that the optimization is correct
- [ ] _More: formalize rbpf's verifier, static analysis, memory model, and JIT compiler (correctness proof) ..._

# How to install
- [Isabelle/HOL 2023](https://isabelle.in.tum.de/) (please set your PATH with e.g. `/YOUR-PATH/Isabelle2023`)
- [AutoCorres 1.10](https://github.com/seL4/l4v/releases/tag/autocorres-1.10)

```shell
# 1. assume the current folder is the root of CertSBF
# 2. assume you has downloaded Isabelle2023 and autocorres

# unzip autocorres on the folder of the Isabelle/HOL home folder
tar -zxvf YOUR-AUTOCORRES-DIR/autocorres-1.10.tar.gz -C /YOUR-PATH/Isabelle2023/

# confige info
./configure --isabelledir=/YOUR-PATH/Isabelle2023

# open Isabelle/HOL with autocorres
make
```
