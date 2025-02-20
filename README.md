# A complete formal semantics of eBPF instruction set architecture for Solana



## 1. Introduction

The artifact contains the code, formal proof and tests of our eBPF instruction set architecture for Solana.

1. We begin with a complete formal semantics of the Solana eBPF bytecode in Isabelle/HOL, which facilitates the formalization of the eBPF interpreter.
2. We also extend SBPF ISA formalization to the main components of the Solana eBPF virtual machine, covering the proofs of assembler-disassembler consistency, verifier safety, and semantics preservation of a subset of the x64 JIT compiler. All the proofs are developed in Isabelle/HOL and could be compiled by `make`  in the artifact.
3. We also introduce a validation framework that extracts the executable semantics from our formalization to OCaml language and test it against the original implementation of the Solana eBPF interpreter. The artifact includes the extracted code along with the glue code in OCaml, as well as over 100,000 micro-benchmarks and the Solana test suite for macro-benchmarks. Use `make micro-test` and `make macro-test` to compile and run the tests.

As claimed in Section 1.2 of our paper, the contributions of this paper include:

- Complete Semantics of Solana eBPF ISA,
- Semantics Validation, and
- Solana VM Formalization.

These contributions are directly supported by the artifact, which repsectively aligns with the points 1, 3, 2  listed above.

- URL: https://zenodo.org/records/14586436 (DOI: 10.5281/zenodo.14586436)
- Anonymous GitHub: https://anonymous.4open.science/r/SBPF-EC62/



## 2. Hardware Dependencies

Note that we only test our project on

- Windows 11 + WSL2 (Ubuntu 22.04 LTS)
- Ubuntu 22.04 LTS

plus `CPU: Intel(R) Core(TM) Ultra 7 155H   1.40 GHz` + `RAM 32G` + `Core: 16`

_We record how we install all necessary packages on a fresh Ubuntu22.04 environment._ see `intall_log.md`



## 3. Getting Started Guide

Welcome to the SBPF ISA Semantics and Validation Framework! This guide will help you set up the necessary environment within approximately 5 minutes.

### 3.1 Set up

- **[Isabelle/HOL 2024](https://isabelle.in.tum.de/)**
  - Installation Path: `/YOUR-PATH/Isabelle2024`

- **[Isabelle AFP](https://www.isa-afp.org/download/) (Archive of Formal Proofs)** 
  - Installation Path: `/YOUR-PATH/afp`
  - Simply download the latest AFP release (e.g., `afp-2024-09-23`)

```shell
# set isabelle PATH and update shell environment
vim  ~/.bashrc # export PATH=$PATH:/YOUR-PATH/Isabelle2024/bin:...
source ~/.bashrc

# test isabelle/hol
isabelle version 
# expected：Isabelle2024

# config AFP
cd /YOUR-PATH/afp/thys
isabelle components -u . # Add AFP to isabelle’s dependencies

# go to our repo folder and open this project in jedit
cd /OUR-REPO
```

- **Rust**
  - Installation Instructions: [Rust Installation](https://www.rust-lang.org/tools/install)
  - For our environment:

```shell
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

rustc --version
# expected: rustc 1.85.0
```

- **OCaml and Related Packages**

1. Install opam

   ```
   sudo apt install opam
   ```

   - In the case you fail to install opam:

     - You may need to add the `PPA` repository before installing opam.

     ```shell
     sudo add-apt-repository ppa:avsm/ppa
     sudo apt update
     ```

     - You may need to change your source list to `focal` source If the above step fails.

2. Install ocaml by opam

   ```shell
   # install ocaml
   opam init
   opam switch create sbpf ocaml.4.13.1
   # update your environment
   opam switch set sbpf
   eval $(opam env)
   
   # verify the current switch
   opam switch list
   #   switch  compiler      description
   ->  sbpf     ocaml.4.13.1  sbpf
   # verify ocaml location
   which ocaml
   # example: `/home/bob/.opam/sbpf/bin/ocaml`
   ```

   - Note ocaml above 4.14 version may not work correctly.
   - If you encounter any warnings during this process, execute `eval $(opam env)`, restart your computer/VM, and run the command `eval $(opam env)` again.

3. Install necessary packages

   ```shell
   # install all the dependencies listed in the CertSBF.opam.locked file
   opam install ./CertSBF.opam.locked
   
   #check installed packages
   opam list
   # Packages matching: installed
   	# Name             # Installed  
   -> 	ocamlfind           1.9.6       
   	yojson              2.2.2       
   	...					...
   ```

   - We expect that other later versions of these packages should also work correctly.
   - If you encounter any warnings during the installation, they are generally safe to ignore as long as they do not affect the program's functionality.

- **Cloc Tool**

```shell
sudo apt-get install cloc
```

- **Additional Libraries (for WSL2 users)**

```shell
sudo apt install libxi6 libxtst6 libxrender1 fontconfig
```

### 3.2 Basic Testing

Since we use the `Make` tool to build and manage the entire project, the basic testing process is quite straightforward with `make`.  Please refer to the **Step by Step Instructions** section for guidance.



## 4. Step by Step Instructions

This section provides detailed instructions to reproduce the experiments and activities that support the conclusions in our paper.

### 4.1 SBPF ISA Semantics

#### 4.1.1 Check the SBPF ISA semantics

- This command starts up the IDE of Isabelle/HOL (JEdit), opens the `Interpreter.thy` file, and checks the semantics automatically.

```shell
# Go to the root directory of this repo
make
```

#### 4.1.2 Link to paper

| Paper                       | Code                                                         |
| --------------------------- | ------------------------------------------------------------ |
| Syntax (Section 4.1, Fig 4) | `theory/rBPFSyntax.thy#L41`                                  |
| Semantics (Section 4.2)     | `theory/Interpreter.thy#L510`, `theory/Interpreter.thy#L608` |

### 4.2 Semantics Validation 

- We have two sets of benchmarks for validating semantics:

  - **`Macro-test`**: Compiles and runs program-level tests using the Solana official test suite in `tests/rbpf/tests/execution.rs`.

  - **`Micro-test`**: Compiles and runs instruction-level tests using the generated cases (100 tests by default).

```shell
# Go to the root directory of this repo
make macro-test
make micro-test
# Warnings like `this pattern-matching is not exhaustive` can be ignored
```

- (Optional)  We also provide `make generator num=X` to generate X random instruction test cases. 

```shell
# Go to the root directory of this repo
# For example, to generate and run 100000 tests
make generator num=100000
make micro-test
```

#### 4.2.1 Link to paper

| Paper                            | Code                                                         |
| -------------------------------- | ------------------------------------------------------------ |
| Validation Framework (Section 5) | isabell/hol: glue code1 `theory/Interpreter.thy#L651` + glue code2 `theory/Interpreter.thy#L683` + extraction declration `theory/bpf_generator.thy#L15`, OCaml: glue code `tests/exec_semantics/glue.ml`, interpreter_test `tests/exec_semantics/interp_test.ml`, step_test `tests/exec_semantics/step_test.ml` |

### 4.3 Solana VM applications

#### 4.3.1 Solana Assembler and Disassembler (Section 6.1)

| Paper                           | Code                             |
| ------------------------------- | -------------------------------- |
| Solana Assembler                | `theory/Assembler.thy#L227`      |
| Solana Disassembler             | `theory/Disassembler.thy#L515`   |
| Consistency Proof (Theorem 6.3) | `theory/ConsistencyProof.thy#L8` |


#### 4.3.2 Solana Verifier (Section 6.2)

| Paper                             | Code                            |
| --------------------------------- | ------------------------------- |
| Solana Verifier                   | `theory/verifier.thy#L235`      |
| Solana Verifier Proof (Lemma 6.4) | `theory/VerifierSafety.thy#L13` |

#### 4.3.3 Solana x64 JIT Compiler (Section 6.3)

| Paper                 | Code                                                         |
| --------------------- | ------------------------------------------------------------ |
| x64 model             | `theory/x64Semantics.thy`                                    |
| x64 equivalence proof | `theory/x64DecodeProof.thy#L11`: has sufficiently provided the infrastructure for proving the Solana JIT correctness |
| Solana JIT            | `theory/JITCommType.thy#L264`                                |
| Solana JIT Proof      | `theory/bpfConsistencyAux.thy` |

### 4.4 Code Statistics (Section 7.1)

- Run the following command to get the lines of code

```shell
# Go to the root directory of this repo
make code
```



## 5. Reusability Guide

### 5.1 Formalization
In the paper, we show three examples for reusing our formal syntax and semantics.
### 5.1.1 Syntax

The formal syntax of our model could be used for other static analysis, for example, translating the Solana bytecode into CFG ( control flow graph) for further optimizations.
```ocaml
(* ./theory/rBPFSyntax.thy *)
datatype bpf_instruction = 
  BPF_LD_IMM            dst_ty imm_ty imm_ty | 
  (* BPF_LDX class *)
  BPF_LDX memory_chunk  dst_ty src_ty off_ty |
  (* BPF_ST/BPF_STX class *)
  BPF_ST  memory_chunk  dst_ty snd_op off_ty |
  ...
```
The existing `verifier` model is a template for reusability: The current Solana verifier only does some basic checks, it could be extended with more Linux eBPF verifier features. 
```ocaml
(* ./theory/verifier.thy *)
definition verifier :: "bpf_bin ⇒ SBPFV ⇒ func_map ⇒ bool ⇒ bool" where
```

### 5.1.2 Semantics
The formal semantics of our model could be used for other verification, for example, consider verified compilers from other high-level languages (e.g., C or Rust) to Solana bytecode, or from Solana bytecode to other target architectures (e.g., ARM or RISC-V).

```ocaml
(* ./theory/Interpreter.thy *)
fun step :: "u64 ⇒ bpf_instruction ⇒ reg_map ⇒ mem ⇒ stack_state ⇒ SBPFV ⇒
  func_map ⇒ bool ⇒ u64 ⇒ u64 ⇒ u64 ⇒ bpf_state" where
  ...

fun bpf_interp :: "nat ⇒ bpf_bin ⇒ bpf_state ⇒ bool ⇒ u64 ⇒ bpf_state" where
...
```
The existing `JIT` model is a template for reusability: The current artifact only proves some basic x86-64 ALU instructions, it could be extended with other instructions or other targets. 
```ocaml
(* ./theory/bpfConsistencyAux.thy *)
lemma orq_subgoal_rr_generic:
  assumes ...
       a4:"... = step fuel bins rs m ss is_v1 ..." and
       a5:"Next reg' m'  = exec_instr xins sz reg m" and
       a6:"(∀ r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" 
  shows "(∀ r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
```



### 5.2 Validation Framework

#### 5.2.1 Glue Code (Section 5.1)

- The glue code we integrate into the executable semantics at the OCaml layer is designed to be adaptable to similar use cases. This is because Isabelle/HOL automatically translates the `Word` library into an unambiguous format, which is **not human-readable** but consistent.
- We introduce the following functions to convert the OCaml code extracted by Isabelle/HOL into a usable form: 
  - **int_of_standard_int / int_list_of_standard_int_list**: These functions convert the native `int64` / `int64 list` types from the OCaml standard library to the `int` / `int list` types (we call it `myint`) generated by Isabelle/HOL.
  - **bpf_interp_test**: This function offers a user-friendly interface for testing, using only `int`-related types. This simplifies the testing process by avoiding the need to input other data types.


```ocaml
(* ./tests/exec_semantics/interp_test.ml *)
val int_of_standard_int : int64 -> myint
val int_list_of_standard_int_list : int64 list -> myint list
val bpf_interp_test : int64 int -> int64 list ...

(* ./tests/exec_semantics/test.ml *)
open Interp_test

let lp = Interp_test.int_list_of_standard_int_list test_case.lp_std in
let lm = Interp_test.int_list_of_standard_int_list test_case.lm_std in
...
let result = Interp_test.bpf_interp_test lp lm ..
```



#### 5.2.2 Customize Test Cases

- To run customized program-level tests, you can navigate to `./tests/exec_semantics/test.ml` and add your own test. The following example outlines the structure of a test case:
  - **SBPF Binary Code**: A list of bytes, generated by the Solana rbpf assembler.
  - **Memory Region**: A list of bytes that maps from an `int64` address to a byte.
  - **Syscall Interface**: A list of bytes, though not used in this case since we don't consider test cases involving system calls.
  - **Test Result**: `true` for normal tests and `false` for expectation tests.
  - **SBPF Instruction Version**: Either 1 or 2.
  - **Instruction Count**: The number of instructions executed.
  - **Expected Result**: The result generated by the Solana rbpf after running the test case.


```ocaml 
let test_cases = [
  (*
    / sbpf assembly code
    mov32 r1, 1
    mov32 r0, r1
    exit
  *)
  {
    dis = "test_mov";                            (* Description of the test *)
    lp_std = [180L; 1L; 0L; 0L; 1L; 0L; 0L; 0L;   (* SBPF binary code *)
              188L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 
              149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];                                 (* Memory region *)
    lc_std = [];                                 (* Syscall interface, not used here *)
    isok = true;                                 (* Test result: true for normal tests *)
    v = 2L;                                      (* SBPF instruction version *)
    fuel = 3L;                                   (* Instruction count *)
    result_expected = 0x01L;                     (* Expected result *)
  };
]
```

- To run customized instruction-level tests, you can navigate to `./tests/data/ocaml_in.json` and add your own test. To avoid redundancy, we will focus on explaining the parts that differ from program-level tests:
  - **Register Map**: A randomly generated `int64` SBPF register map from `r0` to `r9`. Note that `r0` is always set to `0` for special instructions (e.g., memory load), which need an extra register to store the return result.
  - **Destination register**: The register where the test result is stored.
  - **Program counter**: The final state of the Program Counter (PC) register.

```json
  {
    "dis": "div r2, 1602358370",							// Description of the test
    "lp_std": [												// SBPF binary code
      "0x37","0x01","0x00","0x00",
      "0x62","0x0C","0x82","0x5F"
    ],
    "lr_std": [												// Register Map
      "0x0000000000000000",
      "0xF4E4C7CAC29A21B8",
      "0x6A5B61236C67D43F",
      "0x5F7B322164C7AF21",
      "0x19FD779B6887B44B",
      "0xA292FCF87FCCC5AC",
      "0x9035EE5D8AF15E0B",
      "0x569AFA5E4607F42C",
      "0x1B5ED1DC1AADE3E0",
      "0x4B0A8B676C7BCF0C"
    ],
    "lm_std": [],											// Memory Region
    "lc_std": [],											// Syscall interface
    "v": "0x1",												// SBPF instruction version
    "fuel": "0x1",											// Instruction count
    "index": "0x2",											// Destination register 
    "ipc": "0x1",											// Program counter
    "result_expected": "0x29069F5D9"						// Expected result
  },
```

## 6. Proof Artifact Guide
see [Proof Artifact](proof_artifact.md)