# Proof Artifact
## Step-by-step instructions

All formalization and proofs are conducted in Isabelle 2024, relying on the Word library from the Isabelle AFP. To build and compile the proof, please follow the installation steps outlined in the README.md file for Isabelle/HOL and AFP.

## Paper-to-artifact correspondence guide
### Link to definitions/theorems in paper

Here explains how each of the definitions and theorems in the paper corresponds to the formalizations in the artifact.

| Definition/ Theorem                        | Paper                | File                              | Name of formalization                     | Location |
| ------------------------------ | -------------------- | --------------------------------- | ----------------------------------------- | -------- |
| Program state $S$ | Page 7, Sect. 4.2 | `theory/Interpreter.thy`       | datatype  bpf_state       |   #L52       | 
| semantics of 32-bit ALU instructions  $eval\_aop32$ | Page 8, Sect. 4.2 |   `theory/Interpreter.thy             `                   |           definition eval_alu32                        |  #L136        |
| semantics of byte-sway instructions $to\_be$                    | Page 9, Sect. 4.2 | `theory/Interpreter.thy` | definition eval_be |    #L252      |
| semantics of byte-sway instructions $to\_le$                    | Page 9, Sect. 4.2 | `theory/Interpreter.thy` | definition eval_le |    #L232      |
| semantics of jump instructions $eval\_cond$                    | Page 10, Sect. 4.2 | `theory/Interpreter.thy` | definition eval_jump |    #L401      |
|    semantics of memory load                   | Page 10, Sect. 4.2 | `theory/Mem.thy` | definition loadv | #L95      |
| semantics of memory store                    | Page 10, Sect. 4.2 | `theory/Mem.thy` | definition storev |    #L105      |
| semantics of byte-sway instructions $to\_le$                    | Page 9, Sect. 4.2 | `theory/Interpreter.thy` | definition eval_le |    #L232      |
| semantics of jump instructions $eval\_cond$                    | Page 10, Sect. 4.2 | `theory/Interpreter.thy` | definition eval_jump |    #L401      |
| pop frame from stack                  | Page 10, Sect. 4.2 | `theory/Interpreter.thy` | definition pop_frame |    #L482      |
|  push frame to stack                 | Page 10, Sect. 4.2 | `theory/Interpreter.thy` | definition push_frame | #L422      |
| 6.1 Assembler implies disassembler | Page 17, Sect. 6.1 | `theory/ConsistencyProof1.thy`       | lemma assemble_disassemble_consistency       |   #L9       |
| 6.2 Disassembler implies assembler | Page 17, Sect. 6.1 |   `theory/ConsistencyProof2.thy`                                |           lemma disassemble_assemble_consistency                              |  #L52        |
| 6.3 Consistency                    | Page 17, Sect. 6.1 | `theory/ConsistencyProof.thy` | lemma x64assemble_disassemble_consistency |    #L8      |
| 6.4 Step safety                    | Page 18, Sect. 6.2 | `theory/VerifierSafety.thy`       | lemma verifier_step_safe                  |    #13      |
| 6.5 Mini-JIT correctness           | Page 20, Sect. 6.3 |  `theory/bpfConsistencyAux.thy`                                 |     lemma   addq_subgoal_rr_generic, </br>lemma subq_subgoal_rr_generic, </br>lemma andq_subgoal_rr_generic, </br>lemma movq_subgoal_rr_generic, </br>lemma xorq_subgoal_rr_generic, </br>lemma orq_subgoal_rr_generic                                   |   #L152,  #L176, #L199, #L223, #L247, #L270      |


### Outline of the proof structure

The following outlines the structure of our proof, which includes the formal semantics of the Solana eBPF bytecode and the proofs of  main components of the Solana eBPF virtual machine.

├── theory

│ └── rBPFSyntax -- Syntax (Section 4.1, Fig 4)

│ └── Interpreter.thy -- Semantics (Section 4.2)

│ └── Assembler.thy -- Solana Assembler (Section 6.1)

│ └── Disassembler.thy -- Solana Disassembler  (Section 6.1)

│ └── ConsistencyProof.tex -- Consistency Proof (Theorem 6.3)

│ └── verifier. -- Solana Verifier  (Section 6.2)

│ └── verifierSafety.thy -- Solana Verifier Proof (Lemma 6.4)	

│ └── x64Semantics.thy -- x64 Model (Section 6.3)

│ └── x64DecodeProof.thy -- x64 Proof

│ └── JITCommType.thy -- Solana JIT

│ └── bpfConsistencyAux.thy -- Solana JIT Proof

The `theory/` folder also includes other auxiliary files, we skip those details here, the root directory contains a session graph (`session_graph.pdf`) to explain the relation between the theories in those files and the main above theories.

## Check unproved hypotheses in the proof

- The code does not contain any unfinished proofs. To verify this, you can use the command `grep -i "sorry" *` in the `theory/` directory to search for unresolved proofs in Isabelle/HOL.
- The code does not use any extra axioms. To check it, use the command `grep -i "axiomatization" *` in the `theory/` directory.

**Note that the only instance of "axiomatization" appears in the file `theory/x64DecodeProof.thy`. It was used to accelerate the proof process. The lemma has since been proved, and you can comment out the code below the axiom (#L15 in `theory/x64DecodeProof.thy`) to review the completed proof.**