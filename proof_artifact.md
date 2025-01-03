# Proof Artifact
## Step-by-step instructions

All formalization and proofs are conducted in Isabelle 2024, relying on the Word library from the Isabelle AFP. To build and compile the proof, please follow the installation steps outlined in the README.md file for Isabelle/HOL and AFP.

## Paper-to-artifact correspondence guide
### Link to definitions/theorems in paper

Here explains how each of the definitions and theorems in the paper corresponds to the formalizations in the artifact.

| Definition/ Theorem                        | Paper                | File                              | Name of formalization                     | Location |
| ------------------------------ | -------------------- | --------------------------------- | ----------------------------------------- | -------- |
| 6.1 Assembler implies disassembler | Page 17, Sect. 6.1 | `theory/ConsistencyProof1.thy`       | lemma assemble_disassemble_consistency       |   #L9       |
| 6.2 Disassembler implies assembler | Page 17, Sect. 6.1 |   `theory/ConsistencyProof2.thy`                                |           lemma disassemble_assemble_consistency                              |  #L52        |
| 6.3 Consistency                    | Page 17, Sect. 6.1 | `theory/ConsistencyProof.thy` | lemma x64assemble_disassemble_consistency |    #L8      |
| 6.4 Step safety                    | Page 18, Sect. 6.2 | `theory/VerifierSafety.thy`       | lemma verifier_step_safe                  |    #13      |
| 6.5 Mini-JIT correctness           | Page 20, Sect. 6.3 |  `theory/bpfConsistencyAux.thy`                                 |     lemma   addq_subgoal_rr_generic, </br>lemma subq_subgoal_rr_generic, </br>lemma andq_subgoal_rr_generic, </br>lemma movq_subgoal_rr_generic, </br>lemma xorq_subgoal_rr_generic, </br>lemma orq_subgoal_rr_generic                                   |   #L152,  #L176, #L199, #L223, #L247, #L270      |


### Outline of the proof structure

The following outlines the structure of our proof, which includes the formal semantics of the Solana eBPF bytecode and the proofs of  main components of the Solana eBPF virtual machine.

**Solana BPF ISA semantics (Section 4)**

| Paper                       | Code                                                         |
| --------------------------- | ------------------------------------------------------------ |
| Syntax (Section 4.1, Fig 4) | `theory/rBPFSyntax.thy#L41`                                  |
| Semantics (Section 4.2)     | `theory/Interpreter.thy#L510`, `theory/Interpreter.thy#L608` |

**Solana Assembler and Disassembler (Section 6.1)**

| Paper                           | Code                             |
| ------------------------------- | -------------------------------- |
| Solana Assembler                | `theory/Assembler.thy#L227`      |
| Solana Disassembler             | `theory/Disassembler.thy#L515`   |
| Consistency Proof (Theorem 6.3) | `theory/ConsistencyProof.thy#L8` |

**Solana Verifier (Section 6.2)**

| Paper                             | Code                            |
| --------------------------------- | ------------------------------- |
| Solana Verifier                   | `theory/verifier.thy#L235`      |
| Solana Verifier Proof (Lemma 6.4) | `theory/VerifierSafety.thy#L13` |

**Solana x64 JIT Compiler (Section 6.3)**

| Paper                 | Code                                                         |
| --------------------- | ------------------------------------------------------------ |
| x64 model             | `theory/x64Semantics.thy`                                    |
| x64 equivalence proof | `theory/x64DecodeProof.thy#L11`: has sufficiently provided the infrastructure for proving the Solana JIT correctness |
| Solana JIT            | `theory/JITCommType.thy#L264`                                |
| Solana JIT Proof      | `theory/bpfConsistencyAux.thy` |



## Check unproved hypotheses in the proof

The code does not contain any unfinished proofs. To verify this, you can use the command `grep -i "sorry" *` in the `theory/` directory to search for unresolved proofs in Isabelle/HOL.

Note that the only instance of "sorry" appears in the file `theory/x64DecodeProof.thy`. It was used to accelerate the proof process. The lemma has since been proved, and you can comment out the code below "sorry" line (#L16 in `theory/x64DecodeProof.thy`) to review the completed proof.

The code does not use any extra axioms. To check it, use the command `grep -i "axiomatization" *` in the `theory/` directory.