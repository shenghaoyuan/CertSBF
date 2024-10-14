theory ConsistencyProof
imports
  Main
  rBPFCommType rBPFSyntax Assembler Disassembler
  ConsistencyProof1 ConsistencyProof2
begin

lemma assemble_disassemble_consistency_iff:
"(assemble l_asm = Some l_bin) = (disassemble l_bin = Some l_asm)"
  by (blast intro: assemble_disassemble_consistency dest: disassemble_assemble_consistency)

(* Sledgehammer suggests:
  using CA1 CA2 by blast *)
(* why the following doesn't work?

by (auto intro: CA1 dest: CA2) 

Answer: auto is too weak, we should use blast instead of auto
*)
end