theory ConsistencyProof
imports
  Main
  rBPFCommType rBPFSyntax Assembler Disassembler
begin

lemma CA1 [simp]: "assemble l_asm = Some l_bin \<Longrightarrow> disassemble l_bin = Some l_asm"
  (**r it is proven in ConsistencyProof1.thy *)
  sorry
lemma CA2 [simp]: "disassemble l_bin = Some l_asm \<Longrightarrow> assemble l_asm = Some l_bin"
  (**r it is proven in ConsistencyProof2.thy *)
  sorry

lemma assemble_disassemble_consistency_iff:
"(assemble l_asm = Some l_bin) = (disassemble l_bin = Some l_asm)"
  using CA1 CA2 by blast
(* TBC: why the following doesn't work?
by (auto intro: CA1 dest: CA2) *)



end