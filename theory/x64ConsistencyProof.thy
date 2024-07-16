theory x64ConsistencyProof
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler
begin

lemma CA1 [simp]: "x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm"
  (**r it is proven in x64ConsistencyProof1.thy *)
  sorry
lemma CA2 [simp]: "x64_disassemble l_bin = Some l_asm \<Longrightarrow> x64_assemble l_asm = Some l_bin"
  (**r it is proven in x64ConsistencyProof2.thy *)
  sorry

lemma assemble_disassemble_consistency_iff:
"(x64_assemble l_asm = Some l_bin) = (x64_disassemble l_bin = Some l_asm)"
  by (blast intro: CA1 dest: CA2)

end