theory x64EquivalenceProof
imports
  Main
  rBPFCommType
  x64Assembler x64Disassembler
begin

lemma CA1 [simp]: "list_in_list l_bin pc l \<Longrightarrow> Some l_bin = x64_encode ins \<Longrightarrow> x64_decode pc l = Some (length l_bin, ins)"
  (**r it is proven in x64DecodeProof.thy *)
  sorry

lemma CA2 [simp]: "list_in_list l_bin pc l \<Longrightarrow> x64_decode pc l = Some (length l_bin, ins) \<Longrightarrow> Some l_bin = x64_encode ins"
  (**r it is proven in x64ConsistencyProof2.thy *)
  sorry

lemma assemble_disassemble_equivalence_iff: "list_in_list l_bin pc l \<Longrightarrow> 
(x64_decode pc l = Some (length l_bin, ins)) = (Some l_bin = x64_encode ins)"
  by (blast intro: CA1 dest: CA2)

end