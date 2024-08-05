theory x64EncodeProof
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler
begin
lemma x64_decode_encode_consistency:
  "x64_decode pc l = Some (length l_bin, ins) \<Longrightarrow> (Some l_bin = x64_encode ins \<and> list_in_list l_bin pc l)"
  apply (cases ins; simp_all)

  done

end