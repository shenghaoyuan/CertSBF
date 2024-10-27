theory x64DecodeProof1
imports
  Main
  rBPFCommType x86CommType
  x64Assembler x64Disassembler
begin

lemma list_nth_right: "v = l!n \<Longrightarrow> l!n = v" using HOL.sym by simp

lemma if_false_eq: "a \<noteq> b \<Longrightarrow> (if a = b then c else d) = d" using HOL.if_not_P
  by argo 

lemma construct_rex_to_u8_neq_144: "construct_rex_to_u8 b0 b1 b2 b3 \<noteq> 144"
  apply (unfold construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_of_bool_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma x64_encode_decode_consistency:
  "list_in_list l_bin pc l \<Longrightarrow> Some l_bin = x64_encode ins \<Longrightarrow>
    x64_decode pc l = Some (length l_bin, ins)"
  apply (cases ins; simp add: Let_def)

  subgoal for rd rs
    apply (simp add: split: if_split_asm; erule conjE)
    subgoal
      apply (drule HOL.sym [of _ "l ! Suc pc"])
      apply (simp add: x64_decode_def
          bitfield_extract_u8_def bitfield_insert_u8_def ireg_of_u8_def)
      apply (simp add: Let_def)
(*
    apply (cases ins; simp add: Let_def construct_rex_to_u8_neq_144) *)
(*
  apply (subst if_false_eq, simp) *)



end