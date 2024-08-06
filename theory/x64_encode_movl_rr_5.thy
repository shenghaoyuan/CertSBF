theory x64_encode_movl_rr_5
imports
  Main
  rBPFCommType rBPFSyntax
  x64Syntax BitsOpMore
begin

lemma encode_movl_rr_5: "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 k) (and 1 v)) = Some dst \<Longrightarrow>
    and 1 v \<noteq> 0 \<Longrightarrow>
    bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) (u8_of_bool (and (u8_of_ireg src) 8 \<noteq> 0))) 0 = 0 \<Longrightarrow> False"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: bitfield_insert_u8_def Let_def u8_of_bool_def and_1_eq_1)
  apply (cases "and (u8_of_ireg src) 8 \<noteq> 0", simp_all)
  done

end