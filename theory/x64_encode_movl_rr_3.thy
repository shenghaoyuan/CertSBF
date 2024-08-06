theory x64_encode_movl_rr_3
imports
  Main
  rBPFCommType rBPFSyntax
  x64Syntax
begin

lemma and_1_eq_1: "\<And> v. (and 1 v \<noteq> 0) = (and 1 v = 1)"
  by (simp add: one_and_eq)


lemma [simp]: "and 1 (v >> 2) = 1 \<Longrightarrow> and (or (and 8 (((v::u8) >> 2) << 3)) (and (and 7 (k >> 3)) (- 9))) 8 \<noteq> 0"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (rule_tac x="3" in exI)
  apply (drule_tac x="0" in spec)
  apply simp
  done


lemma encode_movl_rr_3: "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (k >> 3)) (and 1 (v >> 2))) = Some src \<Longrightarrow>
    and 1 (v >> 2) \<noteq> 0 \<Longrightarrow>
    bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) (u8_of_bool (and (u8_of_ireg src) 8 \<noteq> 0))) 0 = 0 \<Longrightarrow> False"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: bitfield_insert_u8_def Let_def u8_of_bool_def and_1_eq_1)
  apply (cases "and (u8_of_ireg dst) 8 \<noteq> 0", simp_all)
  done

end