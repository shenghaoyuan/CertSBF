theory x64_encode_movl_rr_5
imports
  Main
  rBPFCommType 
  x64Syntax BitsOpMore
begin

lemma encode_movl_rr_5: "and 15 (v >> 4) = 4 \<Longrightarrow>
    and 15 v \<noteq> 0 \<Longrightarrow>
    and 3 (k >> 6) = 3 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (k >> 3)) (and 1 (v >> 2))) = Some src \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (k)) (and 1 v)) = Some dst \<Longrightarrow>
    \<not> bit v 3 \<Longrightarrow>
    \<not> bit v (Suc 0) \<Longrightarrow>
    and 1 v \<noteq> 0 \<Longrightarrow>
    bitfield_insert_u8 4 4
     (bitfield_insert_u8 3 (Suc 0)
       (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0)
         (u8_of_bool (and (u8_of_ireg src) 8 \<noteq> 0)))
       0) 4 = 64  \<Longrightarrow> False
"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp add: bitfield_insert_u8_def Let_def u8_of_bool_def and_1_eq_1)
  apply (cases "and (u8_of_ireg src) 8 \<noteq> 0", simp_all)
  done

end