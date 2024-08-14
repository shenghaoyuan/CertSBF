theory x64_encode_movl_rr_1
imports
  Main
  rBPFCommType rBPFSyntax
  x64Syntax BitsOpMore
begin


lemma encode_movl_rr_1: "
    and 3 (v >> 6) = 3 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (v >> 3)) 0) = Some src \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 v) 0) = Some dst \<Longrightarrow>
    v = bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg dst)) (and 7 (u8_of_ireg src))) 3"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def)
  apply simp
  apply (rule bit_eqI)
  subgoal for n
    apply (auto simp add: bit_simps)
    subgoal using encode_movl_rr_1_subgoal_6 by blast
    done
  done
end