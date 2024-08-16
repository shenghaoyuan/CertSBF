theory x64_encode_mov_rm_2
imports
  Main
  rBPFCommType rBPFSyntax
  x64Syntax BitsOpMore
begin

lemma encode_mov_rm_2: "
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (k >> 3)) (and 1 (v >> 2))) = Some dst \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 k) (and 1 v)) = Some src \<Longrightarrow>
      bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0)
        (u8_of_bool (and (u8_of_ireg src) 8 \<noteq> 0)) 0)
        (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0))) 1 = (0::u8) \<Longrightarrow> False"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def)
  apply simp
  subgoal by (cases "bit v 0"; cases "bit (v >> 2) 0", simp_all)
  done
end