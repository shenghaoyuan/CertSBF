theory x64_encode_mov_rm_4
imports
  Main
  rBPFCommType rBPFSyntax
  x64Syntax BitsOpMore
begin

lemma encode_mov_rm_4_subgoal_1 : "and 15 (v::u8) \<noteq> 0 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> \<not> bit v 3 \<Longrightarrow>
  \<not> bit v 0 \<Longrightarrow> \<not> bit (v >> 2) 0 \<Longrightarrow> False"
  apply (simp only: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal
          by (metis numeral_2_eq_2)
        subgoal for n3 apply (cases n3, simp_all)
          by (metis numeral_3_eq_3)
        done
      done
    done
  done

lemma encode_mov_rm_4: "
  and 15 v \<noteq> 0 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow> \<not> bit v 3 \<Longrightarrow>
  ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (k >> 3)) (and 1 (v >> 2))) = Some dst \<Longrightarrow>
  ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 k) (and 1 v)) = Some src \<Longrightarrow>
    bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0)
      (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg src) 8 \<noteq> 0)) 0)
        (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0))) 0 = 0 \<Longrightarrow> False"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def)
  apply simp
  apply (cases "bit v 0"; cases "bit (v >> 2) 0", simp_all)
  using encode_mov_rm_4_subgoal_1 by blast

end
