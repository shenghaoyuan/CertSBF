theory x64_encode_movl_rr_1
imports
  Main
  rBPFCommType rBPFSyntax
  x64Syntax
begin

lemma encode_movl_rr_1_subgoal_1 [simp]: "n < 8 \<Longrightarrow> 
  \<not> bit (192::int) n \<Longrightarrow> \<not> bit (7::int) n \<Longrightarrow> bit (56::int) n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma encode_movl_rr_1_subgoal_2 [simp]: "n < 8 \<Longrightarrow> 
  \<not> bit (192::int) n \<Longrightarrow> \<not> bit (7::int) n \<Longrightarrow> 3 \<le> n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done


lemma encode_movl_rr_1_subgoal_3 [simp]: "n < 8 \<Longrightarrow> 
  \<not> bit (192::int) n \<Longrightarrow> \<not> bit (7::int) n \<Longrightarrow> bit (71::int) n \<Longrightarrow> False"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma encode_movl_rr_1_subgoal_4 [simp]: "n < 8 \<Longrightarrow>
  \<not> bit (192::int) n \<Longrightarrow> \<not> bit (56::int) n \<Longrightarrow> bit (8::int) n \<Longrightarrow> False"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        done
      done
    done
  done

lemma encode_movl_rr_1_subgoal_5 [simp]:
  "\<not> bit (192::int) n \<Longrightarrow> \<not> 3 \<le> n \<Longrightarrow> bit (8::int) n \<Longrightarrow> False"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma encode_movl_rr_1_subgoal_6 [simp]:
  "\<not> bit (192::int) n \<Longrightarrow> \<not> 3 \<le> n \<Longrightarrow> bit (56::int) n \<Longrightarrow> False"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma encode_movl_rr_1_subgoal_7 [simp]: "n < 8 \<Longrightarrow> bit (v::u8) n \<Longrightarrow>
  \<not> bit (192::int) n \<Longrightarrow> bit (8::int) n \<Longrightarrow> bit v (3 + (n - 3))"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        using numeral_3_eq_3 by argo
      done
    done
  done

lemma encode_movl_rr_1_subgoal_8[simp]: "n < 8 \<Longrightarrow>
  \<not> bit (192::int) n \<Longrightarrow> bit (8::int) n \<Longrightarrow> bit (71::int) n \<Longrightarrow> False"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        done
      done
    done
  done

lemma encode_movl_rr_1_subgoal_9 [simp]: "n < 8 \<Longrightarrow> bit (v::u8) n \<Longrightarrow>
  \<not> bit (192::int) n \<Longrightarrow> bit (56::int) n \<Longrightarrow> bit v (3 + (n - 3))"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal using numeral_3_eq_3 by argo
        subgoal for n4 apply (cases n4, simp_all)
          subgoal
            by (simp add: numeral_Bit0) 
          subgoal for n5 apply (cases n5, simp_all)
            by (simp add: eval_nat_numeral(3) numeral_Bit0)
          done
        done
      done
    done
  done

lemma encode_movl_rr_1_subgoal_10 [simp]: "n < 8 \<Longrightarrow>
  \<not> bit (192::int) n \<Longrightarrow> bit (56::int) n \<Longrightarrow> bit (71::int) n \<Longrightarrow> False"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            done
          done
        done
      done
    done
  done

lemma and_3_shr_6_3_6 [simp]: "and 3 (v >> 6) = 3 \<Longrightarrow> bit v (Suc (Suc (Suc (Suc (Suc (Suc 0))))))"
  by (metis Suc3_eq_add_3 bit_0 bit_and_iff bit_iff_odd_drop_bit bit_numeral_Bit1_0 numeral_3_eq_3 numeral_Bit0)

lemma and_3_shr_6_3_7 [simp]: "and 3 ((v::u8) >> 6) = 3 \<Longrightarrow> bit v (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="1" in spec)
  apply (simp add: eval_nat_numeral(2) eval_nat_numeral(3))
  done


lemma encode_movl_rr_1_subgoal_11 [simp]: "and 3 (v >> 6) = 3 \<Longrightarrow>
  u8_of_ireg src = and (and 7 (v >> 3)) (- 9) \<Longrightarrow> u8_of_ireg dst = and (and 7 v) (- 9) \<Longrightarrow>
  n < 8 \<Longrightarrow> bit (192::int) n \<Longrightarrow> bit v n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done


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
    apply (simp add: bit_or_iff)
    apply (auto simp add: bit_simps)
    subgoal using encode_movl_rr_1_subgoal_3 by blast
    subgoal using encode_movl_rr_1_subgoal_4 by blast
    subgoal using encode_movl_rr_1_subgoal_5 by blast
    subgoal using encode_movl_rr_1_subgoal_6 by blast
    subgoal using encode_movl_rr_1_subgoal_8 by blast
    subgoal using encode_movl_rr_1_subgoal_10 by blast
    done
  done
end