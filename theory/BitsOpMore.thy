theory BitsOpMore
imports
  Main
  rBPFCommType
  x64Syntax
begin

lemma [simp]: "and (and (and 7 (v::u8)) (- 9)) 8 = 0"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  done

lemma [simp]: "(and (and 7 (k::u8)) (- 9)) = and 7 k"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        done
      done
    done
  done

lemma and_1_eq_1: "\<And> v. (and 1 v \<noteq> 0) = (and 1 v = 1)"
  by (simp add: one_and_eq)

lemma [simp]: "and 1 ((v::u8) >> 2) = 1 \<Longrightarrow> (and 8 ((v >> 2) << 3) = 8)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for k
    by (simp add: bit_numeral_Bit0_iff)
  subgoal for k apply (cases k, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          apply (drule_tac x="0" in spec)
          apply simp
          done
        done
      done
    done
  done

lemma [simp]: "and 1 (v >> 2) = 1 \<Longrightarrow> and (or (and 8 (((v::u8) >> 2) << 3)) (and (and 7 (k >> 3)) (- 9))) 8 \<noteq> 0"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (rule_tac x="3" in exI)
  apply (drule_tac x="0" in spec)
  apply simp
  done

lemma [simp]: "and (and 7 (v::u8)) 8 = 0"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        done
      done
    done
  done

lemma [simp]: "and (or (and 8 (v::u8)) (and 7 k)) 8 = and 8 v"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        done
      done
    done
  done

lemma [simp]: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit v (Suc (Suc (Suc (Suc (Suc 0))))) = False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="1" in spec)
  apply simp
  by (simp add: numeral_eq_Suc)

lemma [simp]: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit v (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) = True"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="2" in spec)
  apply simp
  by (simp add: numeral_eq_Suc)

lemma [simp]: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit v (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) = False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="3" in spec)
  apply simp
  by (simp add: numeral_eq_Suc)

lemma [simp]: "(and 1 ((v::u8) >> n) = 1) = (bit v n = True)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="0" in spec)
    by (simp add: numeral_2_eq_2)

lemma [simp]: "(and 1 ((v::u8) >> n) = 0) = (bit v n = False)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="0" in spec)
    by (simp add: numeral_2_eq_2)

lemma [simp]: "bit v 2 \<Longrightarrow> bit v (Suc (Suc 0))"
 using numeral_2_eq_2 by argo

lemma [simp]: "\<not> bit (7::int) n \<Longrightarrow> 3 \<le> n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma [simp]: "bit (56::int) n \<Longrightarrow> 3 \<le> n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma and_3_shr_6_1_False [simp]: "and 3 ((v::u8) >> 6) = 1 \<Longrightarrow>
    bit v (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) \<Longrightarrow> False"
  apply (simp only: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (drule_tac x="1" in spec)
    by (smt (verit, best) One_nat_def Suc3_eq_add_3 Suc_eq_plus1 bit_1_0
      linordered_euclidean_semiring_bit_operations_class.bit_numeral_Bit1_Suc_iff
      numeral_Bit0 numeral_Bit1 numeral_eq_one_iff one_less_numeral_iff)

(*
lemma not_7_lt_3 [simp]: "\<not> bit (7::int) n \<Longrightarrow> \<not> 3 \<le> n \<Longrightarrow> False"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done *)

lemma and_8_shl_3_neq_0 [simp]: "(and 8 ((v::u8) << 3) \<noteq> 0) = (bit v 0 = True)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          done
        done
      done
    done

  subgoal
    apply (rule_tac x="3" in exI)
    apply simp
    done
  done

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
            by (simp add: numeral_eq_Suc)
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

lemma encode_movl_rr_1_subgoal_12 [simp]: "and 3 ((k::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow> bit 192 n \<Longrightarrow> bit k n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all add: bit_numeral_Bit0_iff) 
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

lemma encode_movl_rr_1_subgoal_13 [simp]: "and 3 ((k::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  \<not> bit 192 n \<Longrightarrow> bit 56 n \<Longrightarrow> bit 64 n \<Longrightarrow> bit k n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all add: bit_numeral_Bit0_iff) 
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

end
