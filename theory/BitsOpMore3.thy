theory BitsOpMore3
imports
  Main
  rBPFCommType 
begin
subsection \<open> u32_of_u8_list \<close>

lemma u32_shl_shr_same: "n \<le> 24 \<Longrightarrow> ((ucast (v::u8) ::u32) << n) >> n = (ucast (v::u8) ::u32)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for k
    apply (cases k, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal for n5 apply (cases n5, simp_all)
              subgoal for n6 apply (cases n6, simp_all)
                subgoal for n6 apply (cases n6, simp_all)
                  by (metis add_2_eq_Suc' add_Suc_shift not_add_less2 numeral_Bit0 u8_bit_true_ge_8)
                done
              done
            done
          done
        done
      done
    done
  done

lemma u32_shl_shr_outside: "n+8 \<le> m \<Longrightarrow> ((ucast (v::u8) ::u32) << n) >> m = (0 ::u32)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps u8_ge_8_bit_false)
  done

lemma [simp]: "(n::nat) \<le> 24 \<Longrightarrow> m \<le> n \<Longrightarrow> k < 32 \<Longrightarrow> n - m \<le> k \<Longrightarrow> k + m - n < 8 \<Longrightarrow> m + k < 32"
  by simp

lemma u32_shl_shr_same_minus: "n \<le> 24 \<Longrightarrow> m \<le> n \<Longrightarrow>
  ((ucast (v::u8) ::u32) << n) >> m = ((ucast (v::u8) ::u32) << (n-m))"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps u8_bit_true_ge_8)
  subgoal for k
    by (simp add: add.commute)
  subgoal for k
    by (metis add.commute)
  done

lemma u32_and_or_255_same: "8 \<le> n \<Longrightarrow> (and (or ((v::u32) << n) k) 255) = and k 255"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for t apply (cases t, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal for n5 apply (cases n5, simp_all)
              subgoal for n6 apply (cases n6, simp_all)
                subgoal for n6 apply (cases n6, simp_all)
                  done
                done
              done
            done
          done
        done
      done
    done
  done

lemma u32_ucast_and_ucast_255_same: "(ucast (and (ucast (v::u8)) (255::u32)) ::u8) = v"
  apply (simp only: ucast_eq)
  apply (simp only: uint_word_of_int_eq word_and_def word_of_int_eq_iff)
  apply simp
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n apply (cases n, simp_all)
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
  done



lemma [simp]: "8 \<le> m \<Longrightarrow> (ucast (v::u8) ::u32) >> m = (0 ::u32)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps u8_ge_8_bit_false)
  done

lemma list_consists_4 : "length l = 4 \<Longrightarrow>
  l = [l ! 0, l ! Suc 0, l ! 2, l ! 3]"
  by (smt (z3) add_2_eq_Suc' length_0_conv length_Suc_conv nth_Cons_0
      nth_Cons_Suc numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0)

lemma [simp]: "(Some v = u32_of_u8_list l) = (l = u8_list_of_u32 v)"
  apply (unfold u32_of_u8_list_def u8_list_of_u32_def)
  apply (cases "length l \<noteq> 4", simp_all)
  subgoal by fastforce
  subgoal
    apply (rule iffI)
    subgoal apply simp

    subgoal
      apply (simp add: bit_eq_iff)
      apply (simp add: bit_or_iff)
      apply (auto simp add: bit_simps u32_shl_shr_same u32_shl_shr_outside
          u32_shl_shr_same_minus u32_and_or_255_same u32_ucast_and_ucast_255_same)
      subgoal using list_consists_4 
      done
    done
  done

end