theory BitsOpMore4
imports
  Main
  rBPFCommType 
begin
subsection \<open> u16_of_u8_list \<close>

lemma ucast16_ucast8_and_255_eq [simp]: "ucast (((ucast (and v 255))::u8)) = and (v:: u16) 255"
  apply (simp only: ucast_eq)
(**r 
word_of_int (uint (word_of_int (uint (and v 255)))) is

(word_of_int (uint (and v 255)))::u8

word_of_int (uint v_u8)  :: u64

*)
  apply (simp only: uint_word_of_int_eq word_and_def word_of_int_eq_iff)
  apply (simp)
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n
    apply (cases n, simp_all)
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

lemma u16_shl_shr_same: "n \<le> 8 \<Longrightarrow> ((ucast (v::u8) ::u16) << n) >> n = (ucast (v::u8) ::u16)"
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

lemma u16_shl_shr_outside: "n+8 \<le> m \<Longrightarrow> ((ucast (v::u8) ::u16) << n) >> m = (0 ::u16)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps u8_ge_8_bit_false)
  done

lemma n_le_8_plus_lt_16: "(n::nat) \<le> 8 \<Longrightarrow> m \<le> n \<Longrightarrow> k < 16 \<Longrightarrow> n - m \<le> k \<Longrightarrow> k + m - n < 8 \<Longrightarrow> m + k < 16"
  by simp

lemma u16_shl_shr_same_minus: "n \<le> 8 \<Longrightarrow> m \<le> n \<Longrightarrow>
  ((ucast (v::u8) ::u16) << n) >> m = ((ucast (v::u8) ::u16) << (n-m))"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps u8_bit_true_ge_8 n_le_8_plus_lt_16)
  subgoal for k
    by (simp add: add.commute)
  subgoal for k
    by (metis add.commute)
  done

lemma u16_and_or_255_same: "8 \<le> n \<Longrightarrow> (and (or ((v::u16) << n) k) 255) = and k 255"
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

lemma u16_ucast_and_ucast_255_same: "(ucast (and (ucast (v::u8)) (255::u16)) ::u8) = v"
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


lemma le_m_shr_0 : "8 \<le> m \<Longrightarrow> (ucast (v::u8) ::u16) >> m = (0 ::u16)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps u8_ge_8_bit_false)
  done

lemma list_consists_2 : "length l = 2 \<Longrightarrow> l = [l ! 0, l ! Suc 0]"
  by (metis Cons_nth_drop_Suc Suc_leI append.simps(1) drop_eq_Nil
      id_take_nth_drop lessI numeral_2_eq_2 take0 zero_less_Suc)

lemma [simp]: "and (((v::u16) >> 8) << 8) 65280 = and v 65280"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n using bit_power_k_add_m_ge [of 8 8 n] by simp
  subgoal for n using bit_power_k_add_m_ge [of 8 8 n] by simp
  done

lemma bit_255_not_lt_32 : "n < 16 \<Longrightarrow>
  \<not> bit (65280::int) n \<Longrightarrow> bit (255::int) n"
  using bit_power_k_add_m_lt [of n 8  8] apply simp
  using bit_power_k_add_m_lt [of n 0  8] apply simp
  apply blast
  done

lemma u16_of_u8_list_same: "(Some v = u16_of_u8_list l) = (l = u8_list_of_u16 v)"
  apply (unfold u16_of_u8_list_def u8_list_of_u16_def)
  apply (cases "length l \<noteq> 2", simp_all)
  subgoal by fastforce
  subgoal
    apply (rule iffI)
    subgoal
      apply simp
      apply (simp only: bit_eq_iff [of v])
      apply (auto simp add: bit_simps u16_shl_shr_same u16_shl_shr_outside le_m_shr_0
          u16_shl_shr_same_minus u16_and_or_255_same u16_ucast_and_ucast_255_same)

      subgoal using list_consists_2
        by blast
      done

    subgoal
      apply (simp add: bit_eq_iff [of v])
      apply (simp add: bit_or_iff)
      apply (auto simp add: bit_simps)
      subgoal for n
        using bit_255_not_lt_32 by blast
      done
    done
  done

end