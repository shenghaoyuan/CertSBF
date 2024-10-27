theory BitsOpMore2
imports
  Main
  rBPFCommType 
begin

lemma ucast64_ucast8_and_255_eq [bits_more_simp]:
"ucast (((ucast (and v 255))::u8)) = and (v:: u64) 255"
  apply (simp only: ucast_eq uint_word_of_int_eq word_and_def word_of_int_eq_iff)
  apply (auto simp add: bit_simps bit_eq_iff)
  subgoal for n apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal for n5 apply (cases n5, simp_all)
              subgoal for n6 apply (cases n6, simp_all)
                subgoal for n7 apply (cases n7, simp_all)
                  done
                done
              done
            done
          done
        done
      done
    done
  done

lemma u64_shl_shr_same [bits_more_simp]: "n \<le> 56 \<Longrightarrow> ((ucast (v::u8) ::u64) << n) >> n = (ucast (v::u8) ::u64)"
  apply (auto simp add: bit_simps bit_eq_iff)
  subgoal for k apply (cases k, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal for n5 apply (cases n5, simp_all)
              subgoal for n6 apply (cases n6, simp_all)
                subgoal for n6 apply (cases n6, simp_all add: u8_ge_8_bit_false)
                  done
                done
              done
            done
          done
        done
      done
    done
  done

lemma u64_shl_shr_outside [bits_more_simp]: "n+8 \<le> m \<Longrightarrow> ((ucast (v::u8) ::u64) << n) >> m = (0 ::u64)"
  by (auto simp add: bit_simps u8_ge_8_bit_false bit_eq_iff)

lemma nat_le_56 : "(n::nat) \<le> 56 \<Longrightarrow> m \<le> n \<Longrightarrow> k < 64 \<Longrightarrow> n - m \<le> k \<Longrightarrow> k + m - n < 8 \<Longrightarrow> m + k < 64"
  by simp

lemma u64_shl_shr_same_minus [bits_more_simp]: "n \<le> 56 \<Longrightarrow> m \<le> n \<Longrightarrow> ((ucast (v::u8) ::u64) << n) >> m =
  ((ucast (v::u8) ::u64) << (n-m))"
  apply (auto simp add: bit_simps u8_bit_true_ge_8 nat_le_56 bit_eq_iff)
  subgoal for k
    by (simp add: add.commute)
  subgoal for k
    by (metis add.commute)
  done

lemma u8_ge_8_ucast_0 [bits_more_simp]: "8 \<le> m \<Longrightarrow> (ucast (v::u8) ::u64) >> m = (0 ::u64)"
  apply (auto simp add: bit_simps u8_ge_8_bit_false bit_eq_iff)
  done

lemma u64_and_or_255_same [bits_more_simp]: "8 \<le> n \<Longrightarrow> (and (or ((v::u64) << n) k) 255) = and k 255"
  apply (auto simp add: bit_simps bit_eq_iff)
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

lemma u64_ucast_and_ucast_255_same [bits_more_simp]: "(ucast (and (ucast (v::u8)) (255::u64)) ::u8) = v"
  apply (simp only: ucast_eq uint_word_of_int_eq word_and_def word_of_int_eq_iff)
  apply (auto simp add: bit_simps bit_eq_iff)
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

lemma list_consists_8 : "length l = 8 \<Longrightarrow>
  l = [l ! 0, l ! Suc 0, l ! 2, l ! 3, l ! 4, l ! 5, l ! 6, l ! 7]"
  by (metis Cons_nth_drop_Suc One_nat_def add_implies_diff append.simps(1) diff_Suc_1'
      eval_nat_numeral(2) eval_nat_numeral(3) id_take_nth_drop length_0_conv length_tl
      less_Suc_eq list.sel(3) nat_1_add_1
      semiring_norm(26) semiring_norm(27) semiring_norm(28) take0)

lemma u64_ucast_ucast_and_shr_255_shl_same [bits_more_simp]: "n \<le> 56 \<Longrightarrow>
  ((ucast ((ucast (and ((v::u64) >> n) 255)) ::u8) ::u64) << n) =
  ((and ((v::u64) >> n) 255) << n)"
  apply (simp only: ucast_eq uint_word_of_int_eq word_and_def word_of_int_eq_iff)
  apply (auto simp add: bit_simps bit_eq_iff)
  subgoal for n1
  using bit_power_k_minus_1_le [of 8 "n1-n"] by simp
  done

lemma u8_and_2_power_56_eq [bits_more_simp]: "and (((v::u64) >> 56) << 56) 18374686479671623680 = and v 18374686479671623680"
  apply (auto simp add: bit_simps bit_eq_iff)
  subgoal for n using bit_power_k_add_m_ge [of 56 8 n] by simp
  subgoal for n using bit_power_k_add_m_ge [of 56 8 n] by simp
  done

lemma u8_and_2_power_48_eq [bits_more_simp]: "and (((v::u64) >> 48) << 48) 71776119061217280 = and v 71776119061217280"
  apply (auto simp add: bit_simps bit_eq_iff)
  subgoal for n using bit_power_k_add_m_ge [of 48 8 n] by simp
  subgoal for n using bit_power_k_add_m_ge [of 48 8 n] by simp
  done

lemma u8_and_2_power_40_eq [bits_more_simp]: "and (((v::u64) >> 40) << 40) 280375465082880 = and v 280375465082880"
  apply (auto simp add: bit_simps bit_eq_iff)
  subgoal for n using bit_power_k_add_m_ge [of 40 8 n] by simp
  subgoal for n using bit_power_k_add_m_ge [of 40 8 n] by simp
  done

lemma u8_and_2_power_32_eq [bits_more_simp]: "and (((v::u64) >> 32) << 32) 1095216660480 = and v 1095216660480"
  apply (auto simp add: bit_simps bit_eq_iff)
  subgoal for n using bit_power_k_add_m_ge [of 32 8 n] by simp
  subgoal for n using bit_power_k_add_m_ge [of 32 8 n] by simp
  done

lemma u8_and_2_power_24_eq [bits_more_simp]: "and (((v::u64) >> 24) << 24) 4278190080 = and v 4278190080"
  apply (auto simp add: bit_simps bit_eq_iff)
  subgoal for n using bit_power_k_add_m_ge [of 24 8 n] by simp
  subgoal for n using bit_power_k_add_m_ge [of 24 8 n] by simp
  done

lemma u8_and_2_power_16_eq [bits_more_simp]: "and (((v::u64) >> 16) << 16) 16711680 = and v 16711680"
  apply (auto simp add: bit_simps bit_eq_iff)
  subgoal for n using bit_power_k_add_m_ge [of 16 8 n] by simp
  subgoal for n using bit_power_k_add_m_ge [of 16 8 n] by simp
  done

lemma u8_and_2_power_8_eq [bits_more_simp]: "and (((v::u64) >> 8) << 8) 65280 = and v 65280"
  apply (auto simp add: bit_simps bit_eq_iff)
  subgoal for n using bit_power_k_add_m_ge [of 8 8 n] by simp
  subgoal for n using bit_power_k_add_m_ge [of 8 8 n] by simp
  done

lemma bit_255_not_lt_64 [bits_more_simp]: "n < 64 \<Longrightarrow>
  \<not> bit (18374686479671623680::int) n \<Longrightarrow> \<not> bit (71776119061217280::int) n \<Longrightarrow>
  \<not> bit (280375465082880::int) n \<Longrightarrow> \<not> bit (1095216660480::int) n \<Longrightarrow>
  \<not> bit (4278190080::int) n \<Longrightarrow> \<not> bit (16711680::int) n \<Longrightarrow>
  \<not> bit (65280::int) n \<Longrightarrow> bit (255::int) n"
  using bit_power_k_add_m_lt [of n 56 8] apply simp
  using bit_power_k_add_m_lt [of n 48 8] apply simp
  using bit_power_k_add_m_lt [of n 40 8] apply simp
  using bit_power_k_add_m_lt [of n 32 8] apply simp
  using bit_power_k_add_m_lt [of n 24 8] apply simp
  using bit_power_k_add_m_lt [of n 16 8] apply simp
  using bit_power_k_add_m_lt [of n 8  8] apply simp
  using bit_power_k_add_m_lt [of n 0  8] apply simp
  apply blast
  done

lemma u64_of_u8_list_same [bits_more_simp]: "(Some v = u64_of_u8_list l) = (l = u8_list_of_u64 v)"
  apply (unfold u64_of_u8_list_def u8_list_of_u64_def)
  apply (cases "length l \<noteq> 8", simp_all)
  subgoal by fastforce
  subgoal
    apply (rule iffI)
    subgoal
      apply (simp add: bits_more_simp)
        using list_consists_8 by blast

    subgoal
      apply (auto simp add: bit_eq_iff bit_simps bits_more_simp)
      subgoal for n
        using bit_255_not_lt_64 by blast
      done
    done
  done
end