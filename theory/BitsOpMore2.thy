theory BitsOpMore2
imports
  Main
  rBPFCommType 
begin


lemma [simp]: "bit (18374686479671623680::int) n \<Longrightarrow> 56 \<le> n"
  (**r proof could be find from BitsBadProof.thy *)
  sorry

lemma ucast64_ucast8_and_255_eq [simp]: "ucast (((ucast (and v 255))::u8)) = and (v:: u64) 255"
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

lemma [simp]: "n \<ge> 8 \<Longrightarrow> \<not>bit (v::u8) n"
  apply (rule impossible_bit)
  apply simp
  done

lemma [simp]: "n \<le> 56 \<Longrightarrow> ((ucast (v::u8) ::u64) << n) >> n = (ucast (v::u8) ::u64)"
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
                  done
                done
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "n+8 \<le> m \<Longrightarrow> ((ucast (v::u8) ::u64) << n) >> m = (0 ::u64)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  done

lemma [simp]: "(n::nat) \<le> 56 \<Longrightarrow> m \<le> n \<Longrightarrow> k < 64 \<Longrightarrow> n - m \<le> k \<Longrightarrow> k + m - n < 8 \<Longrightarrow> m + k < 64"
  by simp

lemma [simp]: "bit (v::u8) n \<Longrightarrow> n < 8"
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

lemma [simp]: "n \<le> 56 \<Longrightarrow> m \<le> n \<Longrightarrow> ((ucast (v::u8) ::u64) << n) >> m = ((ucast (v::u8) ::u64) << (n-m))"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for k
    by (simp add: add.commute)
  subgoal for k
    by (metis add.commute)
  done

lemma [simp]: "8 \<le> m \<Longrightarrow> (ucast (v::u8) ::u64) >> m = (0 ::u64)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  done

lemma [simp]: "8 \<le> n \<Longrightarrow> (and (or ((v::u64) << n) k) 255) = and k 255"
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

lemma [simp]: "(ucast (and (ucast (v::u8)) (255::u64)) ::u8) = v"
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

lemma [simp]: "length l = 8 \<Longrightarrow> l = [l ! 0, l ! Suc 0, l ! 2, l ! 3, l ! 4, l ! 5, l ! 6, l ! 7]"
  apply (cases l, simp_all)
  subgoal for a0 l apply (cases l, simp_all)
    subgoal for a1 l apply (cases l, simp_all)
      subgoal for a2 l apply (cases l, simp_all)
        subgoal for a3 l apply (cases l, simp_all)
          subgoal for a4 l apply (cases l, simp_all)
            subgoal for a5 l apply (cases l, simp_all)
              subgoal for a6 l apply (cases l, simp_all)
                done
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "bit (255::int) n \<Longrightarrow> n < 8"
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

lemma [simp]: "n \<le> 56 \<Longrightarrow> ((ucast ((ucast (and ((v::u64) >> n) 255)) ::u8) ::u64) << n) =
  ((and ((v::u64) >> n) 255) << n)"
  apply (simp only: ucast_eq)
  apply (simp only: uint_word_of_int_eq word_and_def word_of_int_eq_iff)
  apply simp
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  done

lemma bit_power_k_minus_1_le: "bit (2^k -1::int) n \<longleftrightarrow> n < k"
  apply (simp only: bit_iff_odd)
  by (simp add: even_decr_exp_div_exp_iff' linorder_not_le)

lemma bit_power_k_minus_1_le_56 [simp]: "bit (0xffffffffffffff::int) n \<longleftrightarrow> n < 56"
  using bit_power_k_minus_1_le [of 56 n] by simp

(*
lemma [simp]: "bit (2^(k+m)-2^k::int) n \<Longrightarrow> k \<le> n"
  apply (simp only: bit_iff_odd) *)

lemma [simp]: "and (((v::u64) >> 56) << 56) 18374686479671623680 = and v 18374686479671623680"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  done

lemma [simp]: "and (((v::u64) >> 48) << 48) 71776119061217280 = and v 71776119061217280" sorry

lemma [simp]: "and (((v::u64) >> 40) << 40) 280375465082880 = and v 280375465082880" sorry

lemma [simp]: "and (((v::u64) >> 32) << 32) 1095216660480 = and v 1095216660480" sorry

lemma [simp]: "and (((v::u64) >> 24) << 24) 4278190080 = and v 4278190080" sorry

lemma [simp]: "and (((v::u64) >> 16) << 16) 16711680 = and v 16711680" sorry

lemma [simp]: "and (((v::u64) >> 8) << 8) 65280 = and v 65280" sorry

lemma [simp]: "(v::u64) =
    or (and ((v >> 56) << 56) 18374686479671623680)
     (or (and ((v >> 48) << 48) 71776119061217280)
       (or (and ((v >> 40) << 40) 280375465082880)
         (or (and ((v >> 32) << 32) 1095216660480) (or (and ((v >> 24) << 24) 4278190080)
            (or (and ((v >> 16) << 16) 16711680) (or (and ((v >> 8) << 8) 65280) (and v 255)))))))"
  apply (simp add: bit_eq_iff)
  apply (simp add: bit_or_iff)
  (**r 
  apply (rule allI) *)
  apply (auto simp add: bit_simps)
  subgoal for n



lemma [simp]: "(Some v = u64_of_u8_list l) = (l = u8_list_of_u64 v)"
  apply (unfold u64_of_u8_list_def u8_list_of_u64_def)
  apply (cases "length l \<noteq> 8", simp_all)
  subgoal by fastforce
  subgoal
    apply (rule iffI)
    subgoal by simp

    subgoal
      apply (simp add: bit_eq_iff)
      apply (simp add: bit_or_iff)


      done
    done
  sorry *)

(*lemma [simp]: "u8_list_of_u32 v = l \<Longrightarrow> u32_of_u8_list2 l = Some v " 
  apply (unfold u8_list_of_u32_def u32_of_u8_list2_def,simp)
  apply (cases l)
  subgoal by simp
  subgoal for v1 l1
    apply (auto)
    subgoal
      apply(cases l1)
      subgoal by simp
      subgoal for v2 l2
        apply(cases l2)
        subgoal by simp
        subgoal for v3 l3
          apply(cases l3)
          subgoal by simp
          subgoal for v4 l4
            apply (cases l4)
             apply (auto)
            apply(cases v)
            subgoal for n*)


end