theory x64_encode_movq_rr_1
imports
  Main
  rBPFCommType rBPFSyntax
  x64Syntax BitsOpMore
begin

lemma [simp]: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit (v::u8) 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow>
  bit v 0 \<Longrightarrow> bit v 2 \<Longrightarrow> n < 8 \<Longrightarrow> bit v n \<Longrightarrow> bit (77::int) n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal
            by (metis bit_1_0 bit_and_iff bit_numeral_Bit1_0 bit_word_iff_drop_bit_and
                eval_nat_numeral(2) not_bit_numeral_Bit0_0 numeral_3_eq_3
                semiring_norm(26) semiring_norm(27))
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma encode_movq_rr_1_subgoal_1: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit (v::u8) 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow>
  bit v 0 \<Longrightarrow> bit v 2 \<Longrightarrow> n < 8 \<Longrightarrow> bit (77::int) n \<Longrightarrow> bit v n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          using numeral_3_eq_3 by argo
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

lemma encode_movq_rr_1_subgoal_2 [simp]: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit v 3 \<Longrightarrow>
  \<not> bit v (Suc 0) \<Longrightarrow> bit v 0 \<Longrightarrow> bit (v >> 2) 0 \<Longrightarrow> v = 77"
  apply (rule bit_eqI)
  subgoal for n
    apply (auto simp add: bit_simps)
    subgoal using encode_movq_rr_1_subgoal_1 by blast
    done
  done

lemma [simp]: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit (v::u8) 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow>
  bit v 0 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> n < 8 \<Longrightarrow> bit v n \<Longrightarrow> bit (73::int) n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal
        by (metis numeral_2_eq_2) 
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal
            by (metis bit_1_0 bit_and_iff bit_numeral_Bit1_0 bit_word_iff_drop_bit_and
                eval_nat_numeral(2) not_bit_numeral_Bit0_0 numeral_3_eq_3
                semiring_norm(26) semiring_norm(27))
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma encode_movq_rr_1_subgoal_3: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit (v::u8) 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow>
  bit v 0 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> n < 8 \<Longrightarrow> bit (73::int) n \<Longrightarrow> bit v n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          using numeral_3_eq_3 by argo
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

lemma encode_movq_rr_1_subgoal_4 [simp]: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit v 3 \<Longrightarrow>
  \<not> bit v (Suc 0) \<Longrightarrow> bit v 0 \<Longrightarrow> \<not> bit (v >> 2) 0 \<Longrightarrow> v = 73"
  apply (rule bit_eqI)
  subgoal for n
    apply (auto simp add: bit_simps)
    subgoal using encode_movq_rr_1_subgoal_3 by blast
    done
  done

lemma [simp]: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit (v::u8) 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow>
  \<not> bit v 0 \<Longrightarrow> bit v 2 \<Longrightarrow> n < 8 \<Longrightarrow> bit v n \<Longrightarrow> bit (76::int) n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal
            by (metis bit_1_0 bit_and_iff bit_numeral_Bit1_0 bit_word_iff_drop_bit_and
                eval_nat_numeral(2) not_bit_numeral_Bit0_0 numeral_3_eq_3
                semiring_norm(26) semiring_norm(27))
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma encode_movq_rr_1_subgoal_5: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit (v::u8) 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow>
  \<not> bit v 0 \<Longrightarrow> bit v 2 \<Longrightarrow> n < 8 \<Longrightarrow> bit (76::int) n \<Longrightarrow> bit v n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          using numeral_3_eq_3 by argo
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

lemma encode_movq_rr_1_subgoal_6 [simp]: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit v 3 \<Longrightarrow>
  \<not> bit v (Suc 0) \<Longrightarrow> \<not> bit v 0 \<Longrightarrow> bit (v >> 2) 0 \<Longrightarrow> v = 76"
  apply (rule bit_eqI)
  subgoal for n
    apply (auto simp add: bit_simps)
    subgoal using encode_movq_rr_1_subgoal_5 by blast
    done
  done

lemma [simp]: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit (v::u8) 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow>
  \<not> bit v 0 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> n < 8 \<Longrightarrow> bit v n \<Longrightarrow> bit (72::int) n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal
        by (metis numeral_2_eq_2) 
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal
            by (metis bit_1_0 bit_and_iff bit_numeral_Bit1_0 bit_word_iff_drop_bit_and
                eval_nat_numeral(2) not_bit_numeral_Bit0_0 numeral_3_eq_3
                semiring_norm(26) semiring_norm(27))
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma encode_movq_rr_1_subgoal_7: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit (v::u8) 3 \<Longrightarrow> \<not> bit v (Suc 0) \<Longrightarrow>
  \<not> bit v 0 \<Longrightarrow> \<not> bit v 2 \<Longrightarrow> n < 8 \<Longrightarrow> bit (72::int) n \<Longrightarrow> bit v n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal
          using numeral_3_eq_3 by argo
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

lemma encode_movq_rr_1_subgoal_8 [simp]: "and 15 ((v::u8) >> 4) = 4 \<Longrightarrow> bit v 3 \<Longrightarrow>
  \<not> bit v (Suc 0) \<Longrightarrow> \<not> bit v 0 \<Longrightarrow> \<not> bit (v >> 2) 0 \<Longrightarrow> v = 72"
  apply (rule bit_eqI)
  subgoal for n
    apply (auto simp add: bit_simps)
    subgoal using encode_movq_rr_1_subgoal_7 by blast
    done
  done

lemma encode_movq_rr_1_subgoal_9 [simp]: "and 3 ((k::u8) >> 6) = 3 \<Longrightarrow>
    k = or 192 (and (or (and 56 (or (and 64 ((v >> 2) << 6))
      (and 56 ((k >> 3) << 3)))) (and (and 7 (or (and 8 (v << 3)) (and 7 k))) (- 57))) (- 193))"
  apply (rule bit_eqI)
  subgoal for n
    apply (auto simp add: bit_simps)
    subgoal
      using not_7_lt_3 by blast
    subgoal
      using not_7_lt_3 by blast
    subgoal
      using not_7_lt_3 by blast
    subgoal
      using not_7_lt_3 by blast
    subgoal
      using not_7_lt_3 by blast
    subgoal
      using not_7_lt_3 by blast
    subgoal
      using not_7_lt_3 by blast
    subgoal
      using not_7_lt_3 by blast
    subgoal
      using encode_movl_rr_1_subgoal_6 by blast
    subgoal
      using encode_movl_rr_1_subgoal_6 by blast
    subgoal
      using encode_movl_rr_1_subgoal_6 by blast
    subgoal
      using encode_movl_rr_1_subgoal_4 by blast
    done
  done

lemma encode_movq_rr_1: "
    and 15 (v >> 4) = 4 \<Longrightarrow>
    bit v 3 \<Longrightarrow>
    \<not> bit v (Suc 0) \<Longrightarrow>
    and 3 (k >> 6) = 3 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (k >> 3)) (and 1 (v >> 2))) = Some src \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 k) (and 1 v)) = Some dst \<Longrightarrow>
    v = bitfield_insert_u8 4 4 (bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0)
          (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0)
          (u8_of_bool (and (u8_of_ireg src) 8 \<noteq> 0))) 1) 4 \<and>
    k = bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg dst)) (and 7 (u8_of_ireg src))) 3"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def)
  apply simp
  subgoal by (cases "bit v 0"; cases "bit (v >> 2) 0", simp_all)    
  done

end

