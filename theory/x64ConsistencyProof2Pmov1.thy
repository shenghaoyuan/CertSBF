theory x64ConsistencyProof2Pmov1
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler
begin

lemma and_8_shl_3: "and (8::u8) (rex << 3) = 0 \<or> and (8::u8) (rex << 3) = 8"
  apply (auto simp add: bit_eq_iff bit_simps)
  subgoal for n na
    by (metis bit_numeral_Bit0_Suc_iff bot_nat_0.extremum_strict leI less_Suc_eq not_bit_numeral_Bit0_0 numeral_3_eq_3)
  subgoal for n na apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          apply (cases na, simp_all)
          subgoal for b1 apply (cases b1, simp_all)
            subgoal for b2 apply (cases b2, simp_all)
              subgoal for b3 apply (cases b3, simp_all)
                done
              done
            done
          done
        done
      done
    done
  done

lemma and_64_shl_6: "(and (64::u8) (rex << 6)) = 0 \<or> (and (64::u8) (rex << 6)) = 64"
  apply (auto simp add: bit_eq_iff bit_simps)
  subgoal for n na apply (cases n, simp_all)
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
    
  subgoal for n na apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal for n5 apply (cases n5, simp_all)
              subgoal for n6 apply (cases n6, simp_all)
                apply (cases na, simp_all)
                subgoal for b1 apply (cases b1, simp_all)
                  subgoal for b2 apply (cases b2, simp_all)
                    subgoal for b3 apply (cases b3, simp_all)
                      subgoal for b4 apply (cases b4, simp_all)
                        subgoal for b5 apply (cases b5, simp_all)
                          subgoal for b6 apply (cases b6, simp_all)
                            done
                          done
                        done
                      done
                    done
                  done
                done
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow> bit (192::int) n \<Longrightarrow> bit rop n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              subgoal apply (drule_tac x="0" in spec)
                apply (simp add: numeral_eq_Suc)
                done
              subgoal apply (drule_tac x="1" in spec)
                apply (simp add: numeral_eq_Suc)
                done
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow> bit rop n \<Longrightarrow>
  \<not> bit (192::int) n \<Longrightarrow> \<not> bit (7::int) n \<Longrightarrow> bit (56::int) n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
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

lemma [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow> bit rop n \<Longrightarrow>
  \<not> bit (192::int) n \<Longrightarrow> \<not> bit (7::int) n \<Longrightarrow> 3 \<le> n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma mov_subgoal1 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow>
    n < 8 \<Longrightarrow> bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow>
    \<not> bit (7::int) n \<Longrightarrow> bit (71::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
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

lemma mov_subgoal2 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow>
    n < 8 \<Longrightarrow> bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow>
    \<not> bit (56::int) n \<Longrightarrow> bit (8::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        done
      done
    done
  done

lemma  [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow> bit rop n \<Longrightarrow>
  \<not> bit (192::int) n \<Longrightarrow> bit (8::int) n \<Longrightarrow> 3 \<le> n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma mov_subgoal3 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow>
    bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow>
    \<not> 3 \<le> n \<Longrightarrow> bit (8::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma mov_subgoal4 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow>
    bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow>
    \<not> 3 \<le> n \<Longrightarrow> bit (56::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma mov_subgoal5 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow>
    n < 8 \<Longrightarrow> bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow>
    bit (8::int) n \<Longrightarrow> bit (71::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        done
      done
    done
  done

lemma [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow>
    n < 8 \<Longrightarrow> bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow>
    bit (56::int) n \<Longrightarrow> bit rop (3 + (n - 3))"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3
        by (metis Suc3_eq_add_3) 
      done
    done
  done

lemma mov_subgoal6 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow>
    n < 8 \<Longrightarrow> bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow>
    bit (56::int) n \<Longrightarrow> bit (71::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
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

lemma mov_subgoal1_1: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow>
    or 192
     (and (or (and 56 (and (and 56 ((rop >> 3) << 3)) (- 72)))
            (and (and 7 (and (and 7 rop) (- 9))) (- 57)))
       (- 193)) =
    rop"
  apply (rule bit_eqI)
  subgoal for n apply (simp add: bit_or_iff)
    apply (auto simp add: bit_simps)
    subgoal using mov_subgoal1 by blast
    subgoal using mov_subgoal2 by blast
    subgoal using mov_subgoal3 by blast
    subgoal using mov_subgoal4 by blast
    subgoal using mov_subgoal5 by blast
    subgoal using mov_subgoal6 by blast
    done
  done

lemma mov_subgoal7: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit (56::int) n \<Longrightarrow> bit (64::int) n \<Longrightarrow> bit rop n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
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

lemma mov_subgoal8 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
    bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (7::int) n \<Longrightarrow>
    \<not> bit (64::int) n \<Longrightarrow> bit (71::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma mov_subgoal9 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (56::int) n \<Longrightarrow> bit (8::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        done
      done
    done
  done

lemma [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (64::int) n \<Longrightarrow>
  bit (8::int) n \<Longrightarrow> bit (56::int) n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        done
      done
    done
  done

lemma mov_subgoal10 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (64::int) n \<Longrightarrow>
  bit (8::int) n \<Longrightarrow> bit (71::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (64::int) n \<Longrightarrow> bit (56::int) n \<Longrightarrow> 3 \<le> n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma mov_subgoal11 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (64::int) n \<Longrightarrow> bit (56::int) n \<Longrightarrow>
  bit (71::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma mov_subgoal1_2: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow>
    or 192
     (and (or (and 56 (or 64 (and (and 56 ((rop >> 3) << 3)) (- 72))))
            (and (and 7 (and (and 7 rop) (- 9))) (- 57)))
       (- 193)) =
    rop"
  apply (rule bit_eqI)
  subgoal for n
    apply (simp add: bit_or_iff)
    apply (auto simp add: bit_simps)
    subgoal using mov_subgoal7 by blast
    subgoal using mov_subgoal8 by blast
    subgoal using mov_subgoal9 by blast
    subgoal using mov_subgoal10 by blast
    subgoal using mov_subgoal11 by blast
    done
  done

lemma [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit (7::int) n \<Longrightarrow> bit (8::int) n \<Longrightarrow> bit rop n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1
    apply (cases n1, simp_all)
    subgoal for n2
      apply (cases n2, simp_all)
      done
    done
  done

lemma mov_subgoal12 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (7::int) n \<Longrightarrow> bit (71::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1
    apply (cases n1, simp_all)
    subgoal for n2
      apply (cases n2, simp_all)
      subgoal for n3
        apply (cases n3, simp_all)
        subgoal for n4
          apply (cases n4, simp_all)
          subgoal for n5
            apply (cases n5, simp_all)
            subgoal for n6
              apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma mov_subgoal13 : "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (8::int) n \<Longrightarrow> \<not> bit (56::int) n \<Longrightarrow> bit (7::int) n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1
    apply (cases n1, simp_all)
    subgoal for n2
      apply (cases n2, simp_all)
      subgoal for n3
        apply (cases n3, simp_all)
        subgoal for n4
          apply (cases n4, simp_all)
          subgoal for n5
            apply (cases n5, simp_all)
            subgoal for n6
              apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma mov_subgoal14 : "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (8::int) n \<Longrightarrow>
  \<not> 3 \<le> n \<Longrightarrow> bit (7::int) n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma mov_subgoal15 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (8::int) n \<Longrightarrow>
  \<not> bit (7::int) n \<Longrightarrow> bit (71::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1
    apply (cases n1, simp_all)
    subgoal for n2
      apply (cases n2, simp_all)
      subgoal for n3
        apply (cases n3, simp_all)
        subgoal for n4
          apply (cases n4, simp_all)
          subgoal for n5
            apply (cases n5, simp_all)
            subgoal for n6
              apply (cases n6, simp_all)
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> bit (56::int) n \<Longrightarrow> 3 \<le> n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma mov_subgoal16 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> bit (56::int) n \<Longrightarrow>
  bit (71::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
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

lemma mov_subgoal1_3: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow>
   or 192
     (and (or (and 56 (and (and 56 ((rop >> 3) << 3)) (- 72)))
            (and (and 7 (or 8 (and (and 7 rop) (- 9)))) (- 57)))
       (- 193)) =
    rop"
  apply (rule bit_eqI)
  subgoal for n apply (simp add: bit_or_iff)
    apply (auto simp add: bit_simps)
    subgoal using mov_subgoal12 by blast
    subgoal using mov_subgoal13 by blast
    subgoal using mov_subgoal14 by blast
    subgoal using mov_subgoal15 by blast
    subgoal using mov_subgoal16 by blast
    done
  done

lemma mov_subgoal17: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit (56::int) n \<Longrightarrow> bit (64::int) n \<Longrightarrow> bit rop n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
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

lemma mov_subgoal18 [simp]: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (7::int) n \<Longrightarrow>
  \<not> bit (64::int) n \<Longrightarrow> bit (71::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma mov_subgoal19 : "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (8::int) n \<Longrightarrow>
  \<not> bit (56::int) n \<Longrightarrow> bit (7::int) n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
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

lemma mov_subgoal20 : "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (64::int) n \<Longrightarrow>
  \<not> bit (8::int) n \<Longrightarrow> \<not> bit (56::int) n \<Longrightarrow> bit (7::int) n"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
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

lemma mov_subgoal21 : "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (8::int) n \<Longrightarrow>
  \<not> bit (64::int) n \<Longrightarrow> \<not> bit (7::int) n \<Longrightarrow> bit (71::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma mov_subgoal22 : "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit rop n \<Longrightarrow> \<not> bit (192::int) n \<Longrightarrow> \<not> bit (64::int) n \<Longrightarrow>
  bit (56::int) n \<Longrightarrow> bit (71::int) n \<Longrightarrow> False"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma mov_subgoal1_4: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow>
  or 192
     (and (or (and 56 (or 64 (and (and 56 ((rop >> 3) << 3)) (- 72))))
            (and (and 7 (or 8 (and (and 7 rop) (- 9)))) (- 57)))
       (- 193)) =
    rop"
  apply (rule bit_eqI)
  subgoal for n
    apply (simp add: bit_or_iff)
    apply (auto simp add: bit_simps)
    subgoal using mov_subgoal17 by blast
    subgoal using mov_subgoal18 by blast
    subgoal using mov_subgoal19 by blast
    subgoal using mov_subgoal20 by blast
    subgoal using mov_subgoal21 by blast
    subgoal using mov_subgoal22 by blast
    done
  done

lemma mov_goal_1: "and 3 ((rop::u8) >> 6) = 3 \<Longrightarrow>
     construct_modsib_to_u8 3
     (bitfield_insert_u8 3 (Suc 0) (and 7 (rop >> 3)) (and 1 (rex >> 2)))
     (bitfield_insert_u8 3 (Suc 0) (and 7 rop) (and 1 rex)) =
    rop"
  apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def bitfield_insert_u8_def)
  apply simp
  apply (insert and_8_shl_3 [of rex])
  apply (erule disjE, simp_all)
  subgoal
    apply (insert and_64_shl_6 [of "rex >> 2"])
    apply (erule disjE, simp_all)
    subgoal using mov_subgoal1_1 by blast
    subgoal using mov_subgoal1_2 by blast
    done
  subgoal
    apply (insert and_64_shl_6 [of "rex >> 2"])
    apply (erule disjE, simp_all)
    subgoal using mov_subgoal1_3 by blast
    subgoal using mov_subgoal1_4 by blast
    done
  done

end