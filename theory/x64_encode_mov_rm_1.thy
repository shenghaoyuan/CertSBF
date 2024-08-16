theory x64_encode_mov_rm_1
imports
  Main
  rBPFCommType rBPFSyntax
  x64Syntax BitsOpMore
begin

lemma [simp]: "and 3 ((v::u8) >> 6) = 1 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit v n \<Longrightarrow> \<not> bit (64::int) n \<Longrightarrow> \<not> bit (7::int) n \<Longrightarrow> bit (56::int) n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              subgoal for n7 apply (cases n7, simp_all)
                subgoal using and_3_shr_6_1_False by blast
                done
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "and 3 ((v::u8) >> 6) = 1 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit v n \<Longrightarrow> \<not> bit (64::int) n \<Longrightarrow> \<not> bit (7::int) n \<Longrightarrow> 3 \<le> n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma [simp]: "and 3 ((v::u8) >> 6) = 1 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit v n \<Longrightarrow> \<not> bit (64::int) n \<Longrightarrow> bit (56::int) n \<Longrightarrow> 3 \<le> n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      done
    done
  done

lemma encode_mov_rm_1_subgoal_1: "and 3 ((v::u8) >> 6) = 1 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit v n \<Longrightarrow> \<not> bit (64::int) n \<Longrightarrow> bit (192::int) n \<Longrightarrow> False"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              subgoal for n7 apply (cases n7, simp_all)
                subgoal using and_3_shr_6_1_False by blast
                done
              done
            done
          done
        done
      done
    done
  done

lemma encode_mov_rm_1_subgoal_2 [simp]: "and 3 ((v::u8) >> 6) = 1 \<Longrightarrow> n < 8 \<Longrightarrow>
  bit (64::int) n \<Longrightarrow> bit v n"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              subgoal
                by (metis Suc3_eq_add_3 bit_0 bit_1_0 bit_and_iff bit_iff_odd_drop_bit
                    numeral_3_eq_3 numeral_Bit0)
              done
            done
          done
        done
      done
    done
  done

lemma encode_mov_rm_1: "
    and 3 (v >> 6) = 1 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (v >> 3)) 0) = Some dst \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 v) 0) = Some src \<Longrightarrow>
    v = bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg src)) (and 7 (u8_of_ireg dst))) 1"
  apply (simp add: u8_of_ireg_of_u8_iff[symmetric])
  apply (unfold bitfield_insert_u8_def u8_of_bool_def Let_def)
  apply simp
  apply (rule bit_eqI)
  subgoal for n
    apply (auto simp add: bit_simps)
    subgoal using encode_mov_rm_1_subgoal_1 by blast
    done
  done

end