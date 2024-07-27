theory BitsLemma
imports
  Main
  rBPFCommType
begin

lemma add_commute_nat: "a + b = b + (a::nat)" by simp

lemma add_commute_u8: "a + b = b + (a::u8)" by simp

lemma and_truel: "(a \<and> b = b) = (a = True)" by simp

lemma bits_zero_ext_u8 [simp]: "\<And>n x i. 0 \<le> i \<Longrightarrow>
  bit (and ((2 ^ n) - 1) (x::u8)) i = (if i < n then bit x i else False)"
  apply (induct_tac n, simp_all add: bit_simps)
  by (smt (verit) bit_1_0 bit_iff_odd bit_imp_le_length
      cancel_comm_monoid_add_class.diff_cancel even_mask_div_iff
      even_mult_exp_div_word_iff less_antisym mult.right_neutral
      not_less one_add_one power.simps(2) square_diff_one_factored)

lemma bits_shl_u8 [simp]: "\<And>(x::u8) y i. 0 \<le> i \<Longrightarrow> i < 8 \<Longrightarrow>
  bit (x << y) i = (if i < y then False else bit x (i - y))"
  subgoal for x y i by (cases "i < y", simp_all add: bit_simps)
  done

lemma bits_mod_two_p_u8 [simp]: "0 \<le> n \<Longrightarrow> 0 \<le> i \<Longrightarrow>
  bit ((x::u8) mod (2 ^ n)) i = (if i < n then bit x i else False)"
  apply (induction n arbitrary: x i, simp_all add: bit_simps)
  subgoal for n x i
    apply (cases "i < n", simp_all add: bit_simps)
    subgoal by (metis bit_take_bit_iff less_Suc_eq power_Suc take_bit_eq_mod)
    subgoal
      by (metis bit_take_bit_iff power_Suc take_bit_eq_mod) 
    done
  done

lemma [simp]:"\<And>(a::u8) b c. a + (b + c) = (a + c) + b"
  by simp

lemma eq_neq_false [simp]: "(a = b) \<Longrightarrow> a \<noteq> b \<Longrightarrow> False" by blast


lemma eq_false_neq_u8 [simp]: "(a < b \<or> b < a) \<Longrightarrow> ((a::u8) \<noteq> b)"
  by force

(* This lemma is wrong for u8 because there is a `mod 256` for any u8 integer
lemma mod_unique_u8: "\<And>(a::u8) b q r. r < b \<Longrightarrow>
  a = b*q+r \<Longrightarrow> r = a mod b"
  subgoal for a b q r
    apply simp
    apply (simp add: minus_mult_div_eq_mod[symmetric])
    value "((10::u8) * 30 + 1) mod 10"
    value "(10::u8) * 30" 
    value "10 * (((10::u8) * 30 + 1) div 10)"
*)

lemma bits_two_p_m1_u8 [simp]: "n \<le> 8 \<Longrightarrow> bit ((2 ^ n - 1)::u8) i = (if i < n then True else False)"
  apply (cases n, simp_all add: bit_simps)
  subgoal for n1 apply (cases n1, simp_all add: bit_simps)
    subgoal for n2 apply (cases n2, simp_all add: bit_simps)
      subgoal by (cases i, simp_all add: bit_simps)

      subgoal for n3 apply (cases n3, simp_all add: bit_simps)
        subgoal apply (cases i, simp_all add: bit_simps)
          subgoal for i1 by (cases i1, simp_all add: bit_simps)
          done

        subgoal for n4 apply (cases n4, simp_all add: bit_simps)
          subgoal apply (cases i, simp_all add: bit_simps)
            subgoal for i1 apply (cases i1, simp_all add: bit_simps)
              subgoal for i2 by (cases i2, simp_all add: bit_simps)
              done
            done

          subgoal for n5 apply (cases n5, simp_all add: bit_simps)
            subgoal apply (cases i, simp_all add: bit_simps)
              subgoal for i1 apply (cases i1, simp_all add: bit_simps)
                subgoal for i2 apply (cases i2, simp_all add: bit_simps)
                  subgoal for i3 by (cases i3, simp_all add: bit_simps)
                  done
                done
              done

            subgoal for n6 apply (cases n6, simp_all add: bit_simps)
              subgoal apply (cases i, simp_all add: bit_simps)
                subgoal for i1 apply (cases i1, simp_all add: bit_simps)
                  subgoal for i2 apply (cases i2, simp_all add: bit_simps)
                    subgoal for i3 apply (cases i3, simp_all add: bit_simps)
                      subgoal for i4 by (cases i4, simp_all add: bit_simps)
                      done
                    done
                  done
                done
  
              subgoal for n7 apply (cases n7, simp_all add: bit_simps)
                subgoal apply (cases i, simp_all add: bit_simps)
                  subgoal for i1 apply (cases i1, simp_all add: bit_simps)
                    subgoal for i2 apply (cases i2, simp_all add: bit_simps)
                      subgoal for i3 apply (cases i3, simp_all add: bit_simps)
                        subgoal for i4 apply (cases i4, simp_all add: bit_simps)
                          subgoal for i5 by (cases i5, simp_all add: bit_simps)
                          done
                        done
                      done
                    done
                  done

                subgoal apply (cases i, simp_all add: bit_simps)
                  subgoal for i1 apply (cases i1, simp_all add: bit_simps)
                    subgoal for i2 apply (cases i2, simp_all add: bit_simps)
                      subgoal for i3 apply (cases i3, simp_all add: bit_simps)
                        subgoal for i4 apply (cases i4, simp_all add: bit_simps)
                          subgoal for i5 apply (cases i5, simp_all add: bit_simps)
                            subgoal for i6 by (cases i6, simp_all add: bit_simps)
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

lemma bits_unsigned_bitfield_extract_u8: "\<And>pos width n i.
  0 \<le> pos \<Longrightarrow> 0 < width \<Longrightarrow> pos + width \<le> 8 \<Longrightarrow>
  0 \<le> i \<Longrightarrow> i < 8 \<Longrightarrow> \<comment> \<open> TODO: i \<le> 8 is also OK !!  \<close>
  bit (unsigned_bitfield_extract_u8 pos width n) i =
  (if i < width then bit n (i + pos) else False)"
  subgoal for pos width n i
    apply (unfold unsigned_bitfield_extract_u8_def)
    apply (simp only: bits_zero_ext_u8)
    apply (cases "i < width", simp_all add: bit_simps)
    apply (simp add: add_commute_nat)
    done
  done

lemma [simp]: "\<not> (i::nat) < pos \<Longrightarrow> (i - pos < width) = (i < pos + width)"
  by (simp add: add_commute_nat less_diff_conv2)

lemma bits_bitfield_insert_u8: "\<And>pos width n p i.
  0 \<le> pos \<Longrightarrow> 0 < width \<Longrightarrow> pos + width \<le> 8 \<Longrightarrow>
  0 \<le> i \<Longrightarrow> i < 8 \<Longrightarrow>
  bit (bitfield_insert_u8 pos width n p) i =
  (if pos \<le> i \<and> i < (pos + width) then bit p (i - pos) else bit n i)"
  subgoal for pos width n p i
    apply (unfold bitfield_insert_u8_def Let_def)
    apply (simp only: bit_or_iff)
    apply (simp only: bit_and_iff)
    apply (simp only: bit_not_iff)
    apply (simp only: bits_shl_u8)
    apply (simp only: bits_zero_ext_u8)
    apply (cases "i < pos", simp_all)
    done
  done

subsection \<open> So we may be use
- `bits_unsigned_bitfield_extract_u8` and 
- `bits_bitfield_insert_u8`
 to implement ops for u16/u32/u64 \<close>

end