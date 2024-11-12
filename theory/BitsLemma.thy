theory BitsLemma
imports
  Main
  rBPFCommType
begin

named_theorems bitfield_simps

lemma bits_zero_ext_u8 [bitfield_simps]: " 0 \<le> i \<Longrightarrow>
  bit (and ((2 ^ n) - 1) (x::u8)) i = (if i < n then bit x i else False)"
  apply (induct_tac n, simp_all add: bit_simps)
  by (smt (verit) bit_1_0 bit_iff_odd bit_imp_le_length
      cancel_comm_monoid_add_class.diff_cancel even_mask_div_iff
      even_mult_exp_div_word_iff less_antisym mult.right_neutral
      not_less one_add_one power.simps(2) square_diff_one_factored)

lemma bits_shl_u8 [bitfield_simps]: "0 \<le> i \<Longrightarrow> i < 8 \<Longrightarrow>
  bit ((x::u8) << y) i = (if i < y then False else bit x (i - y))"
  by (cases "i < y", simp_all add: bit_simps)

lemma bits_mod_two_p_u8 [bitfield_simps]: "0 \<le> n \<Longrightarrow> 0 \<le> i \<Longrightarrow>
  bit ((x::u8) mod (2 ^ n)) i = (if i < n then bit x i else False)"
  apply (induction n arbitrary: x i, simp_all add: bit_simps)
  subgoal for n x i
    apply (cases "i < n", simp_all add: bit_simps)
    subgoal by (metis bit_take_bit_iff less_Suc_eq power_Suc take_bit_eq_mod)
    subgoal
      by (metis bit_take_bit_iff power_Suc take_bit_eq_mod) 
    done
  done

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

lemma bit_2_power_n_ge_False [bitfield_simps]: " i \<ge> n \<Longrightarrow> bit ((2 ^ n - 1)::u8) i = False"
  by (simp add: bit_iff_odd even_mask_div_iff)


lemma bits_two_p_m1_u8 [bitfield_simps]: "n \<le> 8 \<Longrightarrow>
  bit ((2 ^ n - 1)::u8) i = (if i < n then True else False)"
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

lemma bis_bitfield_extract_u8 [bitfield_simps]: "
  0 \<le> pos \<Longrightarrow> 0 < width \<Longrightarrow> pos + width \<le> 8 \<Longrightarrow>
  0 \<le> i \<Longrightarrow> i < 8 \<Longrightarrow> \<comment> \<open> TODO: i \<le> 8 is also OK !!  \<close>
  bit (bitfield_extract_u8 pos width n) i =
  (if i < width then bit n (i + pos) else False)"
  apply (unfold bitfield_extract_u8_def)
  apply (simp only: bits_zero_ext_u8)
  apply (cases "i < width", simp_all add: bit_simps)
  apply (simp add: add.commute)
  done

lemma nat_ge_minus_eq : "\<not> (i::nat) < pos \<Longrightarrow> (i - pos < width) = (i < pos + width)"
  by (simp add: add.commute less_diff_conv2)

lemma bits_bitfield_insert_u8 [bitfield_simps]: "
  0 \<le> pos \<Longrightarrow> 0 < width \<Longrightarrow> pos + width \<le> 8 \<Longrightarrow>
  0 \<le> i \<Longrightarrow> i < 8 \<Longrightarrow>
  bit (bitfield_insert_u8 pos width n p) i =
  (if pos \<le> i \<and> i < (pos + width) then bit p (i - pos) else bit n i)"
  apply (unfold bitfield_insert_u8_def Let_def)
  apply (simp only: bit_or_iff)
  apply (simp only: bit_and_iff)
  apply (simp only: bit_not_iff)
  apply (simp only: bits_shl_u8)
  apply (simp only: bits_zero_ext_u8)
  apply (cases "i < pos"; simp add: bits_two_p_m1_u8 nat_ge_minus_eq)
  done

subsection \<open> So we may be use
- `bits_unsigned_bitfield_extract_u8` and 
- `bits_bitfield_insert_u8`
 to implement ops for u16/u32/u64 \<close>

lemma bitfield_extract_insert_same0 [bitfield_simps]:
  "0 < w0 \<Longrightarrow> p0 + w0 \<le> 8 \<Longrightarrow>
  bitfield_extract_u8 p0 w0 (bitfield_insert_u8 p0 w0 n v) =
  bitfield_extract_u8 0 w0 v"
  apply (simp add: bit_eq_iff)
  apply (rule allI)
  subgoal by (simp add: bitfield_simps)
  done

lemma bitfield_extract_insert_same1 [bitfield_simps]:
  "0 < w0 \<Longrightarrow> 0 < w1 \<Longrightarrow> p0 + w0 \<le> p1 \<Longrightarrow> p1 + w1 \<le> 8 \<Longrightarrow>
  bitfield_extract_u8 p0 w0 (bitfield_insert_u8 p1 w1 n v) =
  bitfield_extract_u8 p0 w0 n"
  apply (simp add: bit_eq_iff)
  apply (rule allI)
  subgoal by (simp add: bitfield_simps)
  done

lemma bitfield_extract_same_0 [bitfield_simps]:
  "0 < w0 \<Longrightarrow> p0 + w0 < 8 \<Longrightarrow>
    bitfield_extract_u8 0 w0 (bitfield_extract_u8 p0 w0 v) =
    bitfield_extract_u8 p0 w0 v"
  apply (simp add: bit_eq_iff)
  apply (rule allI)
  subgoal by (simp add: bitfield_simps)
  done

lemma bitfield_extract_u8_width_1 [bitfield_simps]:
  " bitfield_extract_u8 p0 1 v = 0 \<or>
    bitfield_extract_u8 p0 1 v = 1"
  apply (simp add: bitfield_extract_u8_def)
  by (metis not_mod_2_eq_0_eq_1 one_and_eq)

lemma bitfield_extract_u8_of_bool_same [bitfield_simps]:
  "p0 < 7 \<Longrightarrow>
    u8_of_bool (bitfield_extract_u8 p0 (Suc 0) v \<noteq> 0) =
    bitfield_extract_u8 p0 1 v"
  apply (unfold u8_of_bool_def)
  apply (cases "bitfield_extract_u8 p0 1 v \<noteq> 0"; simp)
  using bitfield_extract_u8_width_1 by fastforce

lemma bitfield_insert_extract_same0 [bitfield_simps]:
  " 0 < w0 \<Longrightarrow> 0 < w1 \<Longrightarrow> w0 + w1 < 8 \<Longrightarrow>
    bitfield_insert_u8 w0 w1
     (bitfield_extract_u8 0 w0 v)
     (bitfield_extract_u8 w0 w1 v) =
    bitfield_extract_u8 0 (w0+w1) v"
  apply (simp add: bit_eq_iff)
  apply (rule allI)
  subgoal for n
    apply (simp add: bitfield_simps)
    by linarith
  done

lemma bitfield_insert_zero_other [bitfield_simps]:
  " 0 < w0 \<Longrightarrow> 0 < w1 \<Longrightarrow> p0 + w0 < 8 \<Longrightarrow> p1 + w1 < 8 \<Longrightarrow> w0 \<le> p1 \<Longrightarrow>
    bitfield_insert_u8 p1 w1
     (bitfield_extract_u8 p0 w0 v)
     0 =
    bitfield_extract_u8 p0 w0 v"
  apply (simp add: bit_eq_iff)
  apply (rule allI)
  subgoal for n
    apply (simp add: bitfield_simps)
    done
  done

end