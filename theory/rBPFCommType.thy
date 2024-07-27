theory rBPFCommType
imports
  Main
  "Word_Lib.Signed_Words"
begin

type_synonym u4 = "4 word"
type_synonym u8 = "8 word"
type_synonym i8 = "8 sword"
type_synonym i16 = "16 sword"
type_synonym u16 = "16 word"
type_synonym i32 = "32 sword"
type_synonym u32 = "32 word"
type_synonym i64 = "64 sword"
type_synonym u64 = "64 word"
type_synonym i128 = "128 sword"
type_synonym u128 = "128 word"

type_synonym usize = "64 word" \<comment> \<open> Assume the hardware is 64-bit \<close>

definition i32_MIN :: "i32" where
"i32_MIN = 0x80000000"

definition i32_MAX :: "i32" where
"i32_MAX = 0x7FFFFFFF"

definition u32_MAX :: "u32" where
"u32_MAX = 0xFFFFFFFF"

definition i64_MIN :: "i64" where
"i64_MIN = 0x8000000000000000"

definition i64_MAX :: "i64" where
"i64_MAX = 0x7FFFFFFFFFFFFFFF"

definition u64_MAX :: "u64" where
"u64_MAX = 0xFFFFFFFFFFFFFFFF"


record ebpf_binary =
bpf_opc :: u8
bpf_dst :: u4
bpf_src :: u4
bpf_off :: i16
bpf_imm :: i32

type_synonym ebpf_bin = "ebpf_binary list"

abbreviation bit_left_shift ::
  "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" (infix "<<" 50)
where "x << n \<equiv> push_bit n x"

abbreviation bit_right_shift ::
  "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" (infix ">>" 50)
  where "x >> n \<equiv> drop_bit n x"

definition unsigned_bitfield_extract_u8 :: "nat \<Rightarrow> nat \<Rightarrow> u8 \<Rightarrow> u8" where
"unsigned_bitfield_extract_u8 pos width n = and ((2 ^ width) - 1) (n >> pos)"

definition bitfield_insert_u8 :: "nat \<Rightarrow> nat \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> u8" where
"bitfield_insert_u8 pos width n p = (
  let mask = ((2 ^ width) - 1) << pos in
    or ((and ((2 ^ width) - 1) p) << pos)
       (and n (not mask))
)"

(* something is wrong
definition unsigned_bitfield_extract_i8 :: "nat \<Rightarrow> nat \<Rightarrow> i8 \<Rightarrow> i8" where
"unsigned_bitfield_extract_i8 pos width n = and ((2 ^ width) - 1) (n >> pos)" *)

(* Test
value "drop_bit 3 0b10101010::u8"
value "0b10101::u8"

value "and ((2 ^ 4) - 1) 0b10101::u8"

value "unsigned_bitfield_extract_u8 3 4 0b10101010"

This one is wrong
value "(scast (unsigned_bitfield_extract_i8 3 4 0b11101010)) :: i16" *)

definition u8_of_bool :: "bool \<Rightarrow> u8" where
"u8_of_bool b = (
  case b of
    True \<Rightarrow> 1 |
    False \<Rightarrow> 0
)"

definition u4_of_bool :: "bool \<Rightarrow> u4" where
"u4_of_bool b = (
  case b of
    True \<Rightarrow> 1 |
    False \<Rightarrow> 0
)"

definition u8_list_of_u16 :: "u16 \<Rightarrow> u8 list" where
"u8_list_of_u16 i =
  [ (ucast (and i 0xff)),
    (ucast (i >> 8))
  ]"

definition u8_list_of_u32 :: "u32 \<Rightarrow> u8 list" where
"u8_list_of_u32 i =
  [ (ucast (and i 0xff)),
    (ucast (i >> 8)),
    (ucast (i >> 16)),
    (ucast (i >> 24))
  ]"

definition u8_list_of_u64 :: "u64 \<Rightarrow> u8 list" where
"u8_list_of_u64 i =
  [ (ucast (and i 0xff)),
    (ucast (i >> 8)),
    (ucast (i >> 16)),
    (ucast (i >> 24)),
    (ucast (i >> 32)),
    (ucast (i >> 40)),
    (ucast (i >> 48)),
    (ucast (i >> 56))
  ]"

lemma [simp]: "u8_of_bool False = 0" by (unfold u8_of_bool_def, simp)

lemma [simp]: "u8_of_bool True = 1" by (unfold u8_of_bool_def, simp)

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

(*
lemma mod_unique_u8: "\<And>(a::u8) b q r. 0 \<le> a \<Longrightarrow> 0 \<le> r \<Longrightarrow> r < b \<Longrightarrow>
  a = b*q+r \<Longrightarrow> r = a mod b"
  subgoal for a b q r
 *)

(**r
mod_unique:
 forall a b q r, 0<=a -> 0<=r<b ->
  a == b*q + r -> r == a mod b.
Proof.
intros a b q r Ha (Hb,Hr) EQ.
destruct (div_mod_unique b q (a/b) r (a mod b)); auto.
- apply mod_bound_pos; order.
- rewrite <- div_mod; order.
Qed.

*)

(*
lemma mod_add_u8: "\<And>(a::u8) b c. 0 \<le> a \<Longrightarrow> 0 \<le> a+b*c \<Longrightarrow> 0 < c \<Longrightarrow>
  (a + b * c) mod c == a mod c"
  subgoal for a b c
*)

(**r

Lemma mod_add : forall a b c, 0<=a -> 0<=a+b*c -> 0<c ->
 (a + b * c) mod c == a mod c.
Proof.
 intros a b c ? ? ?.
 symmetry.
 apply mod_unique with (a/c+b); auto.
 - apply mod_bound_pos; auto.
 - rewrite mul_add_distr_l, add_shuffle0, <- div_mod by order.
   now rewrite mul_comm.
Qed.

*)

(*
lemma mod_plus_u8: "\<And>(a::u8) b c. (a + b * c) mod c = a mod c"
  subgoal for a b c
    apply (cases "c = 0", simp_all)
*)

(**r 

Lemma Z_mod_plus_full : forall a b c:Z, (a + b * c) mod c = a mod c.
Proof. intros a b c. zero_or_not c.
 - now rewrite Z.mul_0_r, Z.add_0_r.
 - now apply Z.mod_add.
Qed.

*)


(*
lemma mod_unique_u8: "\<And>(x::u8) y a b. x = a * y + b \<Longrightarrow> 0 \<le> b \<Longrightarrow> b < y \<Longrightarrow> x mod y = b"
  subgoal for x y a b
    apply (simp add: add_commute_u8)
*)

(**r 
(a + b * c) mod c = a mod c
Lemma Zmod_unique:
  forall x y a b,
  x = a * y + b -> 0 <= b < y -> x mod y = b.
Proof.
  intros. subst x. rewrite Z.add_comm.
  rewrite Z_mod_plus. apply Z.mod_small. auto. lia.
Qed.

*)

(*
lemma [simp]: "\<And>(n::nat). ((two_p n - 1)::u8) = (((-1)::u8) mod (two_p n))"
  subgoal for n

lemma bits_two_p_m1_u8: "\<And>n i. bit ((2 ^ n - 1)::u8) i = (if i < n then True else False)"

  apply (induct_tac n, simp_all add: bit_simps)
  subgoal for i n
    apply (simp add: bits_mod_two_p_u8)
    subgoal 

      done
*)

(**r
Ztestbit_two_p_m1:
  forall n i, 0 <= n -> 0 <= i ->
  Z.testbit (two_p n - 1) i = if zlt i n then true else false.
Proof.
  intros. replace (two_p n - 1) with ((-1) mod (two_p n)).
  rewrite Ztestbit_mod_two_p; auto. destruct (zlt i n); auto. apply Ztestbit_m1; auto.
  apply Zmod_unique with (-1). ring.
  exploit (two_p_gt_ZERO n). auto. lia.
Qed.

*)

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
        \<comment> \<open> TODO: why Isabell/HOL can not do Nat.add_commute automatically \<close>
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
\<comment> \<open> TODO: We try a stupid way now \<close>
    apply (cases i, simp_all add: bit_1_iff bit_0)
    subgoal for i1 apply (cases i1, simp_all)
       apply (smt (verit) One_nat_def Suc_diff_eq_diff_pred add_diff_cancel_left' bit_and_iff
          bits_zero_ext_u8 diff_diff_cancel le0 leI not_gr_zero odd_bit_iff_bit_pred plus_1_eq_Suc
          semiring_parity_class.even_mask_iff zero_less_diff)

      subgoal for i2 apply (cases i2, simp_all)
        subgoal apply (cases pos, simp_all)
          apply (meson bit_and_iff bits_zero_ext_u8 le0)
          subgoal for pos1
            by (smt (verit, del_insts) Suc_le_eq Suc_lessI add_diff_cancel_left' bit_iff_odd
                bit_imp_le_length diff_is_0_eq' diff_zero even_mask_div_iff leI less_le_not_le) 
          done

        subgoal for i3 apply (cases i3, simp_all)
          subgoal apply (cases pos, simp_all)
            apply (meson bit_iff_odd even_mask_div_iff exp_eq_0_imp_not_bit linorder_not_less)
            subgoal for pos1
              by (smt (verit) Suc_le_eq add_diff_cancel_left' bit_iff_odd bit_imp_le_length
                  diff_is_0_eq' diff_zero even_mask_div_iff exp_eq_zero_iff leI less_Suc_eq
                  less_le_not_le plus_1_eq_Suc zero_less_Suc)
            done

          subgoal for i4 apply (cases i4, simp_all)
            subgoal apply (cases pos, simp_all)
              apply (meson bit_iff_odd even_mask_div_iff exp_eq_0_imp_not_bit linorder_not_less)
              subgoal for pos1
                by (smt (verit) One_nat_def Suc_diff_eq_diff_pred Suc_pred add_diff_cancel_left' 
                    bit_iff_odd bot_nat_0.not_eq_extremum cancel_comm_monoid_add_class.diff_cancel
                    diff_is_0_eq' even_mask_div_iff exp_eq_0_imp_not_bit le_Suc_eq less_SucE
                    less_diff_conv mult.right_neutral not_less_eq one_add_one plus_1_eq_Suc
                    power.simps(2) square_diff_one_factored)
              done

            subgoal for i5 apply (cases i5, simp_all)
              subgoal apply (cases pos, simp_all)
                apply (meson bit_iff_odd even_mask_div_iff exp_eq_0_imp_not_bit linorder_not_less)
                subgoal for pos1
                  by (smt (verit) One_nat_def Suc_diff_eq_diff_pred Suc_pred add_diff_cancel_left' 
                      bit_iff_odd bot_nat_0.not_eq_extremum cancel_comm_monoid_add_class.diff_cancel
                      diff_is_0_eq' even_mask_div_iff exp_eq_0_imp_not_bit le_Suc_eq less_SucE
                      less_diff_conv mult.right_neutral not_less_eq one_add_one plus_1_eq_Suc
                      power.simps(2) square_diff_one_factored)
                done

              subgoal for i6 apply (cases i6, simp_all)
                subgoal apply (cases pos, simp_all)
                   apply (meson bit_iff_odd even_mask_div_iff exp_eq_0_imp_not_bit linorder_not_less)
                  subgoal for pos1
                    by (smt (verit) One_nat_def Suc_diff_eq_diff_pred Suc_pred add_diff_cancel_left' 
                        bit_iff_odd bot_nat_0.not_eq_extremum cancel_comm_monoid_add_class.diff_cancel
                        diff_is_0_eq' even_mask_div_iff exp_eq_0_imp_not_bit le_Suc_eq less_SucE
                        less_diff_conv mult.right_neutral not_less_eq one_add_one plus_1_eq_Suc
                        power.simps(2) square_diff_one_factored)
                  done

                subgoal for i7 apply (cases i7, simp_all)
                  subgoal apply (cases pos, simp_all)
                     apply (meson bit_iff_odd even_mask_div_iff exp_eq_0_imp_not_bit linorder_not_less)
                    subgoal for pos1
                      by (smt (verit) One_nat_def Suc_diff_eq_diff_pred Suc_pred add_diff_cancel_left' 
                          bit_iff_odd bot_nat_0.not_eq_extremum cancel_comm_monoid_add_class.diff_cancel
                          diff_is_0_eq' even_mask_div_iff exp_eq_0_imp_not_bit le_Suc_eq less_SucE
                          less_diff_conv mult.right_neutral not_less_eq one_add_one plus_1_eq_Suc
                          power.simps(2) square_diff_one_factored)
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


(*
    apply (cases "i - pos < width", simp_all)
    subgoal 

*)


(**r

  destruct (zlt i pos).
- unfold proj_sumbool; rewrite zle_false by lia. cbn. apply andb_true_r.
- unfold proj_sumbool; rewrite zle_true by lia; cbn.
  rewrite bits_zero_ext, testbit_repr, Ztestbit_two_p_m1 by lia.
  destruct (zlt (i - pos) width); cbn.
+ rewrite zlt_true by lia. rewrite andb_false_r, orb_false_r. auto.
+ rewrite zlt_false by lia. apply andb_true_r.

*)

end