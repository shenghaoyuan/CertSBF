theory x64DecodeProofAux
imports
  Main
  rBPFCommType
  x64Assembler x64Disassembler BitsOpMore BitsOpMore2 BitsOpMore3 BitsOpMore4
begin

lemma [simp]: "l @ [a] = l_bin \<Longrightarrow> l_bin!(length l) = a" by fastforce
lemma [simp]: "l @ [a, b] = l_bin \<Longrightarrow> l_bin!(length l) = a" by fastforce  
lemma [simp]: "l @ [a, b, c] = l_bin \<Longrightarrow> l_bin!(length l) = a" by fastforce
lemma [simp]: "l @ [a, b, c, d] = l_bin \<Longrightarrow> l_bin!(length l) = a" by fastforce
lemma [simp]: "l @ [a, b, c, d, e] = l_bin \<Longrightarrow> l_bin!(length l) = a" by fastforce

lemma [simp]: "l @ [a, b] = l_bin \<Longrightarrow> l_bin!(length l + 1) = b"
  by (metis One_nat_def nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
lemma [simp]: "l @ [a, b, c] = l_bin \<Longrightarrow> l_bin!(length l + 1) = b"
  by (metis One_nat_def nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
lemma [simp]: "l @ [a, b, c, d] = l_bin \<Longrightarrow> l_bin!(length l + 1) = b"
  by (metis One_nat_def nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
lemma [simp]: "l @ [a, b, c, d, e] = l_bin \<Longrightarrow> l_bin!(length l + 1) = b"
  by (metis One_nat_def nth_Cons_0 nth_Cons_Suc nth_append_length_plus)

lemma [simp]: "l @ [a, b] = l_bin \<Longrightarrow> l_bin!(Suc (length l)) = b"
  by (metis One_nat_def add_diff_cancel_right' not_add_less2 nth_Cons_0 nth_Cons_Suc nth_append plus_1_eq_Suc)
lemma [simp]: "l @ [a, b, c] = l_bin \<Longrightarrow> l_bin!(Suc (length l)) = b"
  by (metis One_nat_def add_diff_cancel_right' not_add_less2 nth_Cons_0 nth_Cons_Suc nth_append plus_1_eq_Suc)
lemma [simp]: "l @ [a, b, c, d] = l_bin \<Longrightarrow> l_bin!(Suc (length l)) = b"
  by (metis One_nat_def add_diff_cancel_right' not_add_less2 nth_Cons_0 nth_Cons_Suc nth_append plus_1_eq_Suc)
lemma [simp]: "l @ [a, b, c, d, e] = l_bin \<Longrightarrow> l_bin!(Suc (length l)) = b"
  by (metis One_nat_def add_diff_cancel_right' not_add_less2 nth_Cons_0 nth_Cons_Suc nth_append plus_1_eq_Suc)

lemma [simp]: "l @ [a, b, c] = l_bin \<Longrightarrow> l_bin!(length l + 2) = c"
  by (metis One_nat_def Suc_1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
lemma [simp]: "l @ [a, b, c, d] = l_bin \<Longrightarrow> l_bin!(length l + 2) = c"
  by (metis One_nat_def Suc_1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
lemma [simp]: "l @ [a, b, c, d, e] = l_bin \<Longrightarrow> l_bin!(length l + 2) = c"
  by (metis One_nat_def Suc_1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus)


lemma [simp]: "l @ [a, b, c] = l_bin \<Longrightarrow> l_bin!(Suc (Suc (length l))) = c"
  by (metis Cons_eq_appendI One_nat_def add_Suc_right append_Nil length_append list.size(3) list.size(4) nth_append_length nth_append_length_plus plus_1_eq_Suc)
lemma [simp]: "l @ [a, b, c, d] = l_bin \<Longrightarrow> l_bin!(Suc (Suc (length l))) = c"
  by (metis Cons_eq_appendI One_nat_def add_Suc_right append_Nil length_append list.size(3) list.size(4) nth_append_length nth_append_length_plus plus_1_eq_Suc)
lemma [simp]: "l @ [a, b, c, d, e] = l_bin \<Longrightarrow> l_bin!(Suc (Suc (length l))) = c"
  by (metis Cons_eq_appendI One_nat_def add_Suc_right append_Nil length_append list.size(3) list.size(4) nth_append_length nth_append_length_plus plus_1_eq_Suc)

lemma [simp]: "l @ [a, b, c, d] = l_bin \<Longrightarrow> l_bin!(length l + 3) = d"
  by force
lemma [simp]: "l @ [a, b, c, d, e] = l_bin \<Longrightarrow> l_bin!(length l + 3) = d"
  by force


lemma [simp]: "l @ [a, b, c, d] = l_bin \<Longrightarrow> l_bin!(Suc (Suc (Suc (length l)))) = d"
  by (metis One_nat_def Suc3_eq_add_3 add_diff_cancel_right' last.simps last_conv_nth length_Cons list.discI list.size(3) not_add_less2 nth_append)
lemma [simp]: "l @ [a, b, c, d, e] = l_bin \<Longrightarrow> l_bin!(Suc (Suc (Suc (length l)))) = d"
  by (metis Suc3_eq_add_3 add.commute nth_Cons_0 nth_Cons_Suc nth_append_length_plus numeral_3_eq_3)

lemma [simp]: "l @ [a, b, c, d, e] = l_bin \<Longrightarrow> l_bin!(length l + 4) = e"
  by force

lemma [simp]: "l @ [a, b, c, d, e] = l_bin \<Longrightarrow> l_bin!(Suc (Suc (Suc (Suc (length l))))) = e"
  by (metis Nil_is_append_conv One_nat_def Suc_1 add_2_eq_Suc' add_Suc_right diff_Suc_1' last.simps last_appendR last_conv_nth length_Cons length_append list.discI list.size(3))

lemma [simp]: "l @ [a] = l_bin \<Longrightarrow> length l_bin - length l = 1" by fastforce
lemma [simp]: "l @ [a, b] = l_bin \<Longrightarrow> length l_bin - length l = 2" by fastforce  
lemma [simp]: "l @ [a, b, c] = l_bin \<Longrightarrow> length l_bin - length l = 3" by fastforce
lemma [simp]: "l @ [a, b, c, d] = l_bin \<Longrightarrow> length l_bin - length l = 4" by fastforce
lemma [simp]: "l @ [a, b, c, d, e] = l_bin \<Longrightarrow> length l_bin - length l = 5" by fastforce


  \<comment> \<open> u16 \<close> 
lemma list_in_list_u8_list_of_u16_simp : "list_in_list (u8_list_of_u16 imm) pc l \<Longrightarrow>
  Some imm = u16_of_u8_list [l ! pc, l ! (pc + 1)]"
  by (simp add: u16_of_u8_list_same u8_list_of_u16_def
      Suc3_eq_add_3 add.commute)

lemma list_in_list_u8_list_of_u16_simp_sym : "list_in_list (u8_list_of_u16 imm) pc l \<Longrightarrow>
  u16_of_u8_list [l ! pc, l ! (pc + 1)] = Some imm"
  using list_in_list_u8_list_of_u16_simp
  by presburger

lemma length_u8_list_of_u16_eq_2 : "length (u8_list_of_u16 imm) = 2"
  by (simp add: u8_list_of_u16_def)

  \<comment> \<open> u32 \<close> 
lemma list_in_list_u8_list_of_u32_simp : "list_in_list (u8_list_of_u32 imm) pc l \<Longrightarrow>
  Some imm = u32_of_u8_list [l ! pc, l ! (pc + 1), l ! (pc + 2), l ! (pc + 3)]"
  by (simp add: u32_of_u8_list_same u8_list_of_u32_def
      Suc3_eq_add_3 add.commute)

lemma list_in_list_u8_list_of_u32_simp_sym : "list_in_list (u8_list_of_u32 imm) pc l \<Longrightarrow>
  u32_of_u8_list [l ! pc, l ! (pc + 1), l ! (pc + 2), l ! (pc + 3)] = Some imm"
  using list_in_list_u8_list_of_u32_simp
  by presburger

lemma length_u8_list_of_u32_eq_4 : "length (u8_list_of_u32 imm) = 4"
  by (simp add: u8_list_of_u32_def)

  \<comment> \<open> u64 \<close> 
lemma list_in_list_u8_list_of_u64_simp : "list_in_list (u8_list_of_u64 imm) pc l \<Longrightarrow>
  Some imm = u64_of_u8_list [l ! pc, l ! (pc + 1), l ! (pc + 2), l ! (pc + 3), l ! (pc + 4), l ! (pc + 5), l ! (pc + 6), l ! (pc + 7)]"
  by (simp add: u64_of_u8_list_same u8_list_of_u64_def
        Suc3_eq_add_3 add.commute)

lemma list_in_list_u8_list_of_u64_simp_sym : "list_in_list (u8_list_of_u64 imm) pc l \<Longrightarrow>
  u64_of_u8_list [l ! pc, l ! (pc + 1), l ! (pc + 2), l ! (pc + 3), l ! (pc + 4), l ! (pc + 5), l ! (pc + 6), l ! (pc + 7)] = Some imm"
  using list_in_list_u8_list_of_u64_simp
  by presburger

lemma length_u8_list_of_u64_eq_8 : "length (u8_list_of_u64 imm) = 8"
  by (simp add: u8_list_of_u64_def)

lemma list_in_list_concat: "list_in_list (l1 @ l2) pc l = (list_in_list l1 pc l \<and> list_in_list l2 (pc + length l1) l)"
(*
l1 = h # t
list_in_list ((h # t) @ l2) pc l                    \<Longrightarrow> (h = l!pc \<and> list_in_list (t @ l2) (pc+1) l) by def of list_in_list
                                                      \<Longrightarrow> list_in_list (t @ l2) (pc+1) l
list_in_list l1 pc l \<Longrightarrow> list_in_list (h # t) pc l  \<Longrightarrow> (h = l!pc \<and> list_in_list t (pc+1) l)
                                                      \<Longrightarrow> list_in_list t (pc+1) l
list_in_list l2 (pc + length l1) l                  \<Longrightarrow> list_in_list l2 (pc + 1+ length t) l 
                                                          \<Longrightarrow> by IH *)
  by (induction l1 arbitrary: l2 pc l, simp_all)

lemma Suc4_eq_add_4: "(Suc (Suc (Suc (Suc pc)))) = pc + 4" by simp

lemma and_7_or_192_simp: "(and 7 (or (and 192 (scale << 6)) v ) ) = and 7 (v::u8)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        done
      done
    done
  done

lemma construct_modsib_to_u8_imply_base_reg_simp: "
  rex = construct_rex_to_u8 True b (and (u8_of_ireg index_reg) 8 \<noteq> 0)
    (and (u8_of_ireg base_reg) 8 \<noteq> 0) \<Longrightarrow>
  v = construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 1 (unsigned_bitfield_extract_u8 0 3 v)
      (unsigned_bitfield_extract_u8 0 1 rex)) = Some base_reg"
  apply (simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
      bitfield_insert_u8_def Let_def)
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp only: and_7_or_192_simp)
  apply (cases b; cases index_reg; cases base_reg; simp)
  done

lemma construct_modsib_to_u8_imply_base_reg: "
  construct_rex_to_u8 True b (and (u8_of_ireg index_reg) 8 \<noteq> 0)
    (and (u8_of_ireg base_reg) 8 \<noteq> 0) = rex \<Longrightarrow>
  construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) = v \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 1 (unsigned_bitfield_extract_u8 0 3 v)
      (unsigned_bitfield_extract_u8 0 1 rex)) = Some base_reg"
  using construct_modsib_to_u8_imply_base_reg_simp by blast

lemma and_7_or_24_simp: "and 7 (or (and 24 ((scale << 6) >> 3)) v) = and 7 (v::u8)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        done
      done
    done
  done

lemma construct_modsib_to_u8_imply_index_reg_simp: "
  rex = construct_rex_to_u8 True b (and (u8_of_ireg index_reg) 8 \<noteq> 0)
    (and (u8_of_ireg base_reg) 8 \<noteq> 0) \<Longrightarrow>
  v = construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 1 (unsigned_bitfield_extract_u8 3 3 v)
      (unsigned_bitfield_extract_u8 1 1 rex)) = Some index_reg"
  apply (simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
      bitfield_insert_u8_def Let_def)
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp only: and_7_or_24_simp)
  apply (cases b; cases index_reg; cases base_reg; simp)
  done

lemma construct_modsib_to_u8_imply_index_reg: "
  construct_rex_to_u8 True b (and (u8_of_ireg index_reg) 8 \<noteq> 0)
    (and (u8_of_ireg base_reg) 8 \<noteq> 0) = rex \<Longrightarrow>
  construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) = v \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 1 (unsigned_bitfield_extract_u8 3 3 v)
      (unsigned_bitfield_extract_u8 1 1 rex)) = Some index_reg"
  using construct_modsib_to_u8_imply_index_reg_simp by blast

lemma word_of_nat_3_eq: "word_of_nat n \<le> (3::u8) \<longleftrightarrow> ((word_of_nat n) ::u8) \<le> word_of_nat 3"
  by simp

lemma u8_le3_eq1: "(scale::u8) \<le> 3 \<Longrightarrow> scale = 0 \<or> scale = 1 \<or> scale = 2 \<or> scale = 3"
  apply (cases scale, simp_all)
  subgoal for n
    apply (simp only: word_of_nat_3_eq)
    apply (simp only: word_of_nat_less_eq_iff)
    apply simp
    apply (simp only: take_bit_eq_mod)
    apply simp
    by (metis Abs_fnat_hom_0 One_nat_def le_neq_implies_less less_2_cases less_Suc_eq
        numeral_2_eq_2 numeral_3_eq_3 of_nat_1 of_nat_numeral)
  done

lemma u8_le3_eq2: "scale = 0 \<or> scale = 1 \<or> scale = 2 \<or> scale = 3 \<Longrightarrow> (scale::u8) \<le> 3"
  apply (erule disjE, simp)
  apply (erule disjE, simp)
  apply (erule disjE, simp)
  apply simp
  done

lemma u8_le3_eq: "(scale::u8) \<le> 3 \<longleftrightarrow> scale = 0 \<or> scale = 1 \<or> scale = 2 \<or> scale = 3"
  using u8_le3_eq1 u8_le3_eq2 by blast


lemma scale_le3_eq_simp: "scale \<le> 3 \<Longrightarrow> and 3 ((scale << 6) >> 6) = (scale::u8)"
  apply (simp only: u8_le3_eq)
  apply (erule disjE, simp)
  apply (erule disjE, simp)
  apply (erule disjE, simp)
  apply simp
  done

lemma scale_le3_eq: "\<not> 3 < scale \<Longrightarrow> and 3 ((scale << 6) >> 6) = (scale::u8)"
  using scale_le3_eq_simp
  using linorder_le_less_linear by blast 

lemma construct_modsib_to_u8_imply_scale_simp: " \<not> 3 < scale \<Longrightarrow>
  v = construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) \<Longrightarrow>
    unsigned_bitfield_extract_u8 6 2 v = scale"
  apply (simp add: construct_modsib_to_u8_def bitfield_insert_u8_def Let_def)
  using scale_le3_eq by blast

lemma construct_modsib_to_u8_imply_scale: " \<not> 3 < scale \<Longrightarrow>
  construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) = v \<Longrightarrow>
    unsigned_bitfield_extract_u8 6 2 v = scale"
  using construct_modsib_to_u8_imply_scale_simp by blast

lemma bit_n_ge: "bit v n \<Longrightarrow> (v::u32) \<ge> 2^n"
  apply (simp only: bit_iff_odd)
  by (metis div_word_less dvd_0_right verit_comp_simplify1(3))

lemma bit_n_plus_ge: "bit v (n+m) \<Longrightarrow> (v::u32) \<ge> 2^n"
  apply (simp only: bit_iff_odd)
  by (metis (no_types, lifting) div_0 div_exp_eq div_word_less even_zero verit_comp_simplify1(3))

lemma bit_n_plus_lt: "(v::u32) < 2^n \<Longrightarrow> bit v (n+m) = False" using bit_n_plus_ge
  using verit_comp_simplify1(3) by blast

lemma bit_n_plus_le: "(v::u32) \<le> 2^n - 1 \<Longrightarrow> bit v (n+m) = False" using bit_n_plus_lt
  by (meson bit_n_plus_ge exp_add_not_zero_imp_left exp_eq_0_imp_not_bit one_neq_zero
      order_trans sub_wrap word_less_1)

lemma Suc7_eq_add_7:"(Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))) = 7+n" by simp

lemma word_not_set_inverse:"(ofs::('a::len) word) \<le> 2^n-1 \<longleftrightarrow> - (2^n) \<le> (not ofs)"
  by (smt (z3) add_diff_cancel_left' add_uminus_conv_diff linorder_not_le minus_diff_commute
      not_eq_complement sub_wrap word_le_minus_mono_left word_less_1 word_sub_le_iff)
 
lemma bit_n_plus_le_7: "(v::u32) \<le> 127 \<Longrightarrow> bit v (7+m) = False"
  using bit_n_plus_le [of v 7 m] by simp

lemma u32_le_127_ge_7_False: "(ofs::u32) \<le> 127 \<Longrightarrow>
    bit ofs (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))) = False"
  apply (simp only: Suc7_eq_add_7)
  using bit_n_plus_le_7 [of ofs n] by simp

lemma len_word:
  "m < LENGTH ('a) \<Longrightarrow> bit (k::'a::len word) m \<longleftrightarrow> \<not>(bit (not k) m)"
  by (simp add: bit_not_iff)
 
lemma bit_n_plus_gt: 
  assumes a0:"m + n < 32" and a1:"-(2^m) \<le> (v::u32)" shows "bit v (m + n) = True"
proof-
  have v0:"m + n < LENGTH(32)" using a0 by auto
  
  have u:"\<forall>v \<le> ((2::u32)^m)-1. bit v (m + n) = False"
    by (simp add: bit_n_plus_le)
  then obtain v' where "bit v' (m + n) = False" and "v'\<le>((2::u32)^m)-1"
    by auto
  then have "not v' \<ge> -((2::u32)^m)" and "bit v' (m + n) = False"
    by (auto simp add: word_not_set_inverse)
  then show ?thesis using len_word[OF v0, of v']
    by (metis a1 bit.double_compl len_word u v0 word_not_set_inverse) 
qed
  
declare [[show_types]]
lemma u32_ge_minus_128_ge_7_True: "n < 25 \<Longrightarrow> -128 \<le> (ofs::u32) \<Longrightarrow>
  bit ofs (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))) = True"
  apply (simp only: Suc7_eq_add_7)
  using bit_n_plus_gt by auto
 
lemma scast_un_aa:
   assumes a0:"LENGTH('a) = m" and a1:"LENGTH('b) = n" and a2:"m \<le> n"
 shows "\<forall>k. k \<le> m - 1 \<longrightarrow> bit ((scast (ofs::('b::len word)))::'a::len word) k = bit ofs k"
  using a0 a1 a2 bit_ucast_iff down_cast_same is_down.rep_eq by fastforce
  

lemma scast_un_bb:
   assumes a0:"LENGTH('a) = m" and a1:"LENGTH('b) = n" and a2:"m \<le> n" and
    a3: "\<forall>k. k \<le> m - 1 \<longrightarrow> bit ((v::'a::len word)) k = bit (ofs::('b::len word)) k" and
    a4:"v\<le>0" and a5:"\<forall>k. k \<ge>  m - 1 \<and> k \<le> n - 1 \<longrightarrow> (bit ofs k)"
  shows "(scast v)  = ofs"
  using a0 a2 a3 a4 a5 bit_last_iff by auto

lemma scast_u32_scast_u8_eq_simp: "ofs \<le> 127 \<or> - 128 \<le> ofs \<Longrightarrow>
  (v::u8) = scast (ofs::u32) \<Longrightarrow> (scast v) = ofs"
  apply simp                   
  apply (simp only: scast_eq)

  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
     apply (metis BitM.simps(1) BitM.simps(2) BitM.simps(3) 
           eval_nat_numeral(3) min_def numeral_3_eq_3 numeral_nat(2) u32_le_127_ge_7_False)
    apply (metis bit_n_plus_le_7 min.absorb2 nat_le_linear 
           ordered_cancel_comm_monoid_diff_class.add_diff_inverse)

  subgoal for n
    apply (drule_tac x="n" in spec)
    apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal for n5 apply (cases n5, simp_all)
              subgoal for n6 apply (cases n6, simp_all add: u32_ge_minus_128_ge_7_True)
                done
              done
            done
          done
        done
      done
    done

  subgoal for n
    apply (drule_tac x="n" in spec)
    apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal for n5 apply (cases n5, simp_all)
              subgoal for n6 apply (cases n6, simp_all add: u32_ge_minus_128_ge_7_True)
                done
              done
            done
          done
        done
      done
    done
done
  
lemma scast_u32_scast_u8_eq: "ofs \<le> 127 \<or> - 128 \<le> ofs \<Longrightarrow>
  scast (ofs::u32) = (v::u8) \<Longrightarrow> (scast v) = ofs"
  using scast_u32_scast_u8_eq_simp by blast

end