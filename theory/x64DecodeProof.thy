theory x64DecodeProof
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler BitsOpMore BitsOpMore2 BitsOpMore3
begin

declare if_split_asm [split]

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
  rex = construct_rex_to_u8 True False (and (u8_of_ireg index_reg) 8 \<noteq> 0)
    (and (u8_of_ireg base_reg) 8 \<noteq> 0) \<Longrightarrow>
  v = construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 1 (unsigned_bitfield_extract_u8 0 3 v)
      (unsigned_bitfield_extract_u8 0 1 rex)) = Some base_reg"
  apply (simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
      bitfield_insert_u8_def Let_def)
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp only: and_7_or_192_simp)
  apply (cases index_reg; cases base_reg; simp)
  done

lemma construct_modsib_to_u8_imply_base_reg: "
  construct_rex_to_u8 True False (and (u8_of_ireg index_reg) 8 \<noteq> 0)
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
  rex = construct_rex_to_u8 True False (and (u8_of_ireg index_reg) 8 \<noteq> 0)
    (and (u8_of_ireg base_reg) 8 \<noteq> 0) \<Longrightarrow>
  v = construct_modsib_to_u8 scale (u8_of_ireg index_reg) (u8_of_ireg base_reg) \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 1 (unsigned_bitfield_extract_u8 3 3 v)
      (unsigned_bitfield_extract_u8 1 1 rex)) = Some index_reg"
  apply (simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
      bitfield_insert_u8_def Let_def)
  apply (simp only: u8_of_ireg_of_u8_iff[symmetric])
  apply (simp only: and_7_or_24_simp)
  apply (cases index_reg; cases base_reg; simp)
  done

lemma construct_modsib_to_u8_imply_index_reg: "
  construct_rex_to_u8 True False (and (u8_of_ireg index_reg) 8 \<noteq> 0)
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

lemma bit_n_plus_le_7: "(v::u32) \<le> 127 \<Longrightarrow> bit v (7+m) = False"
  using bit_n_plus_le [of v 7 m] by simp

lemma ofs_ge_n: "(ofs::u32) \<le> 127 \<Longrightarrow>
    bit ofs (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))) = False"
  apply (simp only: Suc7_eq_add_7)
  using bit_n_plus_le_7 [of ofs n] by simp

(*
lemma [simp]: "- (2 * 2 ^ n) \<le> v \<Longrightarrow> - (2 ^ n) \<le> (v::u32) div 2"
  apply (cases "even v")


lemma bit_n_ge: "(v::u32) \<ge> - (2^n) \<Longrightarrow> bit v n"
  apply (simp only: bit_iff_odd)
  apply (induction n arbitrary: v)
  subgoal for v apply simp
    using dvd_minus_iff odd_one word_order.extremum_uniqueI by blast

  subgoal for n v apply simp

value "(-128::u32)"
value "(2^32::u32)" *)

lemma [simp]: "-128 \<le> (ofs::u32) \<Longrightarrow>
  bit ofs (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))) = True" sorry

lemma scast_u32_scast_u8_eq_simp: "ofs \<le> 127 \<or> - 128 \<le> ofs \<Longrightarrow>
  (v::u8) = scast (ofs::u32) \<Longrightarrow> (scast v) = ofs"
  apply simp
  apply (simp only: scast_eq)

  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n
    apply (drule_tac x="n" in spec)
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

  subgoal for n
    apply (drule_tac x="n" in spec)
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

  subgoal for n
    apply (drule_tac x="n" in spec)
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

  subgoal for n
    apply (drule_tac x="n" in spec)
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
  done

lemma scast_u32_scast_u8_eq: "ofs \<le> 127 \<or> - 128 \<le> ofs \<Longrightarrow>
  scast (ofs::u32) = (v::u8) \<Longrightarrow> (scast v) = ofs"
  using scast_u32_scast_u8_eq_simp by blast

lemma x64_encode_decode_consistency:
  "list_in_list l_bin pc l \<Longrightarrow> Some l_bin = x64_encode ins \<Longrightarrow>
    x64_decode pc l = Some (length l_bin, ins)"
  apply (cases ins; simp_all)

  prefer 8
  subgoal for test dst src
    \<comment> \<open> Pcmovl \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases test; simp)
    subgoal by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal
      by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal
      by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal
      by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)

    subgoal by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal
      by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)

    subgoal by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal
      by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)

    subgoal by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal
      by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)

    subgoal by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal
      by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)

    subgoal by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal
      by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)

    subgoal by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal
      by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)

    subgoal by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal
      by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)

    subgoal by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal
      by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)

    subgoal by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    subgoal
      by (cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    done




                         

(*proof done


  subgoal for dst src
  \<comment> \<open> Pmovl_rr \<close> 
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False (and (u8_of_ireg src) 8 \<noteq> 0) False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64"; simp_all add: construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src
  \<comment> \<open> Pmovq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm
  \<comment> \<open> Pmovl_ri  \<close>
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64";
        simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal \<comment> \<open> rex = 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done

    subgoal \<comment> \<open> rex <> 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(pc+3)" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst imm
 \<comment> \<open> Pmovq_ri\<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    using list_in_list_u8_list_of_u64_simp_sym [of imm "(Suc (Suc pc))" l]
    using length_u8_list_of_u64_eq_8
    apply (cases dst; simp_all add: bitfield_insert_u8_def x64_decode_def ireg_of_u8_def Suc3_eq_add_3 add.commute)
    done

      
  subgoal for dst addr chunk
  \<comment> \<open> Pmov_rm \<close>
    apply (cases addr, simp)
    subgoal for base index2 ofs
      apply (cases base; simp)
      subgoal for base_reg
        apply (cases index2; simp add: Let_def)
        subgoal \<comment> \<open> ofs < u8 /\ index2 = None  /\ not rex \<close>
          sorry
(*
          apply (cases chunk; simp)
          apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def
              bitfield_insert_u8_def Let_def)
          using scast_u32_scast_u8_eq
          apply (cases dst; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def)
          done *)

        subgoal \<comment> \<open> ofs < u8 /\ index2 = None  /\ has rex \<close>
          sorry
(*
          using scast_u32_scast_u8_eq
          apply (cases chunk; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
            bitfield_insert_u8_def Let_def)
          subgoal \<comment> \<open> index2 = None  /\ has rex  /\ M32 \<close>
            apply (cases dst; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                  bitfield_insert_u8_def  Suc3_eq_add_3 add.commute)
            done
          subgoal \<comment> \<open> index2 = None  /\ has rex  /\ M64 \<close>
            apply (cases dst; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                  bitfield_insert_u8_def  Suc3_eq_add_3 add.commute)
            done
          done *)

        subgoal \<comment> \<open> ofs > u8 /\ index2 = None  /\ not rex \<close>
          sorry
(*
          apply (cases chunk; simp; erule conjE)
          apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def
              bitfield_insert_u8_def Let_def)

          using list_in_list_u8_list_of_u32_simp_sym [of ofs "(Suc (Suc pc))" l]
          using length_u8_list_of_u32_eq_4

          apply (cases dst; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                    bitfield_insert_u8_def Suc3_eq_add_3 add.commute)
          done *)

        subgoal \<comment> \<open> ofs > u8 /\ index2 = None  /\ has rex \<close>
          sorry
(*
          apply (cases chunk; simp; erule conjE; erule conjE; erule conjE)
          apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def
              bitfield_insert_u8_def Let_def)
          subgoal  \<comment> \<open> M32 \<close>
            using list_in_list_u8_list_of_u32_simp_sym [of ofs "(Suc (Suc (Suc pc)))" l]
            using length_u8_list_of_u32_eq_4
            apply (cases dst; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                    bitfield_insert_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
            done
          subgoal  \<comment> \<open> M64 \<close>
            using list_in_list_u8_list_of_u32_simp_sym [of ofs "(Suc (Suc (Suc pc)))" l]
            using length_u8_list_of_u32_eq_4
            apply (cases dst; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                    bitfield_insert_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
            done*)

        subgoal for index22\<comment> \<open> index2 = Some \<close>
          sorry  (*not done*)
        (*  apply(cases chunk; cases index22;simp_all)
          subgoal for index_reg scale
            apply (erule conjE; erule conjE; erule conjE; erule conjE)
            using list_in_list_u8_list_of_u32_simp_sym [of "ofs" " (Suc (Suc (Suc (Suc pc))))" l]
            using length_u8_list_of_u32_eq_4
            using construct_modsib_to_u8_imply_index_reg [of index_reg base_reg "l ! pc" scale "l ! (Suc (Suc (Suc pc)))"]
            using construct_modsib_to_u8_imply_base_reg [of index_reg base_reg "l ! pc" scale "l ! (Suc (Suc (Suc pc)))"]
            using construct_modsib_to_u8_imply_scale [of scale index_reg base_reg "l !  Suc (Suc (Suc pc))"]
            apply (cases dst;simp)
            subgoal by (cases base_reg; simp; cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
            subgoal by (cases base_reg; simp; cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) *)

            done
          done
        done


  subgoal for dst src chunk
    \<comment> \<open> Pmov_mr \<close> 
    sorry

  subgoal for addr imm chunk
    \<comment> \<open> Pmov_mi \<close> 
    apply(cases chunk, simp_all)
    apply (cases addr, simp)
    subgoal for base index2 ofs
      apply (cases base, simp_all)
      subgoal for base_reg
        apply (cases index2; simp add: Let_def; erule conjE; erule conjE; erule conjE; erule conjE)
        subgoal
          apply (auto simp add: construct_rex_to_u8_def construct_modsib_to_u8_def)
          subgoal
            using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc (Suc (Suc pc))))" l]
            using length_u8_list_of_u32_eq_4 
            using scast_u32_scast_u8_eq
              by (cases base_reg;auto simp add: x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
            subgoal
            using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc (Suc (Suc pc))))" l]
            using length_u8_list_of_u32_eq_4 
            using scast_u32_scast_u8_eq
            by (cases base_reg;auto simp add: x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
          done
        subgoal
          apply (simp add: list_in_list_concat length_u8_list_of_u32_eq_4)
          using list_in_list_u8_list_of_u32_simp_sym [of "ofs" "(Suc (Suc (Suc pc)))" l]
          using list_in_list_u8_list_of_u32_simp_sym [of imm "(7 + pc)" l]
          apply (cases base_reg; simp add: x64_decode_def  construct_rex_to_u8_def bitfield_insert_u8_def 
              Let_def construct_modsib_to_u8_def ireg_of_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
          done
        done
      done
    done

  subgoal for test dst src
    \<comment> \<open> Pcmovl \<close> 
    sorry

  subgoal for test dst src
    \<comment> \<open> Pcmovq  \<close> 
    sorry

  subgoal for dst src
    \<comment> \<open> Pxchgq_rr \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src
    \<comment> \<open> Pmovsq_rr \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal 
    \<comment> \<open> Pcdq \<close>
    apply(unfold Let_def x64_decode_def; simp)
    done

  subgoal 
    \<comment> \<open> Pcqo \<close>
    apply(unfold Let_def x64_decode_def; simp)
    done

  subgoal for dst addr
    \<comment> \<open> Pleaq \<close> 
    sorry

  subgoal for dst
    \<comment> \<open> Pnegl \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst
    \<comment> \<open> Pnegq \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src 
    \<comment> \<open> Paddq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src 
    \<comment> \<open> Paddl_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm 
    \<comment> \<open> Paddl_ri \<close> 
    sorry

  subgoal for addr imm chunk
  \<comment> \<open> Paddq_mi \<close> 
    apply (cases chunk, simp_all)
    apply (cases addr)
    subgoal for base index2 ofs
      apply simp
      apply (cases base, simp_all)
      subgoal for base_reg
        apply (cases index2, simp_all)
        subgoal for index22
          apply (cases index22, simp_all)
          subgoal for index_reg scale
            apply (erule conjE; erule conjE; erule conjE; erule conjE)
            apply (simp add: list_in_list_concat; erule conjE)

            using construct_modsib_to_u8_imply_index_reg [of index_reg base_reg "l ! pc" scale "l ! Suc (Suc (Suc pc))"]
            using construct_modsib_to_u8_imply_base_reg [of index_reg base_reg "l ! pc" scale "l ! Suc (Suc (Suc pc))"]
            using construct_modsib_to_u8_imply_scale [of scale index_reg base_reg "l ! (pc+3)"]
            using list_in_list_u8_list_of_u32_simp_sym [of "ofs" "(pc+4)" l]
            using length_u8_list_of_u32_eq_4
            using list_in_list_u8_list_of_u32_simp_sym [of imm "(pc+8)" l]
(*
            apply (cases base_reg; simp; cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) *)
            apply (cases base_reg; simp)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            done
          done
        done
      done
    done

  subgoal for dst src 
    \<comment> \<open> Psubl_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src 
    \<comment> \<open> Psubq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm 
    \<comment> \<open> Psubl_ri \<close> 
    sorry

  subgoal for dst 
    \<comment> \<open> Pmull_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pmulq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pimull_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pimulq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pdivl_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pdivq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pidivl_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pidivq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src 
    \<comment> \<open> Pandl_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm 
    \<comment> \<open> Pandl_ri \<close> 
    sorry

  subgoal for dst src
    \<comment> \<open> Pandq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src 
    \<comment> \<open> Porl_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm 
    \<comment> \<open> Porl_ri \<close> 
    sorry

  subgoal for dst src
    \<comment> \<open> Porq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src 
    \<comment> \<open> Pxorl_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src
    \<comment> \<open> Pxorq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm 
    \<comment> \<open> Pxorl_ri \<close> 
    sorry
  
  subgoal for dst imm
    \<comment> \<open> Pshll_ri \<close>
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64",
        simp_all)

    subgoal \<comment> \<open> rex = 0x40 \<close>
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          construct_rex_to_u8_def construct_modsib_to_u8_def)
      done

    subgoal  \<comment> \<open> rex <> 0x40 \<close>
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          construct_rex_to_u8_def construct_modsib_to_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst
    \<comment> \<open> Pshlq_ri \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def  Suc3_eq_add_3 add.commute)
    done

  subgoal for dst
  \<comment> \<open> Pshll_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst
  \<comment> \<open> Pshlq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm
    \<comment> \<open> Pshrl_ri \<close>
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64",
        simp_all)

    subgoal \<comment> \<open> rex = 0x40 \<close>
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          construct_rex_to_u8_def construct_modsib_to_u8_def)
      done

    subgoal  \<comment> \<open> rex <> 0x40 \<close>
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          construct_rex_to_u8_def construct_modsib_to_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst
    \<comment> \<open> Pshrq_ri \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def  Suc3_eq_add_3 add.commute)
    done


  subgoal for dst
  \<comment> \<open> Pshrl_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done     

  subgoal for dst
  \<comment> \<open> Pshrq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm
    \<comment> \<open> Psarl_ri \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def  Suc3_eq_add_3 add.commute)
    done

  subgoal for dst
  \<comment> \<open> Psarq_ri \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def  Suc3_eq_add_3 add.commute)
    done

  subgoal for dst
  \<comment> \<open> Psarl_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done  

  subgoal for dst
  \<comment> \<open> Psarq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done  

  subgoal for dst imm
    \<comment> \<open> Prolw_ri \<close>
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64",
        simp_all)

    subgoal \<comment> \<open> rex = 0x40 \<close>
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          construct_rex_to_u8_def construct_modsib_to_u8_def Suc3_eq_add_3 add.commute)
      done

    subgoal  \<comment> \<open> rex <> 0x40 \<close>
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          construct_rex_to_u8_def construct_modsib_to_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst
    \<comment> \<open> Pbswapl \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst
    \<comment> \<open> Pbswapq \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst
    \<comment> \<open> Ppushl_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for imm
    \<comment> \<open> Ppushl_i \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal 
      using list_in_list_u8_list_of_u32_simp_sym [of imm  "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply(auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def Suc3_eq_add_3 add.commute)
    done

  subgoal for dst
    \<comment> \<open> Ppopl_i \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src
    \<comment> \<open> Ptestl_rr \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src
    \<comment> \<open> Ptestq_rr \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm
  \<comment> \<open> Ptestl_ri  \<close>
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64";
        simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal \<comment> \<open> rex = 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done

    subgoal \<comment> \<open> rex <> 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(pc+3)" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst imm
  \<comment> \<open> Ptestq_ri  \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc (Suc pc)))" l]
    using length_u8_list_of_u32_eq_4
    apply (cases dst; simp_all add: bitfield_insert_u8_def x64_decode_def ireg_of_u8_def Suc3_eq_add_3 add.commute)
    done

  subgoal for dst src
    \<comment> \<open> Pcmpl_rr \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src
    \<comment> \<open> Pcmpq_rr \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def;  erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm
  \<comment> \<open> Pcmpl_ri  \<close>
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64";
        simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal \<comment> \<open> rex = 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done

    subgoal \<comment> \<open> rex <> 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(pc+3)" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst imm
  \<comment> \<open> Pcmpq_ri\<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE; erule conjE)
    using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc (Suc pc)))" l]
    using length_u8_list_of_u32_eq_4
    apply (cases dst; simp_all add: bitfield_insert_u8_def x64_decode_def ireg_of_u8_def Suc3_eq_add_3 add.commute)
    done

  subgoal for test imm
    \<comment> \<open> Pjcc \<close>
    subgoal 
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply (cases test; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
            Suc3_eq_add_3 add.commute)
    done

  subgoal for imm
    \<comment> \<open> Pjmp \<close>
    subgoal 
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc pc)" l]
      using length_u8_list_of_u32_eq_4
      apply (auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
            Suc3_eq_add_3 add.commute)
    done

  subgoal for dst 
    \<comment> \<open> Pcall_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for imm 
    \<comment> \<open> Pcall_i \<close> 
    subgoal 
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc pc)" l]
      using length_u8_list_of_u32_eq_4
      apply (auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
            Suc3_eq_add_3 add.commute)
    done

  subgoal 
    \<comment> \<open> Pret \<close>
    apply(unfold Let_def x64_decode_def; simp)
    done

  subgoal 
    \<comment> \<open> Prdtsc \<close>
    apply(unfold Let_def x64_decode_def; simp)
    done

  subgoal 
    \<comment> \<open> Pnop \<close>
    apply(unfold Let_def x64_decode_def; simp)
    done


*)
end