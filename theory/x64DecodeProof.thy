theory x64DecodeProof
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler BitsOpMore2
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

lemma [simp]: "length l1 = 8 \<Longrightarrow> list_in_list l1 pc l \<Longrightarrow>
[l ! pc, l ! (pc + 1), l ! (pc + 2), l ! (pc + 3), l ! (pc + 4), l ! (pc + 5), 
  l ! (pc + 6), l ! (pc + 7)] = l1"
  apply (cases "l1", simp)
  subgoal for a1 l1 apply (cases "l1", simp)
  subgoal for a2 l2 apply (cases "l2", simp)
  subgoal for a3 l3 apply (cases "l3", simp)
  subgoal for a4 l4 apply (cases "l4", simp)
  subgoal for a5 l5 apply (cases "l5", simp)
  subgoal for a6 l6 apply (cases "l6", simp)
  subgoal for a7 l7 apply (cases "l7", simp)
  subgoal for a8 l8 apply (cases "l8", simp)
    apply (simp add: eval_nat_numeral(3) numeral_Bit0)
  subgoal for a9 l9 apply (cases "l9", simp)
    subgoal for a10 l10 apply (cases "l10", simp) 
      sorry

lemma x64_encode_decode_consistency:
  "list_in_list l_bin pc l \<Longrightarrow> Some l_bin = x64_encode ins \<Longrightarrow> x64_decode pc l = Some (length l_bin, ins)"
  apply (cases ins; simp_all)

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
  \<comment> \<open> Pmovl_ri  
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 0"; simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE )
    subgoal 
      apply (cases dst;cases imm; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def )\<close>
    sorry

  subgoal for dst imm
 \<comment> \<open> Pmovq_ri
    apply (cases dst; simp add: construct_rex_to_u8_def bitfield_insert_u8_def x64_decode_def Let_def ireg_of_u8_def)

    apply (cases "l ! pc = 144", simp)
    subgoal by (cases dst; simp)

    apply (simp add: x64_decode_def Let_def construct_rex_to_u8_def bitfield_insert_u8_def construct_modsib_to_u8_def)
    apply (cases "construct_rex_to_u8 True False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 0"; simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE )
    subgoal 
    subgoal 
      apply (unfold x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def u8_list_of_u64_def )\<close>
    sorry
      
  subgoal for src dst chunk
  \<comment> \<open> Pmov_rm 
    apply (cases dst, simp)
    subgoal for rd rs ro
      apply (cases rd, simp_all)
      subgoal for rd1
        apply (cases rs, simp_all)
        apply (cases "rd1 = ireg.R11 \<and> ro = 0", simp_all add: Let_def)
        apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
        apply (cases chunk; cases src; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)\<close> 
    sorry

  subgoal for src dst chunk
    \<comment> \<open> Pmov_mr \<close> 
    sorry

  subgoal for src dst chunk
    \<comment> \<open> Pmov_mi \<close> 
    sorry

  subgoal for src dst
    \<comment> \<open> Pxchg_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for src dst
    \<comment> \<open> Pmovsq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst
    \<comment> \<open> Pnegl_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

 \<comment> \<open> 
    apply (cases src)
    subgoal
      apply (cases dst)
      subgoal
        apply (auto simp add: bitfield_insert_u8_def Let_def u8_of_bool_def)
        apply (unfold x64_decode_def Let_def)
        apply simp
        value "unsigned_bitfield_extract_u8 4 4 (8)"

        apply (auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)

    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
 \<close> 
  done
end