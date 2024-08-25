theory x64DecodeProof
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler BitsOpMore2 BitsOpMore3
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

lemma x64_encode_decode_consistency:
  "list_in_list l_bin pc l \<Longrightarrow> Some l_bin = x64_encode ins \<Longrightarrow>
    x64_decode pc l = Some (length l_bin, ins)"
  apply (cases ins; simp_all)
                      prefer 4
  subgoal for dst imm
 \<comment> \<open> Pmovq_ri\<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    using list_in_list_u8_list_of_u64_simp_sym [of imm "(Suc (Suc pc))" l]
    using length_u8_list_of_u64_eq_8
    apply (cases dst; simp_all add: bitfield_insert_u8_def x64_decode_def ireg_of_u8_def Suc3_eq_add_3 add.commute)
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
      
  subgoal for dst src chunk
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

  subgoal for dst src chunk
    \<comment> \<open> Pmov_mr \<close> 
    sorry

  subgoal for dst imm chunk
    \<comment> \<open> Pmov_mi \<close> 
    sorry

  subgoal for dst src chunk
    \<comment> \<open> Pcmovl \<close> 
    sorry

  subgoal for dst chunk
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
*)
end