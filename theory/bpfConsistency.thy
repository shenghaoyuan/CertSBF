theory bpfConsistency
  imports bpfConsistencyAux
begin
(*datatype bpf_state =
  BPF_OK u64 reg_map mem stack_state SBPFV func_map u64 u64 | (**r normal state *)
  BPF_Success u64 |
  BPF_EFlag | (**r find bugs at runtime *)
  BPF_Err  (**r bad thing *)*)

(*datatype outcome = Next regset mem | Stuck*)



(*JIT_OK JitCompiler reg_map SBPFV *)
(*definition is_refined_state :: "bpf_state \<Rightarrow> jit_state \<Rightarrow> bool" where
"is_refined_state bst xst = (case bst of BPF_OK pc rs m ss sv fm cur_cu remain_cu \<Rightarrow>
                                case xst of JIT_OK jcomp res s_v \<Rightarrow> (\<forall> r. Vlong (rs r) = res (IR (bpf_to_x64_reg r))) | _ \<Rightarrow> False |
                                BPF_Success ret \<Rightarrow> case xst of JIT_Success \<Rightarrow> True | _ \<Rightarrow> False |
                            _ \<Rightarrow> False)"
lemma consistency_proof_aux:
  assumes a0:"is_refined_state bst xst" and
    a1:"bst' = bpf_interp fuel prog bst enable_stack_frame_gaps program_vm_addr " and
    a2:"xst' = jit_compile fuel prog xst" and 
    a3:"bpf_find_prog 3 0 prog = Some [BPF_ALU64 BPF_ADD BR1 (SOReg BR2), BPF_EXIT]"
  shows "is_refined_state bst' xst'"
  sorry
*)

(*definition is_refined_state2 :: "bpf_state \<Rightarrow> outcome \<Rightarrow> bool" where
"is_refined_state2 bst xst = (case bst of BPF_OK pc rs m ss sv fm cur_cu remain_cu \<Rightarrow>
                                case xst of Next reg mem \<Rightarrow> (\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))) \<and> m = mem | _ \<Rightarrow> False |
                             BPF_EFlag \<Rightarrow> case xst of Next reg mem \<Rightarrow> False | _ \<Rightarrow> True |
                             BPF_Success ret \<Rightarrow> case xst of Next reg mem \<Rightarrow> reg (IR x64Syntax.RAX) = Vlong ret | 
                                                            _ \<Rightarrow> False |
                             _ \<Rightarrow> False)"

lemma consistency_proof_aux2:
  assumes a0:"is_refined_state2 bst xst" and
    a1:"bins = [BPF_ALU64 BPF_ADD BR1 (SOReg BR2), BPF_EXIT] " and
    a2:"per_jit_insns bins res sv = Some bl" and
    a3:"list_in_list bl (unat pc) l_bin" and
    a4:"x64_decodes (unat pc) l_bin = Some v" and
    a5:"xst' = interp3 xins xst" and
    a6:"bst' = bpf_interp fuel prog bst enable_stack_frame_gaps program_vm_addr" and
    a7:"xins = map snd v" and
    a8:"bpf_find_prog fuel 0 prog = Some bins"
  shows "is_refined_state2 bst' xst'"
  sorry
*)


definition is_refined_state2 :: "bpf_state \<Rightarrow> bin_state \<Rightarrow> bool" where
"is_refined_state2 bst xst = (case bst of BPF_OK pc rs m ss sv fm cur_cu remain_cu \<Rightarrow>
                                case xst of Bin_OK pc2 reg mem \<Rightarrow> (\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))) | _ \<Rightarrow> False |
                             BPF_EFlag \<Rightarrow> case xst of Bin_OK pc2 reg mem \<Rightarrow> False | _ \<Rightarrow> True |
                             BPF_Success ret \<Rightarrow> True |
                             _ \<Rightarrow> False)"
  

lemma addq_subgoal_rr_aux1:
  assumes a0:"bins = BPF_ALU64 BPF_ADD dst (SOReg src)" and
     a1:"xins = (Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))" and
     a2:"(BPF_OK pc rs' m ss' is_v1 fm (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu" and
     a3:"Next reg' m = exec_instr xins sz reg m" and
     a4:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))"
   shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
proof -
    have b1:"Vlong (rs dst) = reg (IR (bpf_to_x64_reg dst))" using a4 spec by simp
    moreover have b2:"Vlong (rs src) = reg (IR (bpf_to_x64_reg src))" using a4 spec by simp
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using aluq_subgoal_rr_aux1 a0 a1 a2 a3 b1 b2 by force
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using aluq_subgoal_rr_aux2 a3 a1 by blast
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 aluq_subgoal_rr_aux3 a2 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a4 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed


lemma addq_subgoal_rr_aux2:"bst2 = step 0 (BPF_ALU64 BPF_ADD dst (SOReg src)) rs m ss sv fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu 
    \<Longrightarrow> \<exists> rs2. BPF_OK 1 rs2 m ss sv fm (cur_cu+1) remain_cu = bst2"
  apply(cases "(BPF_ALU64 BPF_ADD dst (SOReg src))",simp_all)
  apply(unfold eval_alu64_def eval_alu64_aux1_def,simp_all)
  done

lemma addq_subgoal_rr_aux3:"\<exists> reg2. exec_instr (Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)) 1 reg mem = Next reg2 mem"
  apply(unfold exec_instr_def)
  apply(cases "Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)",simp_all)
  done

(*lemma "bpf_find_prog fuel 0 prog = Some [bins] \<Longrightarrow> bins = BPF_ALU64 BPF_ADD dst (SOReg src) \<Longrightarrow> fuel > 8 \<Longrightarrow> length (bpf_find_prog_aux fuel (0::nat) prog) \<noteq> Suc (0::nat) \<Longrightarrow>
bpf_find_prog_aux fuel (0::nat) prog = [Some bins, None]"
  apply(cases bins,simp_all)
  apply(unfold bpf_find_prog_def Let_def,simp_all)
  subgoal for x91 apply(split if_splits, simp_all)
  
lemma 
  assumes a0:"bpf_find_prog fuel 0 prog = Some [bins]" and 
    a1:"bins = BPF_ALU64 BPF_ADD dst (SOReg src)" and 
    a2:"fuel > 8" 
  shows" bpf_find_instr 0 prog = Some bins"
proof-
  have "bpf_find_prog_aux fuel (0::nat) prog = [Some bins, None]" using a0
qed

lemma "bpf_find_prog fuel 0 prog = Some [bins] \<Longrightarrow> bins = BPF_ALU64 BPF_ADD dst (SOReg src) \<Longrightarrow> fuel > 8 \<Longrightarrow> bpf_find_instr 0 prog = Some bins"
  apply(cases bins,simp_all)
  apply(unfold bpf_find_prog_def Let_def,simp_all)
  apply(split if_splits, simp_all)
*)


lemma addq_subgoal_rr_aux4:"bpf_find_instr 0 prog = Some bins \<Longrightarrow> prog = [0x95::u8,0x00,0x00,0x00,0x00,0x00,0x00,0x00]
  \<Longrightarrow> bins = BPF_EXIT"
  apply(cases bins,simp_all)
  apply(unfold bpf_find_instr_def rbpf_decoder_def u16_of_u8_list_def u32_of_u8_list_def u4_to_bpf_ireg_def,simp_all)
  done

lemma addq_subgoal_rr_aux5:"bst = BPF_Success v \<Longrightarrow> bst' = bpf_interp 3 prog bst enable_stack_frame_gaps program_vm_addr \<Longrightarrow> bst = bst'"
  by (simp add: numeral_3_eq_3)

(*value "bpf_interp 0 [0x95::u8,0x00,0x00,0x00,0x00,0x00,0x00,0x00] (BPF_Success v) enable_stack_frame_gaps program_vm_addr"*)

lemma bpf_interp_list_aux1:
  assumes a0:"bpf_find_instr 0 prog = Some bins" and
  a1:"prog = [0x95::u8,0x00,0x00,0x00,0x00,0x00,0x00,0x00]" and
  a2:"bst' = step 0 bins rs m ss sv fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu" and
  a3:"bst' = BPF_Success v" and
  (*a4:"bst = init_bpf_state init_reg_map init_mem fuel V1"*)
  a4:"bst = BPF_OK 0 rs m ss sv fm cur_cu remain_cu "
shows "bst' = bpf_interp 3 prog bst enable_stack_frame_gaps program_vm_addr"
proof- 
  have b0:"bins = BPF_EXIT" using addq_subgoal_rr_aux4 a0 a1 by simp
  have b1:"length prog = 1*INSN_SIZE" using a1 INSN_SIZE_def by auto
  thus ?thesis using a2 a3 a1 a0 b0 addq_subgoal_rr_aux5 a4 (*init_bpf_state_def init_reg_map_def init_mem_def init_stack_state_def init_func_map_def*)
    sorry
  qed

lemma bpf_interp_list_aux2:"bpf_find_prog 3 0 prog = Some bins \<Longrightarrow> 
  prog = [0x0f::u8,0x12,0x00,0x00,0x00,0x00,0x00,0x00,0x95::u8,0x00,0x00,0x00,0x00,0x00,0x00,0x00] \<Longrightarrow>
  BPF_OK 1 rs2 m ss sv fm (cur_cu+1) remain_cu = step 0 (bins!0) rs m ss sv fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu \<Longrightarrow>
  st2 = step 1 (bins!1) rs2 m ss sv fm enable_stack_frame_gaps program_vm_addr (cur_cu+1) remain_cu \<Longrightarrow>
  bst' = bpf_interp 3 prog bst enable_stack_frame_gaps program_vm_addr \<Longrightarrow> st2 = bst'"
  sorry

lemma consistency_proof_aux1:
  assumes a0:"is_refined_state2 bst xst" and
    a1:"bins = BPF_ALU64 BPF_ADD dst (SOReg src) " and
    a2:"bpf_find_instr 0 prog = Some bins" and
    a3:"bst' = bpf_interp fuel prog bst enable_stack_frame_gaps program_vm_addr" and
    a4:"JIT_Success jprog = jit_compile fuel' prog (JIT_OK init_jitcomp) " and
    a5:"xst' = binary_execute fuel' jprog xst" and 
    a6:"bst = BPF_OK 0 rs m ss sv fm cur_cu remain_cu" and
    a7:"xst = Bin_OK 0 reg mem" and
    a8:"mem = m"
  shows "is_refined_state2 bst' xst'"
proof - 
  have "\<exists> bst2. bst2 = step 0 bins rs m ss sv fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu " by simp
  obtain bst2 where b1_0:"bst2 = step 0 bins rs m ss sv fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu " by auto
  (*have "bpf_find_instr 0 "*)
  have b1_1:"bins = BPF_ALU64 BPF_ADD dst (SOReg src)" using a1 by simp
  hence b1_2:"\<exists> rs2. BPF_OK 1 rs2 m ss sv fm (cur_cu+1) remain_cu = bst2" using b1_0 b1_1 addq_subgoal_rr_aux2 by simp
  obtain rs2 where b1:"BPF_OK 1 rs2 m ss sv fm (cur_cu+1) remain_cu = bst2" using b1_2 by auto
  (*have "\<exists> bst3. bst3 = step 1 (bins!1) rs2 m ss sv fm enable_stack_frame_gaps program_vm_addr (cur_cu+1) remain_cu" by auto
  obtain bst3 where b2_0:"bst3 = step 1 (bins!1) rs2 m ss sv fm enable_stack_frame_gaps program_vm_addr (cur_cu+1) remain_cu " by auto
  have b2_1:"(bins!1) = BPF_EXIT" using a1 by simp
  have b2:"bst3 = bst'" using a1 a2 a3 b2_0 sorry 
  have b2_1:"length bins = 1" using a1 by simp*)
  have b2:"bst2 = bst'"  using a2 a3 b1_0 sorry
  let ?insns = "Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" 
  (*have c0_1:"\<exists> reg mem. xst = Bin_OK 0 reg mem"  sorry
  obtain reg mem where c0:"xst = Bin_OK 0 reg mem" using c0_1 by auto*)
  have c1_0:"\<exists> reg2. exec_instr ?insns 1 reg mem = Next reg2 mem" using addq_subgoal_rr_aux3 by simp
  obtain reg2 where c1:"exec_instr ?insns 1 reg mem  = Next reg2 mem" using c1_0 by auto
  have c2_0:"Bin_OK 1 reg2 mem = xst'" using c1 a5 sorry
  have c2_1:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" using is_refined_state2_def a0 a6 a7 by simp
  have c2:"(\<forall> r. Vlong (rs2 r) = reg2 (IR (bpf_to_x64_reg r)))" using addq_subgoal_rr_generic a0 c1 c2_1 b1_1 addq_subgoal_rr_aux1 b1 a8 by (metis b1_0 nth_Cons_0)
  thus ?thesis using c2_0 b2
    using b1 is_refined_state2_def by force
qed


lemma consistency_proof_aux2:
  assumes a0:"is_refined_state2 bst xst" and
    a1:"bins = [BPF_ALU64 BPF_ADD dst (SOReg src), BPF_EXIT] " and
    a2:"bpf_find_prog fuel 0 prog = Some bins" and
    a3:"bst' = bpf_interp fuel prog bst enable_stack_frame_gaps program_vm_addr" and
    a4:"JIT_Success jprog = jit_compile fuel' prog (JIT_OK init_jitcomp) " and
    a5:"xst' = binary_execute fuel' jprog xst" and 
    a6:"bst = BPF_OK 0 rs m ss sv fm cur_cu remain_cu" and
    a7:"xst = Bin_OK 0 reg mem" and
    a8:"mem = m"
  shows "is_refined_state2 bst' xst'"
proof - 
  have "\<exists> bst2. bst2 = step 0 (bins!0) rs m ss sv fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu " by simp
  obtain bst2 where b1_0:"bst2 = step 0 (bins!0) rs m ss sv fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu " by auto
  (*have "bpf_find_instr 0 "*)
  have b1_1:"(bins!0) = BPF_ALU64 BPF_ADD dst (SOReg src)" using a1 by simp
  hence b1_2:"\<exists> rs2. BPF_OK 1 rs2 m ss sv fm (cur_cu+1) remain_cu = bst2" using b1_0 b1_1 addq_subgoal_rr_aux2 by simp
  obtain rs2 where b1:"BPF_OK 1 rs2 m ss sv fm (cur_cu+1) remain_cu = bst2" using b1_2 by auto
  have "\<exists> bst3. bst3 = step 1 (bins!1) rs2 m ss sv fm enable_stack_frame_gaps program_vm_addr (cur_cu+1) remain_cu" by auto
  obtain bst3 where b2_0:"bst3 = step 1 (bins!1) rs2 m ss sv fm enable_stack_frame_gaps program_vm_addr (cur_cu+1) remain_cu " by auto
  have b2_1:"(bins!1) = BPF_EXIT" using a1 by simp
  have b2:"bst3 = bst'" using a1 a2 a3 b2_0 sorry 
  let ?insns = "[Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src),Pret]" 
  (*have c0_1:"\<exists> reg mem. xst = Bin_OK 0 reg mem"  sorry
  obtain reg mem where c0:"xst = Bin_OK 0 reg mem" using c0_1 by auto*)
  have c1_0:"\<exists> reg2. exec_instr (?insns!0) 1 reg mem = Next reg2 mem" using addq_subgoal_rr_aux3 by simp
  obtain reg2 where c1:"exec_instr (?insns!0) 1 reg mem  = Next reg2 mem" using c1_0 by auto
  have c2_1:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" using is_refined_state2_def a0 a6 a7 by simp
  have c2:"(\<forall> r. Vlong (rs2 r) = reg2 (IR (bpf_to_x64_reg r)))" using addq_subgoal_rr_generic a0 c1 c2_1 b1_1 addq_subgoal_rr_aux1 b1 a8 by (metis b1_0 nth_Cons_0)
  thus ?thesis sorry
qed

