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
definition is_refined_state :: "bpf_state \<Rightarrow> jit_state \<Rightarrow> bool" where
"is_refined_state bst xst = (case bst of BPF_OK pc rs m ss sv fm cur_cu remain_cu \<Rightarrow>
                                case xst of JIT_OK jcomp res s_v \<Rightarrow> (\<forall> r. Vlong (rs r) = res (IR (bpf_to_x64_reg r))) | _ \<Rightarrow> False |
                                BPF_Success ret \<Rightarrow> case xst of JIT_Success \<Rightarrow> True | _ \<Rightarrow> False |
                            _ \<Rightarrow> False)"

definition is_refined_state2 :: "bpf_state \<Rightarrow> outcome \<Rightarrow> bool" where
"is_refined_state2 bst xst = (case bst of BPF_OK pc rs m ss sv fm cur_cu remain_cu \<Rightarrow>
                                case xst of Next reg mem \<Rightarrow> (\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))) \<and> m = mem | _ \<Rightarrow> False |
                             BPF_EFlag \<Rightarrow> case xst of Next reg mem \<Rightarrow> False | Stuck \<Rightarrow> True |
                             BPF_Success ret \<Rightarrow> case xst of Next reg mem \<Rightarrow> reg (IR x64Syntax.RAX) = Vlong ret | 
                                                            Stuck \<Rightarrow> False |
                             BPF_Err \<Rightarrow> False)"

(*fun jit_compile :: "nat \<Rightarrow> bpf_bin \<Rightarrow> reg_map \<Rightarrow> jit_state \<Rightarrow> jit_state " where*)
(*"nat \<Rightarrow> bpf_bin \<Rightarrow> bpf_state \<Rightarrow> bool \<Rightarrow> u64 \<Rightarrow> bpf_state" where*)
lemma consistency_proof_aux:
  assumes a0:"is_refined_state bst xst" and
    a1:"bst' = bpf_interp fuel prog bst enable_stack_frame_gaps program_vm_addr " and
    a2:"xst' = jit_compile fuel prog xst" and 
    a3:"bpf_find_prog 3 0 prog = Some [BPF_ALU64 BPF_ADD BR1 (SOReg BR2), BPF_EXIT]"
  shows "is_refined_state bst' xst'"
  sorry


lemma consistency_proof_aux2:
  assumes a0:"is_refined_state2 bst xst" and
    a1:"bst' = bpf_interp fuel prog st enable_stack_frame_gaps program_vm_addr " and
    a2:"per_jit_ins pc bins rs sv = Some bl" and
    a3:"list_in_list bl (unat pc) l_bin" and
    a4:"x64_decode (unat pc) l_bin = Some (length l_bin, xins)" and
    a5:"xst' = interp3 bbin xst" 
  shows "is_refined_state2 bst' xst'"
  sorry


(*lemma sarq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_ARSH dst (SOReg src)" and
       a1:"per_jit_shift_reg64 7 dst src = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decodes (unat pc) l_bin = Some v" and
       a4:"(BPF_OK pc rs' m' ss' is_v1 fm (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu" and
       a5:"Next reg' m' = interp3 xins (Next reg m) " and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" and
       a7:"(bpf_to_x64_reg dst) \<noteq> x64Syntax.RCX" and
       a8:"xins = map snd v" and
       a9:"Vlong n1 = reg (IR SP)"
  shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
*)