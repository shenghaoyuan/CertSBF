theory bpfConsistencyAux1
  imports Main Interpreter x64Semantics 
  x64Assembler x64DecodeProof Mem JITCommType
begin

lemma div_subgoal_rr_aux1:"
    bins = BPF_ALU64 BPF_DIV dst (SOReg src) \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
    \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(unfold eval_alu64_def,simp)
  apply(cases is_v1,simp_all)
  apply (unfold eval_alu64_aux1_def Let_def, simp_all)
  apply(split if_splits, simp_all)
  done


lemma div_subgoal_rr_aux3_1:
  assumes a0:"bins = BPF_ALU64 BPF_DIV dst (SOReg src)" and
     a1:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX) ri,Pshlq_r rd,Ppopl x64Syntax.RCX]" and
     a2:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
     a3:"Next reg' m' = interp3 xins (Next reg m)" and
     a4:"rd = (bpf_to_x64_reg dst)" and
     a5:"ri = (bpf_to_x64_reg src)" and
     a6:"reg (IR rd) = Vlong n1" and
     a7:"reg (IR ri) = Vlong n2" and
     a8:"n1  = rs dst" and
     a9:"n2  = rs src" and
     a10:"(bpf_to_x64_reg dst) = x64Syntax.RAX"
     shows "Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
  sorry


lemma div_subgoal_rr_aux3:
  assumes a0:"bins = BPF_ALU64 BPF_DIV dst (SOReg src)" and
     a1:"xins = Pdivq_r ri" and
     a2:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
     a3:"Next reg' m' = exec_instr xins sz reg m" and
     a4:"rd = (bpf_to_x64_reg dst)" and
     a5:"ri = (bpf_to_x64_reg src)" and
     a6:"reg (IR rd) = Vlong n1" and
     a7:"reg (IR ri) = Vlong n2" and
     a8:"n1  = rs dst" and
     a9:"n2  = rs src" and
     a10:"(bpf_to_x64_reg dst) = x64Syntax.RAX" and
     a11:"reg (IR x64Syntax.RAX) = Vlong 0"
     shows "Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
  sorry
  

lemma reg_rax_rdx1:"(bpf_to_x64_reg dst) = x64Syntax.RAX \<longrightarrow> (bpf_to_x64_reg dst) \<noteq> x64Syntax.RDX" 
  apply(cases dst) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)

lemma sarq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_DIV dst (SOReg src)" and
       a1:"per_jit_div_and_mod_reg64 True dst src = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decodes (unat pc) l_bin = Some v" and
       a4:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
       a5:"Next reg' m' = interp3 xins (Next reg m) " and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" and
       a7:"(bpf_to_x64_reg dst) = x64Syntax.RAX" and
       a8:"xins = map snd v"
  shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b:"Some bl = x64_encodes_suffix [Ppushl_r x64Syntax.RDX, Pxorq_rr (x64Syntax.RDX) (x64Syntax.RDX),
  Pdivq_r (bpf_to_x64_reg src), Ppopl x64Syntax.RDX]" 
    using a0 a1 a7 per_jit_div_and_mod_reg64_def Let_def a7 reg_rax_rdx1 by simp
  moreover have b0:"xins = [Ppushl_r x64Syntax.RDX, Pxorq_rr (x64Syntax.RDX) (x64Syntax.RDX),
  Pdivq_r (bpf_to_x64_reg src), Ppopl x64Syntax.RDX]" 
    using x64_encodes_decodes_consistency per_jit_shift_reg64_def a1 a2 a3 
    using a8 calculation by presburger
    moreover have b1:"Vlong (rs dst) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using div_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 a7 sorry
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 sorry
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 div_subgoal_rr_aux1 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed

end