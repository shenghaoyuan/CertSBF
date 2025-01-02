theory bpfConsistencyAux3
  imports Main Interpreter x64Semantics 
  x64Assembler x64DecodeProof Mem JITCommType  bpfConsistencyAux1
begin


subsubsection   \<open> BPF_ALU64 LSH aux\<close>

lemma shl_subgoal_rr_aux2_1:"xins = Pmovq_rr (x64Syntax.RCX) src  \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> m'' = m "
  apply(unfold exec_instr_def) by simp

lemma shl_subgoal_rr_aux2_2:"xins = Pshlq_r dst \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> m'' = m"
  apply(unfold exec_instr_def) by simp

lemma shl_subgoal_rr_aux2_3:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX) src),(Pshlq_r dst)]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " 
  shows " m'' = m"
  using shl_subgoal_rr_aux2_1 shl_subgoal_rr_aux2_2 
  by (metis One_nat_def a0 a1 a2 nth_Cons_0 nth_Cons_Suc)

lemma shl_subgoal_rr_aux2:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX) src),(Pshlq_r dst)]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " 
  shows " m'' = m"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 shl_subgoal_rr_aux2_3 
    by (meson interp3_length2_aux2)
qed

lemma shl_subgoal_rr_aux3_1:"xins = Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src)\<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> reg'' (IR SP) = reg (IR SP) "
  apply(unfold exec_instr_def reg_rsp_consist bpf_to_x64_reg_corr) 
  using nextinstr_def reg_rsp_consist by fastforce

lemma shl_subgoal_rr_aux4_2:"xins = Pmovq_rr (x64Syntax.RCX) src \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r . r \<noteq> x64Syntax.RCX \<longrightarrow> reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def)
  by auto

lemma  shl_subgoal_rr_aux4_3:"xins = Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src) \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r. bpf_to_x64_reg r \<noteq> x64Syntax.RCX \<longrightarrow> reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def)
  by simp

lemma shl_subgoal_rr_aux4_4:"xins = Pshlq_r dst \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r . r \<noteq> dst \<longrightarrow> reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def)
  by auto

lemma  shl_subgoal_rr_aux4_5:"xins = Pshlq_r (bpf_to_x64_reg dst) \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def)
  by simp

lemma  shl_subgoal_rr_aux4_6:"xins = Ppushl_r x64Syntax.RCX \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r. r \<notin> {(bpf_to_x64_reg dst), x64Syntax.RCX, x64Syntax.RSP} \<longrightarrow> reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold  exec_push_def nextinstr_nf_def nextinstr_def sub64_def Let_def  vlong_of_memory_chunk_def)
  apply(cases "reg (IR SP)",simp_all)
      subgoal for x5 apply(cases "storev M32 m (x5 - (32::64 word)) (reg (IR ireg.RCX))",simp_all)
  done
  done

lemma  shl_subgoal_rr_aux4_7:"xins = Ppopl x64Syntax.RCX \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r. r \<notin> {(bpf_to_x64_reg dst), x64Syntax.RCX, x64Syntax.RSP} \<longrightarrow> reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold exec_pop_def nextinstr_nf_def nextinstr_def sub64_def Let_def)
  apply(cases "reg (IR SP)",simp_all)
  subgoal for x5 
  apply(cases "loadv M32 m x5 ",simp_all)
    done
  done

subsubsection   \<open> BPF_ALU64 RSH aux \<close>

lemma shr_subgoal_rr_aux2_2:"xins = Pshrq_r dst \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> m'' = m"
  apply(unfold exec_instr_def) by simp

lemma shr_subgoal_rr_aux2_3:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX) src),(Pshrq_r dst)]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " 
  shows " m'' = m"
  using shl_subgoal_rr_aux2_1 shr_subgoal_rr_aux2_2 
  by (metis One_nat_def a0 a1 a2 nth_Cons_0 nth_Cons_Suc)

lemma shr_subgoal_rr_aux2:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX) src),(Pshrq_r dst)]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " 
  shows " m'' = m"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 shr_subgoal_rr_aux2_3 
    by (meson interp3_length2_aux2)
qed


lemma shr_subgoal_rr_aux4_4:"xins = Pshrq_r dst \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r . r \<noteq> dst \<longrightarrow> reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def)
  by auto

lemma  shr_subgoal_rr_aux4_5:"xins = Pshrq_r (bpf_to_x64_reg dst) \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def)
  by simp

subsubsection   \<open> BPF_ALU64 ARSH aux \<close>

lemma sar_subgoal_rr_aux2_2:"xins = Psarq_r dst \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> m'' = m"
  apply(unfold exec_instr_def) by simp

lemma sar_subgoal_rr_aux2_3:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX) src),(Psarq_r dst)]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " 
  shows " m'' = m"
  using shl_subgoal_rr_aux2_1 sar_subgoal_rr_aux2_2 
  by (metis One_nat_def a0 a1 a2 nth_Cons_0 nth_Cons_Suc)

lemma sar_subgoal_rr_aux2:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX) src),(Psarq_r dst)]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " 
  shows " m'' = m"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 sar_subgoal_rr_aux2_3 
    by (meson interp3_length2_aux2)
qed


lemma sar_subgoal_rr_aux4_4:"xins = Psarq_r dst \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r . r \<noteq> dst \<longrightarrow> reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def)
  by auto

lemma  sar_subgoal_rr_aux4_5:"xins = Psarq_r (bpf_to_x64_reg dst) \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def)
  by simp

subsubsection   \<open> BPF_ALU64 shift \<close>

lemma shift_subgoal_rr_aux4_8:
  assumes a0:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src),op (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and
    a2: "op \<in> {Pshrq_r, Pshlq_r, Psarq_r}"
  shows "\<forall> r . bpf_to_x64_reg r \<notin> {(bpf_to_x64_reg dst), x64Syntax.RCX, x64Syntax.RSP} \<longrightarrow> reg'' (IR (bpf_to_x64_reg r )) = reg (IR (bpf_to_x64_reg r ))"
proof-
  have b0_0:"length xins = 4" using a0 by simp
  have b0_1:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (xins!0) 1 reg m)" using exec_instr_def a0
    by (metis a1 interp3_list_aux1 list.distinct(1) outcome.exhaust)
  have b0_2:"length xins >0" using a0 by simp
  have b0_3:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = interp3 (tl xins) (Next reg1 m1) " 
       using a1 by (metis b0_1 b0_2 interp3.elims length_greater_0_conv list.sel(3) nth_Cons_0 outcome.case(1))
  then obtain reg1 m1 where b0_4:" Next reg1 m1 = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = interp3 (tl xins) (Next reg1 m1)" by auto
  have b0:"\<forall> r . r \<notin> {(bpf_to_x64_reg dst), x64Syntax.RCX, x64Syntax.RSP} \<longrightarrow> reg1 (IR r) = reg (IR r)" using a0 b0_2 shl_subgoal_rr_aux4_6
    by (metis b0_4 nth_Cons_0)
  have b1_1:"\<exists> reg2 m2. Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1)" using exec_instr_def a0 by simp
  then obtain reg2 m2 where b1_2:"Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1)" using b1_1 by auto
  have b1_3:"take 2 xins = [xins!0]@[xins!1]" by (simp add: a0 numeral_2_eq_2 take_Suc_conv_app_nth)
  have b1_4:"Next reg2 m2 = interp3 (take 2 xins) (Next reg m)" using a0 b1_2 b1_3 b0_4
    by (metis append_Cons append_Nil interp3.simps(2) interp3_list_aux3 outcome.case(1))
  have b1_5:" Next reg2 m2 = interp3 (take 2 xins) (Next reg m) \<and> Next reg'' m'' = interp3 (drop 2 xins) (Next reg2 m2)" using interp3_length4_aux4 b0_0 a1 b1_4 by metis
  have b1:"\<forall> r . r \<notin> {(bpf_to_x64_reg dst), x64Syntax.RCX} \<longrightarrow> reg1 (IR r) = reg2 (IR r)" using a0 b1_2
    by (metis One_nat_def insertCI nth_Cons_0 nth_Cons_Suc shl_subgoal_rr_aux4_2)
  have b2_1:"\<exists> reg3 m3. Next reg3 m3 = (exec_instr (xins!2) 1 reg2 m2)" 
    using a0 a2 exec_instr_def by auto
  then obtain reg3 m3 where b2_2:"Next reg3 m3 = (exec_instr (xins!2) 1 reg2 m2)" using b1_1 by auto
  have b2_3:"take 3 xins = [xins!0]@[xins!1]@[xins!2]" using a0 
    by (simp add: add_One numeral_3_eq_3 numeral_nat(2) take_Suc_conv_app_nth)
  have b2_4:"Next reg3 m3 = interp3 (take 3 xins) (Next reg m)" using a0 b1_5 b2_3 b2_2
    using append_Cons append_Nil b0_4 b1_2 b1_4 interp3.simps(2) interp3_list_aux3 outcome.case(1) by metis
  have b2_5:"[xins!0]@[xins!1]@[xins!2]@[last xins] = xins" using append_butlast_last_id a0 by fastforce
  have b2_6:"(last xins) = (xins!3)" using a0 by (metis One_nat_def Suc_eq_plus1 Suc_numeral add_2_eq_Suc diff_Suc_1' last_conv_nth length_Suc_conv list.simps(3) list.size(3) semiring_norm(5))
  have b2_7: "(butlast xins) = [xins!0]@[xins!1]@[xins!2]" using a0 b2_6 by simp
  have b2_8:"butlast xins = take 3 xins" using a0 b2_7 by simp
  have b2_9:"Next reg3 m3 = interp3 (butlast xins) (Next reg m) \<and> Next reg'' m'' = (exec_instr (last xins) 1 reg3 m3)" using a0 b2_4 b2_8 interp3_length4_aux4 b0_0 a1 interp3_list_aux3 a1 outcome.inject
    by (metis interp3_length4_aux6)
  have b2_10:"Next reg3 m3 = interp3 (take 3 xins) (Next reg m) \<and> Next reg'' m'' = (exec_instr (last xins) 1 reg3 m3)" using b2_9 b2_8 by simp
  have b2:"\<forall> r . r \<notin> {(bpf_to_x64_reg dst), x64Syntax.RCX} \<longrightarrow> reg3 (IR r) = reg2 (IR r)" using a0 b1_2
    using b2_2 shr_subgoal_rr_aux4_4 shl_subgoal_rr_aux4_4 sar_subgoal_rr_aux4_4 a2 by auto
  hence b3_1:" \<exists> reg4 m4. Next reg4 m4 = (exec_instr (xins!3) 1 reg3 m3)" 
    using b2_6 b2_9 by auto
  then obtain reg4 m4 where b4:"Next reg4 m4 = (exec_instr (xins!3) 1 reg3 m3)" using b3_1 by auto
  have b3:"Next reg4 m4 = Next reg'' m''" using interp3_list_aux3
    by (simp add: b2_6 b2_9 b4)
  have b4:"\<forall> r . r \<notin> {(bpf_to_x64_reg dst), x64Syntax.RCX, x64Syntax.RSP} \<longrightarrow> reg3 (IR r) = reg'' (IR r)" using a0 b0 b1 b2 shl_subgoal_rr_aux4_7 
    by (metis append_Cons append_Nil b2_5 b2_9 list.sel(1) list.sel(3))
  thus ?thesis using b0 b1 b2 b3 by simp
qed


lemma shl_subgoal_rr_aux6:"
    bins = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 fm (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu \<Longrightarrow>
    \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(unfold eval_alu64_def,simp)
  by (unfold eval_alu64_aux2_def, simp_all)

lemma shr_subgoal_rr_aux6:"
    bins = BPF_ALU64 BPF_RSH dst (SOReg src) \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 fm (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu \<Longrightarrow>
    \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(unfold eval_alu64_def,simp)
  by (unfold eval_alu64_aux2_def, simp_all)


lemma sar_subgoal_rr_aux6:"
    bins = BPF_ALU64 BPF_ARSH dst (SOReg src) \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 fm (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu \<Longrightarrow>
    \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(unfold eval_alu64_def,simp)
  by (unfold eval_alu64_aux3_def, simp_all)
end