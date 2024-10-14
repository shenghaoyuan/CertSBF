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

lemma shl_subgoal_rr_aux3_2:"xins = Pshlq_r (bpf_to_x64_reg dst) \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> reg'' (IR SP) = reg (IR SP) "
  apply(unfold exec_instr_def reg_rsp_consist bpf_to_x64_reg_corr)
  apply(cases xins, simp_all)
  apply(unfold nextinstr_def reg_rsp_consist shl64_def nextinstr_nf_def reg_rsp_consist)
  apply(cases "reg (IR (bpf_to_x64_reg dst))",simp_all)
      apply metis
  subgoal for x2 apply (simp add:add64_def)sorry
  subgoal for x3 apply (simp add:add64_def) sorry
  subgoal for x4 apply (simp add:add64_def) sorry
  subgoal for x5 apply (simp add:add64_def) 
    using reg_rsp_consist by blast
  (* no dealing with VByte conversion *)
  done
lemma shl_subgoal_rr_aux3_3:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src)),(Pshlq_r (bpf_to_x64_reg dst))]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " 
  shows " reg'' (IR SP) = reg (IR SP) "
  using shl_subgoal_rr_aux3_1 shl_subgoal_rr_aux3_2 reg_rsp_consist
  by (metis One_nat_def a0 a1 a2 nth_Cons_0 nth_Cons_Suc)

lemma shl_subgoal_rr_aux3:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src)),(Pshlq_r (bpf_to_x64_reg dst))]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " 
  shows "reg'' (IR SP) = reg (IR SP)"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 shl_subgoal_rr_aux3_3 
    by (meson interp3_length2_aux2)
qed

lemma shl_subgoal_rr_aux4_1:
  assumes a0:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src),Pshlq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" 
  shows "reg'' (IR x64Syntax.RCX) = reg (IR x64Syntax.RCX)"
proof-
  have a3:"hd xins = Ppushl_r x64Syntax.RCX" using a0 by simp
  have a4:"last xins = Ppopl x64Syntax.RCX" using a0 by simp
  have b0:"(butlast(tl xins)) = [Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src),Pshlq_r (bpf_to_x64_reg dst)]" using a0 by simp
  let ?midlist = "[ Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src) ,Pshlq_r (bpf_to_x64_reg dst)]"
  have b1:"\<exists> reg' m'. Next reg' m' = exec_push 1 M32 m reg (reg (IR x64Syntax.RCX))" using exec_instr_def a0 
    using a1 exec_push_def a0 
    by (smt (verit, del_insts) instruction.simps(6295) interp3.simps(2) option.case_eq_if outcome.case(2) outcome.simps(4))
  then obtain reg' m' where b0:"Next reg' m' = exec_push 1 M32 m reg (reg (IR x64Syntax.RCX))" by blast
  have b2_0:"length xins = 4" using a0 by simp
  have b2_1: "Next reg' m' = (exec_instr (xins!0) 1 reg m)" 
    by (simp add: a0 b0 exec_instr_def)
  have b2:"\<exists> reg2 m2. interp3 ?midlist (Next reg' m') = Next reg2 m2" using interp3_length4_aux5 b1 a0 a1 b2_0 b0 b2_1 by fastforce
  then obtain reg2 m2 where b3:"interp3 ?midlist (Next reg' m') = Next reg2 m2" by auto
  have b4:"m2 = m'" using shl_subgoal_rr_aux2 by (metis b3)
  have b5:"reg' (IR SP) =  reg2 (IR SP)" using shl_subgoal_rr_aux3 b3 by metis
  have b6:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " using a0 by (simp add: b0 exec_instr_def)
  have b7_1:"length xins \<ge> (2::nat)" using a0 by simp
  have b7_2:"Next reg2 m2 = interp3 (butlast xins) (Next reg m)" using b3 b0 a0 by (simp add: b6)
  have b7:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m2)" using interp3_length4_aux4 b2_0 b7_1 b7_2 by (metis a1 outcome.inject)
  have b8:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m')" using b7 b4 by simp
  thus ?thesis using a3 a4 b4 b5 b6 b8 a1 push_pop_subgoal_rr_aux2_3
    by (metis a0 b3 butlast.simps(2) list.distinct(1) list.sel(3))
qed

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

lemma shr_subgoal_rr_aux3_2:"xins = Pshrq_r (bpf_to_x64_reg dst) \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> reg'' (IR SP) = reg (IR SP) "
  apply(unfold exec_instr_def reg_rsp_consist bpf_to_x64_reg_corr)
  apply(cases xins, simp_all)
  apply(unfold nextinstr_def reg_rsp_consist shr64_def nextinstr_nf_def reg_rsp_consist)
  apply(cases "reg (IR (bpf_to_x64_reg dst))",simp_all)
      apply metis
  subgoal for x2 apply (simp add:add64_def)sorry
  subgoal for x3 apply (simp add:add64_def) sorry
  subgoal for x4 apply (simp add:add64_def) sorry
  subgoal for x5 apply (simp add:add64_def) 
    using reg_rsp_consist by blast
  (* no dealing with VByte conversion *)
  done

lemma shr_subgoal_rr_aux3_3:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src)),(Pshrq_r (bpf_to_x64_reg dst))]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " 
  shows " reg'' (IR SP) = reg (IR SP) "
  using shl_subgoal_rr_aux3_1 shr_subgoal_rr_aux3_2 reg_rsp_consist
  by (metis One_nat_def a0 a1 a2 nth_Cons_0 nth_Cons_Suc)

lemma shr_subgoal_rr_aux3:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src)),(Pshrq_r (bpf_to_x64_reg dst))]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " 
  shows "reg'' (IR SP) = reg (IR SP)"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 shr_subgoal_rr_aux3_3 
    by (meson interp3_length2_aux2)
qed

lemma shr_subgoal_rr_aux4_1:
  assumes a0:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src),Pshrq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and
    a2:"Vlong n1 = reg (IR SP) "
  shows "reg'' (IR x64Syntax.RCX) = reg (IR x64Syntax.RCX)"
proof-
  have a3:"hd xins = Ppushl_r x64Syntax.RCX" using a0 by simp
  have a4:"last xins = Ppopl x64Syntax.RCX" using a0 by simp
  have b0:"(butlast(tl xins)) = [Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src),Pshrq_r (bpf_to_x64_reg dst)]" using a0 by simp
  let ?midlist = "[ Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src) ,Pshrq_r (bpf_to_x64_reg dst)]"
  have b1:"\<exists> reg' m'. Next reg' m' = exec_push 1 M32 m reg (reg (IR x64Syntax.RCX))" using exec_instr_def a0 
    using a1 exec_push_def a0 
    by (smt (verit, del_insts) instruction.simps(6295) interp3.simps(2) option.case_eq_if outcome.case(2) outcome.simps(4))
  then obtain reg' m' where b0:"Next reg' m' = exec_push 1 M32 m reg (reg (IR x64Syntax.RCX))" by blast
  have b2_0:"length xins = 4" using a0 by simp
  have b2_1: "Next reg' m' = (exec_instr (xins!0) 1 reg m)" 
    by (simp add: a0 b0 exec_instr_def)
  have b2:"\<exists> reg2 m2. interp3 ?midlist (Next reg' m') = Next reg2 m2" using interp3_length4_aux5 b1 a0 a1 b2_0 b0 b2_1 by fastforce
  then obtain reg2 m2 where b3:"interp3 ?midlist (Next reg' m') = Next reg2 m2" by auto
  have b4:"m2 = m'" using shr_subgoal_rr_aux2 by (metis b3)
  have b5:"reg' (IR SP) =  reg2 (IR SP)" using shr_subgoal_rr_aux3 b3 by metis
  have b6:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " using a0 by (simp add: b0 exec_instr_def)
  have b7_1:"length xins \<ge> (2::nat)" using a0 by simp
  have b7_2:"Next reg2 m2 = interp3 (butlast xins) (Next reg m)" using b3 b0 a0 by (simp add: b6)
  have b7:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m2)" using interp3_length4_aux4 b2_0 b7_1 b7_2 by (metis a1 outcome.inject)
  have b8:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m')" using b7 b4 by simp
  thus ?thesis using a3 a4 b4 b5 b6 b8 a1 push_pop_subgoal_rr_aux2_3 a2
    using a0 b3 butlast.simps(2) list.distinct(1) list.sel(3)
    by (smt (verit, del_insts) insert_iff)
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

lemma sar_subgoal_rr_aux3_2:"xins = Psarq_r (bpf_to_x64_reg dst) \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> reg'' (IR SP) = reg (IR SP) "
  apply(unfold exec_instr_def reg_rsp_consist bpf_to_x64_reg_corr)
  apply(cases xins, simp_all)
  apply(unfold nextinstr_def reg_rsp_consist shr64_def nextinstr_nf_def reg_rsp_consist)
  apply(cases "reg (IR (bpf_to_x64_reg dst))",simp_all)
      apply(unfold add64_def sar64_def,simp_all)
      apply (cases  Vundef, simp_all)
      apply(cases "reg RIP",simp_all)
  sorry
  (* no dealing with VByte conversion *)
  done

lemma sar_subgoal_rr_aux3_3:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src)),(Psarq_r (bpf_to_x64_reg dst))]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " 
  shows " reg'' (IR SP) = reg (IR SP) "
  using shl_subgoal_rr_aux3_1 sar_subgoal_rr_aux3_2 reg_rsp_consist
  by (metis One_nat_def a0 a1 a2 nth_Cons_0 nth_Cons_Suc)

lemma sar_subgoal_rr_aux3:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src)),(Psarq_r (bpf_to_x64_reg dst))]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " 
  shows "reg'' (IR SP) = reg (IR SP)"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 sar_subgoal_rr_aux3_3 
    by (meson interp3_length2_aux2)
qed

lemma sar_subgoal_rr_aux4_1:
  assumes a0:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src),Psarq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" 
  shows "reg'' (IR x64Syntax.RCX) = reg (IR x64Syntax.RCX)"
proof-
  have a3:"hd xins = Ppushl_r x64Syntax.RCX" using a0 by simp
  have a4:"last xins = Ppopl x64Syntax.RCX" using a0 by simp
  have b0:"(butlast(tl xins)) = [Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src),Psarq_r (bpf_to_x64_reg dst)]" using a0 by simp
  let ?midlist = "[ Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src) ,Psarq_r (bpf_to_x64_reg dst)]"
  have b1:"\<exists> reg' m'. Next reg' m' = exec_push 1 M32 m reg (reg (IR x64Syntax.RCX))" using exec_instr_def a0 
    using a1 exec_push_def a0 
    by (smt (verit, del_insts) instruction.simps(6295) interp3.simps(2) option.case_eq_if outcome.case(2) outcome.simps(4))
  then obtain reg' m' where b0:"Next reg' m' = exec_push 1 M32 m reg (reg (IR x64Syntax.RCX))" by blast
  have b2_0:"length xins = 4" using a0 by simp
  have b2_1: "Next reg' m' = (exec_instr (xins!0) 1 reg m)" 
    by (simp add: a0 b0 exec_instr_def)
  have b2:"\<exists> reg2 m2. interp3 ?midlist (Next reg' m') = Next reg2 m2" using interp3_length4_aux5 b1 a0 a1 b2_0 b0 b2_1 by fastforce
  then obtain reg2 m2 where b3:"interp3 ?midlist (Next reg' m') = Next reg2 m2" by auto
  have b4:"m2 = m'" using sar_subgoal_rr_aux2 by (metis b3)
  have b5:"reg' (IR SP) =  reg2 (IR SP)" using sar_subgoal_rr_aux3 b3 by metis
  have b6:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " using a0 by (simp add: b0 exec_instr_def)
  have b7_1:"length xins \<ge> (2::nat)" using a0 by simp
  have b7_2:"Next reg2 m2 = interp3 (butlast xins) (Next reg m)" using b3 b0 a0 by (simp add: b6)
  have b7:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m2)" using interp3_length4_aux4 b2_0 b7_1 b7_2 by (metis a1 outcome.inject)
  have b8:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m')" using b7 b4 by simp
  thus ?thesis using a3 a4 b4 b5 b6 b8 a1 push_pop_subgoal_rr_aux2_3
    by (metis a0 b3 butlast.simps(2) list.distinct(1) list.sel(3))
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
    by (simp add: One_nat_def Suc_1 add_One numeral_3_eq_3 numeral_nat(2) take_Suc_conv_app_nth)
  have b2_4:"Next reg3 m3 = interp3 (take 3 xins) (Next reg m)" using a0 b1_5 b2_3 b2_2
    using append_Cons append_Nil b0_4 b1_2 b1_4 interp3.simps(2) interp3_list_aux3 outcome.case(1) by metis
  have b2_5:"[xins!0]@[xins!1]@[xins!2]@[last xins] = xins" using append_butlast_last_id a0 by fastforce
  have b2_6:"(last xins) = (xins!3)" using a0 by (metis One_nat_def Suc_eq_plus1 Suc_numeral add_2_eq_Suc diff_Suc_1' last_conv_nth length_Suc_conv list.simps(3) list.size(3) list_consists_4 semiring_norm(5))
  have b2_7: "(butlast xins) = [xins!0]@[xins!1]@[xins!2]" using a0 b2_6 by simp
  have b2_8:"butlast xins = take 3 xins" using a0 b2_7 by simp
  have b2_9:"Next reg3 m3 = interp3 (butlast xins) (Next reg m) \<and> Next reg'' m'' = (exec_instr (last xins) 1 reg3 m3)" using a0 b2_4 b2_8 interp3_length4_aux4 b0_0 a1 by (metis a1 outcome.inject)
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

lemma shift_subgoal_rr_aux4:
  assumes a0:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src) ,op (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX] " and
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " and
    a2: "op \<in> {Pshrq_r, Pshlq_r, Psarq_r}"
  shows" \<forall> r \<noteq> dst. reg'' (IR  (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" 
proof-
  have b0:"reg'' (IR x64Syntax.RCX) = reg (IR x64Syntax.RCX)" using a0 a1 a2 shl_subgoal_rr_aux4_1 shr_subgoal_rr_aux4_1 sar_subgoal_rr_aux4_1 by auto
  have b1:"\<forall> r . bpf_to_x64_reg r  \<notin> {(bpf_to_x64_reg dst), x64Syntax.RCX, x64Syntax.RSP} \<longrightarrow> reg'' (IR (bpf_to_x64_reg r )) = reg (IR (bpf_to_x64_reg r ))" using shift_subgoal_rr_aux4_8 a0 a1 a2 by auto
  have b1_1:"\<forall> r. (bpf_to_x64_reg r) \<noteq> x64Syntax.RSP" using a0 reg_rsp_consist by simp
  thus ?thesis using  b0 b1 b1_1  by force
qed

lemma shl_subgoal_rr_aux5:
  assumes a0:"bins = BPF_ALU64 BPF_LSH dst (SOReg src)" and
     a1:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX) ri,Pshlq_r rd,Ppopl x64Syntax.RCX]" and
     a2:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
     a3:"Next reg' m' = interp3 xins (Next reg m)" and
     a4:"rd = (bpf_to_x64_reg dst)" and
     a5:"ri = (bpf_to_x64_reg src)" and
     a6:"reg (IR rd) = Vlong n1" and
     a7:"reg (IR ri) = Vlong n2" and
     a8:"n1  = rs dst" and
     a9:"n2  = rs src" and
     a9:"(bpf_to_x64_reg dst) \<noteq> x64Syntax.RCX"
     shows "Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
  sorry
  done

lemma shl_subgoal_rr_aux6:"
    bins = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
    \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(unfold eval_alu64_def,simp)
  by (unfold eval_alu64_aux2_def, simp_all)

lemma shlq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_LSH dst (SOReg src)" and
       a1:"per_jit_shift_reg64 4 dst src = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decodes (unat pc) l_bin = Some v" and
       a4:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
       a5:"Next reg' m' = interp3 xins (Next reg m) " and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" and
       a7:"(bpf_to_x64_reg dst) \<noteq> x64Syntax.RCX" and
       a8:"xins = map snd v"
  shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b:"Some bl = x64_encodes_suffix [Ppushl_r x64Syntax.RCX, Pmovq_rr(x64Syntax.RCX) (bpf_to_x64_reg src),Pshlq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" 
    using a0 a1 a7 per_jit_shift_reg64_def by simp
  moreover have b0:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src),Pshlq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" 
    using x64_encodes_decodes_consistency per_jit_shift_reg64_def a1 a2 a3 
    using a8 calculation by presburger
    moreover have b1:"Vlong (rs dst) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using shl_subgoal_rr_aux5 b0 b1 b2 a0 a4 a5 by (metis a7)
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 shift_subgoal_rr_aux4 by simp
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 shl_subgoal_rr_aux6 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed

lemma shr_subgoal_rr_aux5:
  assumes a0:"bins = BPF_ALU64 BPF_RSH dst (SOReg src)" and
     a1:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX) ri,Pshrq_r rd,Ppopl x64Syntax.RCX]" and
     a2:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
     a3:"Next reg' m' = interp3 xins (Next reg m)" and
     a4:"rd = (bpf_to_x64_reg dst)" and
     a5:"ri = (bpf_to_x64_reg src)" and
     a6:"reg (IR rd) = Vlong n1" and
     a7:"reg (IR ri) = Vlong n2" and
     a8:"n1  = rs dst" and
     a9:"n2  = rs src" and
     a9:"(bpf_to_x64_reg dst) \<noteq> x64Syntax.RCX"
     shows "Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
  sorry


lemma shr_subgoal_rr_aux6:"
    bins = BPF_ALU64 BPF_RSH dst (SOReg src) \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
    \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(unfold eval_alu64_def,simp)
  by (unfold eval_alu64_aux2_def, simp_all)

lemma shrq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_RSH dst (SOReg src)" and
       a1:"per_jit_shift_reg64 5 dst src = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decodes (unat pc) l_bin = Some v" and
       a4:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
       a5:"Next reg' m' = interp3 xins (Next reg m) " and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" and
       a7:"(bpf_to_x64_reg dst) \<noteq> x64Syntax.RCX" and
       a8:"xins = map snd v"
  shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b:"Some bl = x64_encodes_suffix [Ppushl_r x64Syntax.RCX, Pmovq_rr(x64Syntax.RCX) (bpf_to_x64_reg src),Pshrq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" 
    using a0 a1 a7 per_jit_shift_reg64_def by simp
  moreover have b0:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src),Pshrq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" 
    using x64_encodes_decodes_consistency per_jit_shift_reg64_def a1 a2 a3 
    using a8 calculation by presburger
    moreover have b1:"Vlong (rs dst) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using shr_subgoal_rr_aux5 b0 b1 b2 a0 a4 a5 a7 by metis
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 shift_subgoal_rr_aux4 by simp
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 shr_subgoal_rr_aux6 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed

lemma sar_subgoal_rr_aux5:
  assumes a0:"bins = BPF_ALU64 BPF_ARSH dst (SOReg src)" and
     a1:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX) ri,Psarq_r rd,Ppopl x64Syntax.RCX]" and
     a2:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
     a3:"Next reg' m' = interp3 xins (Next reg m)" and
     a4:"rd = (bpf_to_x64_reg dst)" and
     a5:"ri = (bpf_to_x64_reg src)" and
     a6:"reg (IR rd) = Vlong n1" and
     a7:"reg (IR ri) = Vlong n2" and
     a8:"n1  = rs dst" and
     a9:"n2  = rs src" and
     a9:"(bpf_to_x64_reg dst) \<noteq> x64Syntax.RCX"
     shows "Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
  sorry


lemma sar_subgoal_rr_aux6:"
    bins = BPF_ALU64 BPF_ARSH dst (SOReg src) \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
    \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(unfold eval_alu64_def,simp)
  by (unfold eval_alu64_aux3_def, simp_all)

lemma sarq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_ARSH dst (SOReg src)" and
       a1:"per_jit_shift_reg64 (7::nat) dst src = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decodes (unat pc) l_bin = Some v" and
       a4:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
       a5:"Next reg' m' = interp3 xins (Next reg m) " and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" and
       a7:"(bpf_to_x64_reg dst) \<noteq> x64Syntax.RCX" and
       a8:"xins = map snd v"
  shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b:"Some bl = x64_encodes_suffix [Ppushl_r x64Syntax.RCX, Pmovq_rr(x64Syntax.RCX) (bpf_to_x64_reg src),Psarq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" 
    using a0 a1 a7 per_jit_shift_reg64_def by simp
  moreover have b0:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src),Psarq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" 
    using x64_encodes_decodes_consistency per_jit_shift_reg64_def a1 a2 a3 
    using a8 calculation by presburger
    moreover have b1:"Vlong (rs dst) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using sar_subgoal_rr_aux5 b0 b1 b2 a0 a4 a5 a7 by metis
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 shift_subgoal_rr_aux4 by simp
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 sar_subgoal_rr_aux6 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed
end