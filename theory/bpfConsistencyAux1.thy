theory bpfConsistencyAux1
  imports Main Interpreter x64Semantics 
  x64Assembler x64DecodeProof Mem JITCommType
begin

lemma interp3_list_aux1:
  assumes a0:"xins\<noteq>[]" and 
          a1:"result = interp3 xins (Next reg m)"
        shows "result = Next reg' m' \<longrightarrow> (exec_instr (xins!0) 1 reg m) \<noteq> Stuck"
  sorry

lemma interp3_list_aux2:
  assumes a0:"length xins = (2::nat)" and 
          a1:"result = interp3 xins (Next reg m)" and
          a2:"Next reg' m' = (exec_instr (xins!0) 1 reg m)"
        shows "result = Next reg'' m'' \<longrightarrow> (exec_instr (xins!1) 1 reg' m') \<noteq> Stuck"
  sorry

lemma interp3_list_aux3:"interp3 [] (Next reg m) = Next reg m"
  by simp

lemma interp3_length2_aux1: assumes a0:"Next reg2 m2 = interp3 xins (Next reg m)" and
  a1:"length xins = (2::nat)"
shows" \<exists> reg' m'. Next reg' m' = (exec_instr (xins!0) 1 reg m) \<and> Next reg2 m2 = (exec_instr (xins!1) 1 reg' m')  "
  sorry

lemma interp3_length2_aux2:"Next reg'' m'' = interp3 xins (Next reg m) \<Longrightarrow> length xins = (2::nat) \<Longrightarrow> \<exists> reg' m'. Next reg' m' = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = (exec_instr (xins!1) 1 reg' m')  "
  using interp3_length2_aux1 by simp



lemma interp3_length4_aux1:
  assumes a0:"xins\<noteq>[]" and 
          a1:"result = interp3 xins (Next reg m)" and
          a2:"Next reg' m' = (exec_instr (xins!0) 1 reg m)"
        shows "result = Next reg'' m'' \<longrightarrow> interp3 (tl xins) (Next reg' m') \<noteq> Stuck"
  sorry

lemma interp3_length4_aux0:
  assumes a0:"length xins = 4" and 
          a1:"result = interp3 xins (Next reg m)" 
        shows "result = Next reg'' m'' \<longrightarrow> (exec_instr (xins!2) 1 reg m) \<noteq> Stuck"
  sorry

lemma interp3_length4_aux2:
  assumes a0:"length xins = (4::nat)" and 
          a1:"result = interp3 xins (Next reg m)" and
          a2:"Next reg2 m2 = interp3 (take 2 xins) (Next reg m)"
        shows "result = Next reg'' m'' \<longrightarrow> interp3 (drop 2 xins) (Next reg2 m2) \<noteq> Stuck"
  sorry
lemma interp3_length4_aux3:
  assumes a0:"length xins = (4::nat)" and 
          a1:"result = interp3 xins (Next reg m)" and
          a2:"Next reg3 m3 = interp3 (butlast xins) (Next reg m)"
        shows "result = Next reg'' m'' \<longrightarrow> (exec_instr (last xins) 1 reg3 m3) \<noteq> Stuck"
  sorry



lemma interp3_length4_aux4:
  assumes a0:"length xins = (4::nat)" and 
          a1:"Next reg'' m''= interp3 xins (Next reg m)" 
        shows "\<exists> reg' m'. Next reg' m' = interp3 (take 2 xins) (Next reg m) \<and> Next reg'' m'' = interp3 (drop 2 xins) (Next reg' m')"
  sorry

lemma interp3_length4_aux5:
  assumes a0:"length xins = (4::nat)" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and
    a2:"Next reg' m' = (exec_instr (xins!0) 1 reg m)"
  shows "\<exists> reg2 m2. interp3 (butlast(tl xins)) (Next reg' m') = Next reg2 m2"
  sorry


lemma push_pop_subgoal_rr_aux1:
  assumes a0:"hd xins = Ppushl_r tmpreg" and 
          a1:"result = (exec_instr (hd xins) 1 reg m)" and
          a2:"tmpreg \<in> {x64Syntax.RDX, x64Syntax.RAX}"
        shows "result = Next reg' m' \<longrightarrow> storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) \<noteq> None"
  sorry

lemma push_pop_subgoal_rr_aux2_1:
  assumes a0:"xins = [Ppushl_r tmpreg, Ppopl tmpreg]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " and 
    a3:"tmpreg \<in> {x64Syntax.RDX, x64Syntax.RAX}"
  shows "reg'' (IR tmpreg) = reg (IR tmpreg)"
  sorry
(*proof -
  have b0:"Next reg' m' = exec_push 1 M32 m reg (reg (IR tmpreg))" using exec_instr_def by (simp add: a0 a1)
  have b1:"Next reg' m' =
    (case storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR tmpreg)) of None \<Rightarrow> Stuck
     | Some (x::64 word \<Rightarrow> 8 word option option) \<Rightarrow>
         Next
          ((undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg(IR SP := sub64 (reg (IR SP)) (vlong_of_memory_chunk M32))))
           (RIP := add64 (undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg(IR SP := sub64 (reg (IR SP)) (vlong_of_memory_chunk M32))) RIP) (Vlong ((1::64 word) + (1::64 word)))))
          x) " using b0 nextinstr_nf_def nextinstr_def exec_push_def by metis
  have b2_1:"(exec_instr (xins!0) 1 reg m) = Next reg' m' \<longrightarrow> storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR tmpreg)) \<noteq> None" using push_pop_subgoal_rr_aux1 a0 a1 
    by (metis b1 option.case(1) outcome.simps(3))
  have b2_2:"storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR tmpreg)) \<noteq> None" using b2_1 a1 by simp
  have b2:"storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR tmpreg))= Some m'" using b1 b2_2 by auto
  have b3:"reg' (IR SP) = sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)" using b1 b2 by auto
  let "?sp" = "reg' (IR SP)"
  have b4:"storev M32 m (reg' (IR SP)) (reg (IR tmpreg)) = Some m'" using b2 b3 by simp
  have c0:"Next reg'' m'' = exec_pop (1::64 word) M32 m' reg' (IR tmpreg)" using exec_instr_def by (simp add: a0 a2)
  have c2:"loadv M32 m' (reg' (IR SP)) = Some (reg (IR tmpreg))" using b4 store_load_consistency by simp
  let "?v" = " (reg (IR tmpreg))"
  have c3:" Next reg'' m'' =
    (case loadv M32 m' (reg' (IR SP)) of None \<Rightarrow> Stuck
     | Some (v::val) \<Rightarrow>
         Next
          ((undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg'(IR tmpreg := ?v, IR SP := add64 (reg' (IR SP)) (vlong_of_memory_chunk M32))))
           (RIP := add64 (undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg'(IR tmpreg := ?v, IR SP := add64 (reg' (IR SP)) (vlong_of_memory_chunk M32))) RIP) (Vlong ((1::64 word) + (1::64 word)))))
          m')" using nextinstr_nf_def nextinstr_def exec_pop_def c2 
    using c0 by force
  have c4:"reg''(IR tmpreg) = ?v" using exec_pop_def c2 c3 a3 by auto
  thus ?thesis using c4 by simp
qed
*)
lemma push_pop_subgoal_rr_aux2_2:
  assumes a0:"xins = [Ppushl_r tmpreg, Ppopl tmpreg]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and
    a2:"tmpreg \<in> {x64Syntax.RDX, x64Syntax.RAX}"
  shows "reg'' (IR tmpreg) = reg (IR tmpreg)"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 a2 push_pop_subgoal_rr_aux2_1 interp3_length2_aux2
    by metis
qed

lemma push_pop_subgoal_rr_aux2_3:
  assumes a0:"hd xins = Ppushl_r tmpreg" and 
          a1:"last xins = Ppopl tmpreg"and
          a2:"interp3 (butlast(tl xins)) (Next reg' m') = Next reg2 m'"and
          a3:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m') " and
          a5:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
          a6:"reg' (IR SP) =  reg2 (IR SP)" and
          a7:"tmpreg \<in> {x64Syntax.RDX, x64Syntax.RAX}"
  shows "reg'' (IR tmpreg) = reg (IR tmpreg)"
  sorry


lemma div_subgoal_rr_aux1:"
    bins = BPF_ALU64 BPF_DIV dst (SOReg src) \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
    \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(unfold eval_alu64_def,simp)
  apply(cases is_v1,simp_all)
  apply (unfold eval_alu64_aux1_def Let_def, simp_all)
  apply(split if_splits, simp_all)
  done

lemma  div_subgoal_rr_aux2_1:"xins = Ppushl_r x64Syntax.RDX \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r. r \<notin> {x64Syntax.RDX, x64Syntax.RSP} \<longrightarrow> reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold exec_push_def Let_def)
  apply(cases "storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RDX))",simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def, simp_all)
  done

lemma  div_subgoal_rr_aux2_2:"xins = Pxorq_rr (x64Syntax.RDX) (x64Syntax.RDX) \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r. r \<notin> {x64Syntax.RDX, x64Syntax.RSP} \<longrightarrow> reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(cases "storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RDX))")
  apply(unfold nextinstr_nf_def nextinstr_def xor64_def,simp_all)
  done

lemma  div_subgoal_rr_aux2_3:"xins = Pdivq_r (bpf_to_x64_reg src) \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r. (bpf_to_x64_reg r) \<notin> {x64Syntax.RAX, x64Syntax.RDX} \<longrightarrow> reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold divmod64u_def Let_def)
  apply(cases "reg (IR ireg.RDX)",simp_all)
  subgoal for x5 apply(cases "reg (IR ireg.RAX)",simp_all)
    apply(cases "reg (IR (bpf_to_x64_reg src))",simp_all)
    apply(split if_splits,simp_all)
    subgoal for x5aa apply(unfold nextinstr_nf_def nextinstr_def) by simp
    done
  done

lemma  div_subgoal_rr_aux2_4:"xins = Ppopl x64Syntax.RDX \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r. r  \<notin> {x64Syntax.RDX, x64Syntax.RSP} \<longrightarrow> reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold exec_pop_def Let_def)
  apply(cases "loadv M32 m (reg (IR SP))",simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def, simp_all)
  done

lemma  div_subgoal_rr_aux3_1:"xins = Pxorq_rr (x64Syntax.RDX) (x64Syntax.RDX) \<Longrightarrow> 
   Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> m'' = m "
  apply(unfold exec_instr_def) by simp


lemma  div_subgoal_rr_aux3_2:"xins = Pdivq_r (bpf_to_x64_reg src) \<Longrightarrow> 
   Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> m'' = m "
  apply(unfold exec_instr_def)
  apply(cases xins, simp_all)
  apply(unfold divmod64u_def Let_def)
  apply(cases "reg (IR ireg.RDX)",simp_all)
  subgoal for x5 apply(cases "reg (IR ireg.RAX)",simp_all)
    apply(cases "reg (IR (bpf_to_x64_reg src))",simp_all)
    apply(split if_splits,simp_all)
    done
  done

lemma div_subgoal_rr_aux3_3:
  assumes a0:"xins = [Pxorq_rr (x64Syntax.RDX) (x64Syntax.RDX),Pdivq_r (bpf_to_x64_reg src)]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " 
  shows " m'' = m"
  using div_subgoal_rr_aux3_1 div_subgoal_rr_aux3_2 
  by (metis One_nat_def a0 a1 a2 nth_Cons_0 nth_Cons_Suc)

lemma div_subgoal_rr_aux3:
  assumes a0:"xins = [Pxorq_rr (x64Syntax.RDX) (x64Syntax.RDX),Pdivq_r (bpf_to_x64_reg src)]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " 
  shows " m'' = m"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 div_subgoal_rr_aux3_3 
    by (meson interp3_length2_aux2)
qed

lemma reg_rsp_consist:"r = (bpf_to_x64_reg dst) \<Longrightarrow> r \<noteq> x64Syntax.RSP"
  apply(cases dst) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)

lemma div_subgoal_rr_aux4_1:"xins = Pxorq_rr (x64Syntax.RDX) (x64Syntax.RDX) \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> reg'' (IR SP) = reg (IR SP) "
  apply(unfold exec_instr_def reg_rsp_consist bpf_to_x64_reg_corr) 
  apply(unfold nextinstr_def nextinstr_def reg_rsp_consist add64_def)
  apply(cases xins,simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def xor64_def add64_def)
  apply(cases "reg (IR ireg.RDX)",simp_all)
  done

lemma div_subgoal_rr_aux4_2:"xins = Pdivq_r (bpf_to_x64_reg src) \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> reg'' (IR SP) = reg (IR SP) "
  apply(unfold exec_instr_def reg_rsp_consist bpf_to_x64_reg_corr) 
  apply(cases xins, simp_all)
  apply(unfold divmod64u_def Let_def)
  apply(cases "reg (IR ireg.RDX)",simp_all)
  subgoal for x5 apply(cases "reg (IR ireg.RAX)",simp_all)
    apply(cases "reg (IR (bpf_to_x64_reg src))",simp_all)
    apply(split if_splits,simp_all)
    subgoal for x5aa apply(unfold nextinstr_nf_def nextinstr_def) by simp
    done
  done

lemma div_subgoal_rr_aux4_3:
  assumes a0:"xins = [Pxorq_rr (x64Syntax.RDX) (x64Syntax.RDX),Pdivq_r (bpf_to_x64_reg src)]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " 
  shows " reg'' (IR SP) = reg (IR SP) "
  using div_subgoal_rr_aux4_2 div_subgoal_rr_aux4_1 reg_rsp_consist
  by (metis One_nat_def a0 a1 a2 nth_Cons_0 nth_Cons_Suc)

lemma div_subgoal_rr_aux4:
  assumes a0:"xins = [Pxorq_rr (x64Syntax.RDX) (x64Syntax.RDX),Pdivq_r (bpf_to_x64_reg src)]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " 
  shows "reg'' (IR SP) = reg (IR SP)"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 div_subgoal_rr_aux4_3
    by (meson interp3_length2_aux2)
qed

lemma div_subgoal_rr_aux5:
  assumes a0:"xins = [Ppushl_r tmpreg, Pxorq_rr tmpreg tmpreg,Pdivq_r (bpf_to_x64_reg src),Ppopl tmpreg]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and 
    a2:"tmpreg = x64Syntax.RDX"
  shows "reg'' (IR tmpreg) = reg (IR tmpreg)"
proof-
  have a3:"hd xins = Ppushl_r tmpreg" using a0 by simp
  have a4:"last xins = Ppopl tmpreg" using a0 by simp
  have b0:"(butlast(tl xins)) = [Pxorq_rr tmpreg tmpreg,Pdivq_r (bpf_to_x64_reg src)]" using a0 by simp
  let ?midlist = "[ Pxorq_rr tmpreg tmpreg,Pdivq_r (bpf_to_x64_reg src)]"
  have b1:"\<exists> reg' m'. Next reg' m' = exec_push 1 M32 m reg (reg (IR tmpreg))" using exec_instr_def a0 
    using a1 exec_push_def a0 sorry
    (*by (smt (verit, del_insts) instruction.simps(6295) interp3.simps(2) option.case_eq_if outcome.case(2) outcome.simps(4))*)
  then obtain reg' m' where b0:"Next reg' m' = exec_push 1 M32 m reg (reg (IR tmpreg))" by blast
  have b2_0:"length xins = 4" using a0 by simp
  have b2_1: "Next reg' m' = (exec_instr (xins!0) 1 reg m)" 
    by (simp add: a0 b0 exec_instr_def)
  have b2:"\<exists> reg2 m2. interp3 ?midlist (Next reg' m') = Next reg2 m2" using interp3_length4_aux5 b1 a0 a1 b2_0 b0 b2_1 by fastforce
  then obtain reg2 m2 where b3:"interp3 ?midlist (Next reg' m') = Next reg2 m2" by auto
  have b4:"m2 = m'" using div_subgoal_rr_aux3 a2 by (metis b3)
  have b5:"reg' (IR SP) =  reg2 (IR SP)" using div_subgoal_rr_aux4 a2 b3 by metis
  have b6:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " using a0 by (simp add: b0 exec_instr_def)
  have b7_1:"length xins \<ge> (2::nat)" using a0 by simp
  have b7_2:"Next reg2 m2 = interp3 (butlast xins) (Next reg m)" using b3 b0 a0 by (simp add: b6)
  have b7:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m2)" using interp3_length4_aux4 b2_0 b7_1 b7_2 (*by (metis a1 outcome.inject)*)sorry
  have b8:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m')" using b7 b4 by simp
  thus ?thesis using a3 a4 b4 b5 b6 b8 a1 push_pop_subgoal_rr_aux2_3
    by (metis a0 b3 butlast.simps(2) list.distinct(1) list.sel(3))
qed

lemma div_subgoal_rr_aux6:
  assumes a0:"xins = [Ppushl_r tmpreg, Pxorq_rr tmpreg tmpreg,Pdivq_r (bpf_to_x64_reg src),Ppopl tmpreg]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and
    a3:"tmpreg = x64Syntax.RDX"
  shows "\<forall> r . bpf_to_x64_reg r \<notin> {x64Syntax.RAX, x64Syntax.RDX, x64Syntax.RSP} \<longrightarrow> reg'' (IR (bpf_to_x64_reg r )) = reg (IR (bpf_to_x64_reg r ))"
proof-
  have b0_0:"length xins = 4" using a0 by simp
  have b0_1:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (xins!0) 1 reg m)" using exec_instr_def a0
    by (metis a1 interp3_list_aux1 list.distinct(1) outcome.exhaust)
  have b0_2:"length xins >0" using a0 by simp
  have b0_3:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = interp3 (tl xins) (Next reg1 m1) " 
       using a1 by (metis b0_1 b0_2 interp3.elims length_greater_0_conv list.sel(3) nth_Cons_0 outcome.case(1))
  then obtain reg1 m1 where b0_4:" Next reg1 m1 = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = interp3 (tl xins) (Next reg1 m1)" by auto
  have b0:"\<forall> r . r \<notin> {x64Syntax.RDX, x64Syntax.RSP} \<longrightarrow> reg1 (IR r) = reg (IR r)" using a0 b0_2 div_subgoal_rr_aux2_1
    using b0_4 nth_Cons_0 a3 by auto
  have b1_1:"\<exists> reg2 m2. Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1)" using exec_instr_def a0 by simp
  then obtain reg2 m2 where b1_2:"Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1)" using b1_1 by auto
  have b1_3:"take 2 xins = [xins!0]@[xins!1]" by (simp add: a0 numeral_2_eq_2 take_Suc_conv_app_nth)
  have b1_4:"Next reg2 m2 = interp3 (take 2 xins) (Next reg m)" using a0 b1_2 b1_3 b0_4
    by (metis append_Cons append_Nil interp3.simps(2) interp3_list_aux3 outcome.case(1))
  have b1_5:" Next reg2 m2 = interp3 (take 2 xins) (Next reg m) \<and> Next reg'' m'' = interp3 (drop 2 xins) (Next reg2 m2)" using interp3_length4_aux4 b0_0 a1 b1_4 by metis
  have b1:"\<forall> r . r \<notin> {x64Syntax.RDX, x64Syntax.RSP} \<longrightarrow> reg1 (IR r) = reg2 (IR r)" using a0 b1_2 a3
    by (metis One_nat_def insertCI nth_Cons_0 nth_Cons_Suc div_subgoal_rr_aux2_2)
  have b2_1:"\<exists> reg3 m3. Next reg3 m3 = (exec_instr (xins!2) 1 reg2 m2)" 
    using a0 a3 a1 exec_instr_def 
    by (smt (verit) Cons_nth_drop_Suc One_nat_def add.right_neutral add_Suc_right b0_0 b0_2 b1_5 drop0 interp3_length2_aux1 list.sel(3) list.size(3) list.size(4) nth_Cons_Suc numeral_2_eq_2 one_less_numeral_iff semiring_norm(76))
  then obtain reg3 m3 where b2_2:"Next reg3 m3 = (exec_instr (xins!2) 1 reg2 m2)" using b1_1 by auto
  have b2_3:"take 3 xins = [xins!0]@[xins!1]@[xins!2]" using a0 
    by (simp add: One_nat_def Suc_1 add_One numeral_3_eq_3 numeral_nat(2) take_Suc_conv_app_nth)
  have b2_4:"Next reg3 m3 = interp3 (take 3 xins) (Next reg m)" using a0 b1_5 b2_3 b2_2
    using append_Cons append_Nil b0_4 b1_2 b1_4 interp3.simps(2) interp3_list_aux3 outcome.case(1) by metis
  have b2_5:"[xins!0]@[xins!1]@[xins!2]@[last xins] = xins" using append_butlast_last_id a0 by fastforce
  have b2_6:"(last xins) = (xins!3)" using a0 by (metis One_nat_def Suc_eq_plus1 Suc_numeral add_2_eq_Suc diff_Suc_1' last_conv_nth length_Suc_conv list.simps(3) list.size(3) list_consists_4 semiring_norm(5))
  have b2_7: "(butlast xins) = [xins!0]@[xins!1]@[xins!2]" using a0 b2_6 by simp
  have b2_8:"butlast xins = take 3 xins" using a0 b2_7 by simp
  have b2_9:"Next reg3 m3 = interp3 (butlast xins) (Next reg m) \<and> Next reg'' m'' = (exec_instr (last xins) 1 reg3 m3)" using a0 b2_4 b2_8 interp3_length4_aux4 b0_0 a1 sorry(* by (metis a1 outcome.inject)*)
  have b2_10:"Next reg3 m3 = interp3 (take 3 xins) (Next reg m) \<and> Next reg'' m'' = (exec_instr (last xins) 1 reg3 m3)" using b2_9 b2_8 by simp
  have b2:"\<forall> r . (bpf_to_x64_reg r) \<notin> {x64Syntax.RAX, x64Syntax.RDX} \<longrightarrow> reg3 (IR (bpf_to_x64_reg r)) = reg2 (IR (bpf_to_x64_reg r))" using a0 b1_2
    using b2_2 div_subgoal_rr_aux2_3 a3 a0 by simp
  hence b3_1:" \<exists> reg4 m4. Next reg4 m4 = (exec_instr (xins!3) 1 reg3 m3)" 
    using b2_6 b2_9 by auto
  then obtain reg4 m4 where b4:"Next reg4 m4 = (exec_instr (xins!3) 1 reg3 m3)" using b3_1 by auto
  have b3:"Next reg4 m4 = Next reg'' m''" using interp3_list_aux3
    by (simp add: b2_6 b2_9 b4)
  have b4:"\<forall> r . bpf_to_x64_reg r \<notin> {x64Syntax.RDX, x64Syntax.RSP} \<longrightarrow> reg3 (IR (bpf_to_x64_reg r )) = reg'' (IR (bpf_to_x64_reg r ))" using a0 b0 b1 b2 div_subgoal_rr_aux2_4
    using append_Cons append_Nil b2_5 b2_9 list.sel(1) list.sel(3) by (metis a3)
  thus ?thesis using b0 b1 b2 by auto
qed

lemma div_subgoal_rr_aux7:
  assumes a0:"xins = [Ppushl_r tmpreg, Pxorq_rr tmpreg tmpreg,Pdivq_r (bpf_to_x64_reg src),Ppopl tmpreg] " and
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " and
    a2:"tmpreg = x64Syntax.RDX" and 
    a3: "(bpf_to_x64_reg dst) = x64Syntax.RAX"
  shows" \<forall> r \<noteq> dst. reg'' (IR  (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" 
proof-
  have b0:"reg'' (IR x64Syntax.RDX) = reg (IR x64Syntax.RDX)" using a0 a1 a2 div_subgoal_rr_aux5 by auto
  have b1:"\<forall> r . bpf_to_x64_reg r  \<notin> {x64Syntax.RAX, x64Syntax.RDX, x64Syntax.RSP} \<longrightarrow> reg'' (IR (bpf_to_x64_reg r )) = reg (IR (bpf_to_x64_reg r ))" using div_subgoal_rr_aux6 a0 a1 a2 by blast
  have b1_1:"\<forall> r. (bpf_to_x64_reg r) \<noteq> x64Syntax.RSP" using a0 reg_rsp_consist by simp
  have b2:"\<forall> r . bpf_to_x64_reg r  \<notin> {(bpf_to_x64_reg dst), x64Syntax.RDX, x64Syntax.RSP} \<longrightarrow> reg'' (IR (bpf_to_x64_reg r )) = reg (IR (bpf_to_x64_reg r ))" using b1 a3 by simp
  thus ?thesis using  b0 b2 b1_1 by force 
qed


lemma div_subgoal_rr_aux8_1:
  assumes a0:"xins = [Ppushl_r x64Syntax.RDX, Pxorq_rr x64Syntax.RDX x64Syntax.RDX,Pdivq_r (bpf_to_x64_reg src),Ppopl x64Syntax.RDX]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and
    a2:"Next reg1 m1 = exec_instr (xins!0) sz reg m " and
    a3:"Next reg2 m2 = exec_instr (xins!1) sz reg1 m1 " and
    a4:"Next reg3 m3 = exec_instr (xins!2) sz reg2 m2" and
    a5:"Next reg' m' = exec_instr xins2 1 tmpreg m" and
    a6:"xins2 = Pdivq_r (bpf_to_x64_reg src)" and
    a7:"tmpreg (IR x64Syntax.RAX) = reg (IR x64Syntax.RAX)" and
    a8:"tmpreg (IR x64Syntax.RDX) = Vlong 0"
  shows"reg' (IR x64Syntax.RAX) = reg3 (IR x64Syntax.RAX)"
  sorry
  (*shows " reg'' (IR x64Syntax.RAX) = reg3 (IR x64Syntax.RAX)"*)
(*proof-
  have b0_0:"length xins = 4" using a0 by simp
  have b0_1:"(xins!2) = xins2" using a0 a6 by simp
  have b0_2:"length xins >0" using a0 by simp
  have b0_3:"(xins!0) = Ppushl_r x64Syntax.RDX" using a0 by simp
  have b1:"reg1 (IR x64Syntax.RAX) = reg (IR x64Syntax.RAX)" using a0 b0_3 a2 div_subgoal_rr_aux2_1 nth_Cons_0 a3 sorry
  have b2:"reg1 (IR x64Syntax.RAX) = reg2 (IR x64Syntax.RAX)" using a0 b0_3 a2 div_subgoal_rr_aux2_1 nth_Cons_0 a3 sorry
  have b3:"reg2 (IR x64Syntax.RAX) = reg (IR x64Syntax.RAX)" using b1 b2 by simp
  have ""
  qed
*)

lemma div_subgoal_rr_aux8_3:
  assumes a0:"last xins = Pdivq_r (bpf_to_x64_reg src)"and
          a1:"interp3 (butlast xins) (Next reg m) = Next reg' m'"and
          a2:"Next reg'' m'' = (exec_instr (last xins) 1 reg' m') " and
          a3:"reg' (IR x64Syntax.RDX) = Vlong 0" and
          a4:"reg' (IR x64Syntax.RAX) =  reg (IR x64Syntax.RAX)" and
          a5:"Next tmpreg' m'' = exec_instr (last xins) 1 tmpreg m'" and
          a6: "tmpreg (IR x64Syntax.RDX) = Vlong 0" and
          a7:"tmpreg (IR x64Syntax.RAX) = reg (IR x64Syntax.RAX)"
        shows "reg'' (IR x64Syntax.RAX) = tmpreg' (IR x64Syntax.RAX)"
  sorry
(*proof-
  let ?midlist = "butlast(tl xins)"
  have b0_1:"xins = [Ppushl_r x64Syntax.RCX]@?midlist@[Ppopl x64Syntax.RCX]" using a0 a1
    by (metis append_Cons append_Nil append_butlast_last_id hd_Nil_eq_last instruction.distinct(5787) last_ConsL last_tl list.collapse)
  have b0:"Next reg' m' = exec_push 1 M32 m reg (reg (IR x64Syntax.RCX))" using exec_instr_def a0 
    using exec_push_def a5 a0 
    by (smt (z3) a1 hd_Nil_eq_last hd_conv_nth instruction.distinct(5787) instruction.simps(6295))
  have b1:"Next reg' m' =
    (case storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) of None \<Rightarrow> Stuck
     | Some (x::64 word \<Rightarrow> 8 word option option) \<Rightarrow>
         Next
          ((undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg(IR SP := sub64 (reg (IR SP)) (vlong_of_memory_chunk M32))))
           (RIP := add64 (undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg(IR SP := sub64 (reg (IR SP)) (vlong_of_memory_chunk M32))) RIP) (Vlong ((1::64 word) + (1::64 word)))))
          x) " using b0 nextinstr_nf_def nextinstr_def exec_push_def by metis
  have b2_1:"(exec_instr (xins!0) 1 reg m) = Next reg' m' \<longrightarrow> storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) \<noteq> None" using push_pop_subgoal_rr_aux1 a0 a1 
    by (metis b1 option.case(1) outcome.simps(3))
  have b2_2:"storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) \<noteq> None" using b2_1 a5 by simp
  have b2:"storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX))= Some m'" using b1 b2_2 by auto
  have b3:"reg' (IR SP) = sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)" using b1 b2 by auto
  let "?sp" = "reg' (IR SP)"
  have b4:"storev M32 m (reg' (IR SP)) (reg (IR ireg.RCX)) = Some m'" using b2 b3 by simp
  have b5:"interp3 (butlast(xins)) (Next reg m) = Next reg2 m'" using a2 a5 b0_1 a0
    by (metis append_Cons append_Nil butlast.simps(1) butlast.simps(2) interp3.simps(2) list.sel(3) list.simps(3) nth_Cons_0 outcome.case(1))
  have b6:"(exec_instr (last xins) 1 reg2 m') = Next reg'' m''" using a5 a1 a2 a3 b5 by simp
  have c0:"Next reg'' m'' = exec_pop (1::64 word) M32 m' reg2 (IR ireg.RCX)" using exec_instr_def using b6 a1 by simp
  have c1:"loadv M32 m' (reg' (IR SP)) = Some (reg (IR ireg.RCX))" using b4 store_load_consistency by simp
  have c2:"loadv M32 m' (reg2 (IR SP)) = Some (reg (IR ireg.RCX))" using b4 c1 a6 by simp
  let "?v" = " (reg (IR ireg.RCX))"
  have c3:" Next reg'' m'' =
    (case loadv M32 m' (reg2 (IR SP)) of None \<Rightarrow> Stuck
     | Some (v::val) \<Rightarrow>
         Next
          ((undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg2(IR ireg.RCX := ?v, IR SP := add64 (reg2 (IR SP)) (vlong_of_memory_chunk M32))))
           (RIP := add64 (undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg2(IR ireg.RCX := ?v, IR SP := add64 (reg2 (IR SP)) (vlong_of_memory_chunk M32))) RIP) (Vlong ((1::64 word) + (1::64 word)))))
          m')" using nextinstr_nf_def nextinstr_def exec_pop_def 
    using c0 c2 by simp
  have c4:"reg''(IR ireg.RCX) = ?v" using exec_pop_def c2 c3 by simp
  thus ?thesis using c4 by simp
qed
*)

lemma div_subgoal_rr_aux8_2:
  assumes a0:"xins = [Ppushl_r x64Syntax.RDX, Pxorq_rr x64Syntax.RDX x64Syntax.RDX,Pdivq_r (bpf_to_x64_reg src),Ppopl x64Syntax.RDX]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and
    a2:"Next reg' m' = exec_instr xins2 1 reg m" and
    a3:"xins2 = Pdivq_r (bpf_to_x64_reg src)" and
    a4:"reg (IR x64Syntax.RDX)  = Vlong 0"
  shows "reg' (IR x64Syntax.RAX) = reg'' (IR x64Syntax.RAX) "
proof-
  have b0_0:"length xins = 4" using a0 by simp
  have b0_1:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (xins!0) 1 reg m)" using exec_instr_def a0
    by (metis a1 interp3_list_aux1 list.distinct(1) outcome.exhaust)
  have b0_2:"length xins >0" using a0 by simp
  have b0_3:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = interp3 (tl xins) (Next reg1 m1) " 
       using a1 by (metis b0_1 b0_2 interp3.elims length_greater_0_conv list.sel(3) nth_Cons_0 outcome.case(1))
  then obtain reg1 m1 where b0_4:" Next reg1 m1 = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = interp3 (tl xins) (Next reg1 m1)" by auto
  have b0:"reg1 (IR x64Syntax.RAX) = reg (IR x64Syntax.RAX)" using a0 b0_2 div_subgoal_rr_aux2_1
    using b0_4 nth_Cons_0 a3 by auto
  have b1_1:"\<exists> reg2 m2. Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1)" using exec_instr_def a0 by simp
  then obtain reg2 m2 where b1_2:"Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1)" using b1_1 by auto
  have b1_3:"take 2 xins = [xins!0]@[xins!1]" by (simp add: a0 numeral_2_eq_2 take_Suc_conv_app_nth)
  have b1_4:"Next reg2 m2 = interp3 (take 2 xins) (Next reg m)" using a0 b1_2 b1_3 b0_4
    by (metis append_Cons append_Nil interp3.simps(2) interp3_list_aux3 outcome.case(1))
  have b1_5:" Next reg2 m2 = interp3 (take 2 xins) (Next reg m) \<and> Next reg'' m'' = interp3 (drop 2 xins) (Next reg2 m2)" using interp3_length4_aux4 b0_0 a1 b1_4 by metis
  have b1:"reg2 (IR x64Syntax.RAX) = reg1 (IR x64Syntax.RAX)" using a0 b1_2 
    using One_nat_def insertCI nth_Cons_0 nth_Cons_Suc div_subgoal_rr_aux2_2
    by (metis insert_absorb insert_iff insert_not_empty ireg.distinct(13) ireg.distinct(5))
  have b2_1:"\<exists> reg3 m3. Next reg3 m3 = (exec_instr (xins!2) 1 reg2 m2)" 
    using a0 a3 a1 exec_instr_def sorry
    (*by (smt (verit) Cons_nth_drop_Suc One_nat_def add.right_neutral add_Suc_right b0_0 b0_2 b1_5 drop0 interp3_length2_aux1 list.sel(3) list.size(3) list.size(4) nth_Cons_Suc numeral_2_eq_2 one_less_numeral_iff semiring_norm(76))*)
  then obtain reg3 m3 where b2_2:"Next reg3 m3 = (exec_instr (xins!2) 1 reg2 m2)" using b1_1 by auto
  have b2_3:"take 3 xins = [xins!0]@[xins!1]@[xins!2]" using a0 
    by (simp add: One_nat_def Suc_1 add_One numeral_3_eq_3 numeral_nat(2) take_Suc_conv_app_nth)
  have b2_4:"Next reg3 m3 = interp3 (take 3 xins) (Next reg m)" using a0 b1_5 b2_3 b2_2
    using append_Cons append_Nil b0_4 b1_2 b1_4 interp3.simps(2) interp3_list_aux3 outcome.case(1) by metis
  have b2_5:"[xins!0]@[xins!1]@[xins!2]@[last xins] = xins" using append_butlast_last_id a0 by fastforce
  have b2_6:"(last xins) = (xins!3)" using a0 by (metis One_nat_def Suc_eq_plus1 Suc_numeral add_2_eq_Suc diff_Suc_1' last_conv_nth length_Suc_conv list.simps(3) list.size(3) list_consists_4 semiring_norm(5))
  have b2_7: "(butlast xins) = [xins!0]@[xins!1]@[xins!2]" using a0 b2_6 by simp
  have b2_8:"butlast xins = take 3 xins" using a0 b2_7 by simp
  have b2_9:"Next reg3 m3 = interp3 (butlast xins) (Next reg m) \<and> Next reg'' m'' = (exec_instr (last xins) 1 reg3 m3)" using a0 b2_4 b2_8 interp3_length4_aux4 b0_0 a1 sorry(* by (metis a1 outcome.inject)*)
  have b2_10:"Next reg3 m3 = interp3 (take 3 xins) (Next reg m) \<and> Next reg'' m'' = (exec_instr (last xins) 1 reg3 m3)" using b2_9 b2_8 by simp
  let ?tmprax = "reg3 (IR x64Syntax.RAX)"
  have b3_1:" \<exists> reg4 m4. Next reg4 m4 = (exec_instr (xins!3) 1 reg3 m3)" 
    using b2_6 b2_9 by auto
  then obtain reg4 m4 where b3_2:"Next reg4 m4 = (exec_instr (xins!3) 1 reg3 m3)" using b3_1 by auto
  have b3:"Next reg4 m4 = Next reg'' m''" using interp3_list_aux3
    by (simp add: b2_6 b2_9 b3_2)
  have b4_1:"(xins!3) = Ppopl x64Syntax.RDX" using a0 by simp
  have b4_2:"reg4 (IR x64Syntax.RAX) = reg3 (IR x64Syntax.RAX)" using a0 b0 b1 div_subgoal_rr_aux2_4 a0 b3_2 b4_1
    using insert_absorb insert_iff insert_not_empty ireg.distinct(13) ireg.distinct(5) by simp   
  have b4:"reg'' (IR x64Syntax.RAX) = reg3 (IR x64Syntax.RAX)" using b4_2 b3 by simp
  have b5_1:"reg2 (IR x64Syntax.RAX) = reg (IR x64Syntax.RAX)" using b1 b0 by simp
  (*have b5_2:"reg2 (IR x64Syntax.RDX) = Vlong 0" should be proved*)
  have b5:" reg' (IR x64Syntax.RAX) = reg3 (IR x64Syntax.RAX)" using b5_1 a0 a1 a3 a2 div_subgoal_rr_aux8_1 b0_1 b1_2 b2_2 using b0_4 a4 by blast
  thus ?thesis using b5 b4 by auto
qed


(*lemma div_subgoal_rr_aux3_1:
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
*)

(*value" divmod64u (Vlong 0) (Vlong 4) (Vlong 3)"

lemma "xins = Pdivq_r ri \<Longrightarrow> result = exec_instr xins sz reg m \<Longrightarrow> 
  reg (IR x64Syntax.RAX) = Vlong n2 \<Longrightarrow> reg (IR x64Syntax.RDX) = Vlong 0 \<Longrightarrow> reg (IR ri) = Vlong n1 \<Longrightarrow> 
  (ucast(n1+n2)::128 word) \<le> ucast u64_MAX \<Longrightarrow> result \<noteq> Stuck"
  apply(unfold exec_instr_def)
  apply(cases "xins",simp_all)
  apply(unfold eval_alu64_def eval_alu64_aux1_def divmod64u_def Let_def,simp_all)
  done
*)

lemma ucast_for_div:"(x::u64) div (y::u64) = ucast(((ucast x)::u128) div ((ucast y)::u128))"
  sorry

lemma div_subgoal_rr_aux100_1:
    "bins = BPF_ALU64 BPF_DIV dst (SOReg src) \<Longrightarrow> 
    xins = Pdivq_r ri \<Longrightarrow>
    (BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow> 
    Next reg' m' = exec_instr xins 1 reg m \<Longrightarrow>
    x64Syntax.RAX = (bpf_to_x64_reg dst) \<Longrightarrow> 
    ri = (bpf_to_x64_reg src) \<Longrightarrow> 
    reg (IR x64Syntax.RAX) = Vlong n1 \<Longrightarrow> 
    reg (IR ri) = Vlong n2 \<Longrightarrow> 
    n1 = rs dst \<Longrightarrow> 
    n2  = rs src \<Longrightarrow> 
    n2 \<noteq> 0 \<Longrightarrow> 
    reg (IR x64Syntax.RDX) = Vlong 0 \<Longrightarrow>
    Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
(*(ucast(n1+n2)::128 word) \<le> ucast u64_MAX \<Longrightarrow>*)
  apply(unfold exec_instr_def)
  apply(cases xins, simp_all)
  subgoal for x31a apply(cases "is_v1",simp_all)
     apply(unfold eval_alu64_def eval_alu64_aux1_def Let_def eval_reg_def,simp_all)
    apply(unfold divmod64u_def Let_def, simp_all)
    apply(simp add:nextinstr_nf_def nextinstr_def add64_def )
    apply(cases "reg RIP",simp_all)
    using ucast_for_div apply blast
    subgoal for x2 using ucast_for_div apply blast
      done
    subgoal for x3 using ucast_for_div apply blast
      done
    subgoal for x4 using ucast_for_div apply blast
      done
    subgoal for x5 using ucast_for_div apply blast
      done
  done
  done

lemma div_subgoal_rr_aux100_2:
    "bins = BPF_ALU64 BPF_DIV dst (SOReg src) \<Longrightarrow> 
    xins = Pdivq_r ri \<Longrightarrow>
    (BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow> 
    Next reg' m' = exec_instr xins 1 reg m \<Longrightarrow>
    x64Syntax.RAX = (bpf_to_x64_reg dst) \<Longrightarrow> 
    ri = (bpf_to_x64_reg src) \<Longrightarrow> 
    reg (IR x64Syntax.RAX) = Vlong n1 \<Longrightarrow> 
    reg (IR ri) = Vlong n2 \<Longrightarrow> 
    n1 = rs dst \<Longrightarrow> 
    n2  = rs src \<Longrightarrow> 
    n2 = 0 \<Longrightarrow> 
    reg (IR x64Syntax.RDX) = Vlong 0 \<Longrightarrow>
    Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
(*(ucast(n1+n2)::128 word) \<le> ucast u64_MAX \<Longrightarrow>*)
  apply(unfold exec_instr_def)
  apply(cases xins, simp_all)
  subgoal for x31a apply(cases "is_v1",simp_all)
     apply(unfold eval_alu64_def eval_alu64_aux1_def Let_def eval_reg_def,simp_all)
    done
  done

lemma div_subgoal_rr_aux100_3:
    "bins = BPF_ALU64 BPF_DIV dst (SOReg src) \<Longrightarrow> 
    (BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow> 
    Next reg' m' = exec_instr (Pdivq_r (bpf_to_x64_reg src)) 1 reg m \<Longrightarrow>
    x64Syntax.RAX = (bpf_to_x64_reg dst) \<Longrightarrow> 
    reg (IR x64Syntax.RAX) = Vlong n1 \<Longrightarrow> 
    reg (IR (bpf_to_x64_reg src)) = Vlong n2 \<Longrightarrow> 
    n1 = rs dst \<Longrightarrow> 
    n2  = rs src \<Longrightarrow> 
    reg (IR x64Syntax.RDX) = Vlong 0 \<Longrightarrow>
    Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
(*(ucast(n1+n2)::128 word) \<le> ucast u64_MAX \<Longrightarrow>*)
  using div_subgoal_rr_aux100_1 div_subgoal_rr_aux100_2 by metis

lemma reg_rax_rdx1:"(bpf_to_x64_reg dst) = x64Syntax.RAX \<longrightarrow> (bpf_to_x64_reg dst) \<noteq> x64Syntax.RDX" 
  apply(cases dst) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)


lemma div_subgoal_rr_aux100:
  assumes a0:"bins = BPF_ALU64 BPF_DIV dst (SOReg src)" and
     a1:"xins = [Ppushl_r x64Syntax.RDX, Pxorq_rr x64Syntax.RDX x64Syntax.RDX,Pdivq_r (bpf_to_x64_reg src),Ppopl x64Syntax.RDX]" and
     a2:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu " and
     a3:"Next reg' m' = interp3 xins (Next reg m)" and
     a4:"x64Syntax.RAX = (bpf_to_x64_reg dst)" and
     a6:"reg (IR x64Syntax.RAX) = Vlong n1" and
     a7:"reg (IR (bpf_to_x64_reg src)) = Vlong n2" and
     a8:"n1  = rs dst" and
     a9:"n2  = rs src" and
     a10:"reg (IR x64Syntax.RDX) = Vlong 0"
     shows "Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
proof-
  have b0_0:"length xins = 4 " using a1 by simp
  let ?xins2 = "(xins !2)"
  have b0:"?xins2 =Pdivq_r (bpf_to_x64_reg src)" using a1 by simp
  have b1_0:"\<exists> result. result = exec_instr ?xins2 1 reg m " using a1 exec_instr_def by simp
  then obtain result where b1_1:"result = exec_instr ?xins2 1 reg m" by auto
  have b1_2:"result  \<noteq> Stuck " using interp3_length4_aux0 a3 b0_0 by (metis b1_1)
  hence b1_3:"\<exists> tmpreg tmpm. result = Next tmpreg tmpm" using b1_2 b1_1 by (meson outcome.exhaust)
    then obtain tmpreg tmpm where b1:"Next tmpreg tmpm = exec_instr (Pdivq_r (bpf_to_x64_reg src)) 1 reg m" using b1_3 b1_1 b0 by auto
    have b2:"Vlong (rs' dst) = tmpreg (IR x64Syntax.RAX)" using div_subgoal_rr_aux100_3 using a0 b0 a2 a4 a6 a7 a8 a9 a10 b1 by simp
    have b3_0:"Vlong (rs' dst) = tmpreg (IR (x64Syntax.RAX))" using b2 a4 by simp
    have b3:"Vlong (rs' dst)  =  reg' (IR x64Syntax.RAX)" using div_subgoal_rr_aux8_2 b0 a3 b3_0 b1 a1 by metis
    thus ?thesis using a4 by simp
qed

lemma divq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_DIV dst (SOReg src)" and
       a1:"per_jit_div_and_mod_reg64 True dst src = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decodes (unat pc) l_bin = Some v" and
       a4:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
       a5:"Next reg' m' = interp3 xins (Next reg m) " and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" and
       a7:"(bpf_to_x64_reg dst) = x64Syntax.RAX" and
       a8:"xins = map snd v" and
       a9:"reg (IR x64Syntax.RDX) = Vlong 0"(*should be proved*)
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
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using b0 b1 b2 a0 a4 a5 a6 a7 div_subgoal_rr_aux100 a9 by simp
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 a7 div_subgoal_rr_aux7 by simp
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 div_subgoal_rr_aux1 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed



end