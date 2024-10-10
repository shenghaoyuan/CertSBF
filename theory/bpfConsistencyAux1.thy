theory bpfConsistencyAux1
  imports Main Interpreter x64Semantics 
  x64Assembler x64DecodeProof Mem JITCommType
begin

lemma push_pop_subgoal_rr_aux2_1:
  assumes a0:"xins = [Ppushl_r x64Syntax.RCX, Ppopl x64Syntax.RCX]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') "
  shows "reg'' (IR x64Syntax.RCX) = reg (IR x64Syntax.RCX)"
proof -
  have b0:"Next reg' m' = exec_push 1 M32 m reg (reg (IR x64Syntax.RCX))" using exec_instr_def by (simp add: a0 a1)
  have b1:"Next reg' m' =
    (case storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) of None \<Rightarrow> Stuck
     | Some (x::64 word \<Rightarrow> 8 word option option) \<Rightarrow>
         Next
          ((undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg(IR SP := sub64 (reg (IR SP)) (vlong_of_memory_chunk M32))))
           (RIP := add64 (undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg(IR SP := sub64 (reg (IR SP)) (vlong_of_memory_chunk M32))) RIP) (Vlong ((1::64 word) + (1::64 word)))))
          x) " using b0 nextinstr_nf_def nextinstr_def exec_push_def by metis
  have b2_1:"(exec_instr (xins!0) 1 reg m) = Next reg' m' \<longrightarrow> storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) \<noteq> None" using push_pop_subgoal_rr_aux1 a0 a1 
    by (metis b1 option.case(1) outcome.simps(3))
  have b2_2:"storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) \<noteq> None" using b2_1 a1 by simp
  have b2:"storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX))= Some m'" using b1 b2_2 by auto
  have b3:"reg' (IR SP) = sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)" using b1 b2 by auto
  let "?sp" = "reg' (IR SP)"
  have b4:"storev M32 m (reg' (IR SP)) (reg (IR ireg.RCX)) = Some m'" using b2 b3 by simp
  have c0:"Next reg'' m'' = exec_pop (1::64 word) M32 m' reg' (IR ireg.RCX)" using exec_instr_def by (simp add: a0 a2)
  have c2:"loadv M32 m' (reg' (IR SP)) = Some (reg (IR ireg.RCX))" using b4 store_load_consistency by simp
  let "?v" = " (reg (IR ireg.RCX))"
  have c3:" Next reg'' m'' =
    (case loadv M32 m' (reg' (IR SP)) of None \<Rightarrow> Stuck
     | Some (v::val) \<Rightarrow>
         Next
          ((undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg'(IR ireg.RCX := ?v, IR SP := add64 (reg' (IR SP)) (vlong_of_memory_chunk M32))))
           (RIP := add64 (undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg'(IR ireg.RCX := ?v, IR SP := add64 (reg' (IR SP)) (vlong_of_memory_chunk M32))) RIP) (Vlong ((1::64 word) + (1::64 word)))))
          m')" using nextinstr_nf_def nextinstr_def exec_pop_def c2 
    using c0 by force
  have c4:"reg''(IR ireg.RCX) = ?v" using exec_pop_def c2 c3 by auto
  thus ?thesis using c4 by simp
qed

lemma push_pop_subgoal_rr_aux2_2:
  assumes a0:"xins = [Ppushl_r x64Syntax.RCX, Ppopl x64Syntax.RCX]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" 
  shows "reg'' (IR x64Syntax.RCX) = reg (IR x64Syntax.RCX)"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 push_pop_subgoal_rr_aux2_1 interp3_length2_aux2
    by metis
qed

lemma push_pop_subgoal_rr_aux2_3:
  assumes a0:"hd xins = Ppushl_r x64Syntax.RCX" and 
          a1:"last xins = Ppopl x64Syntax.RCX"and
          a2:"interp3 (butlast(tl xins)) (Next reg' m') = Next reg2 m'"and
          a3:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m') " and
          a5:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
          a6:"reg' (IR SP) =  reg2 (IR SP)"
  shows "reg'' (IR x64Syntax.RCX) = reg (IR x64Syntax.RCX)"
proof-
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


lemma div_subgoal_rr_aux1:"
    bins = BPF_ALU64 BPF_DIV dst (SOReg src) \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
    \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(unfold eval_alu64_def,simp)
  apply(cases is_v1,simp_all)
  apply (unfold eval_alu64_aux1_def Let_def, simp_all)
  apply(split if_splits, simp_all)
  done


lemma div_subgoal_rr_aux3:
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

lemma div_subgoal_rr_aux3_1:
    "bins = BPF_ALU64 BPF_DIV dst (SOReg src) \<Longrightarrow> 
    xins = Pdivq_r ri \<Longrightarrow>
    (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow> 
    Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
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

lemma div_subgoal_rr_aux3_2:
    "bins = BPF_ALU64 BPF_DIV dst (SOReg src) \<Longrightarrow> 
    xins = Pdivq_r ri \<Longrightarrow>
    (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow> 
    Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
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

lemma div_subgoal_rr_aux3_3:
    "bins = BPF_ALU64 BPF_DIV dst (SOReg src) \<Longrightarrow> 
    xins = Pdivq_r ri \<Longrightarrow>
    (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow> 
    Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
    x64Syntax.RAX = (bpf_to_x64_reg dst) \<Longrightarrow> 
    ri = (bpf_to_x64_reg src) \<Longrightarrow> 
    reg (IR x64Syntax.RAX) = Vlong n1 \<Longrightarrow> 
    reg (IR ri) = Vlong n2 \<Longrightarrow> 
    n1 = rs dst \<Longrightarrow> 
    n2  = rs src \<Longrightarrow> 
    reg (IR x64Syntax.RDX) = Vlong 0 \<Longrightarrow>
    Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
(*(ucast(n1+n2)::128 word) \<le> ucast u64_MAX \<Longrightarrow>*)
  using div_subgoal_rr_aux3_1 div_subgoal_rr_aux3_2 by metis

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
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using div_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 a7 div_subgoal_rr_aux3_3 sorry
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 sorry
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 div_subgoal_rr_aux1 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed



end