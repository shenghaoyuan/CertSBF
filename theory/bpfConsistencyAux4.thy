theory bpfConsistencyAux4
  imports Main Interpreter x64Semantics 
  x64Assembler x64DecodeProof Mem JITCommType bpfConsistencyAux1 bpfConsistencyAux2
begin

lemma  mod_subgoal_rr_aux2_3:"xins = Pmodq_r (bpf_to_x64_reg src) \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r. (bpf_to_x64_reg r) \<notin> {x64Syntax.RAX, x64Syntax.RDX} \<longrightarrow> reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold divmod64u_def)
  apply(unfold Let_def )
  apply(cases "reg (IR ireg.RDX)",simp_all)
  subgoal for x5 apply(cases "reg (IR ireg.RAX)",simp_all)
    apply(cases "reg (IR (bpf_to_x64_reg src))",simp_all)
    apply(split if_splits,simp_all)
    subgoal for x5aa apply(unfold nextinstr_nf_def nextinstr_def) by simp
    done
  done





end