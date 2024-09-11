theory bpfConsistencyAux
  imports Main Interpreter x64Semantics 
begin

(*lemma "bop = BPF_ADD \<Longrightarrow> xop = Paddl_rr \<Longrightarrow> *)


definition corr_registers:: "bpf_ireg \<Rightarrow> ireg \<Rightarrow> bool" where
"corr_registers br ir = (let x = ucast(bpf_ireg2u4 br); y = u8_of_ireg ir in
  (if (x,y)\<in> {(1::u8,7),(0,0),(2,6),(3,2),(4,8),(5,3),(6,13),(7,14),(8,15),(9,5)} then True
  else False))"

(*u8_of_ireg rd = ucast(bpf_ireg2u4 dst) \<Longrightarrow>
u8_of_ireg ri = ucast(bpf_ireg2u4 src) \<Longrightarrow>*)

lemma addl_subgoal_rr:
      "bins = BPF_ALU BPF_ADD dst (SOReg src) \<Longrightarrow>
       xins = Paddl_rr rd ri \<Longrightarrow>
       Some bstate = step conf bins rs m ss l is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       corr_registers dst rd \<Longrightarrow>
       corr_registers src ri \<Longrightarrow>
       reg (IR rd) = Vint n1 \<Longrightarrow>
       reg (IR ri) = Vint n2 \<Longrightarrow>
       ucast n1 = rs (BR dst) \<Longrightarrow>
       ucast n2  = rs (BR src) \<Longrightarrow>
       reg' (IR rd) = Vint n3 \<Longrightarrow>
       memory_mapping bstate = m' \<and> ucast n3 = (registers bstate)(BR dst)"
  apply (unfold exec_instr_def step)
  apply simp
  apply (unfold eval_alu32_def)
  apply (cases BPF_ADD, simp_all)
  apply (unfold eval_alu32_aux1_def)
  apply (unfold Let_def)
  apply (cases BPF_ADD, simp_all)
  apply (unfold add64_def add32_def)
  apply (unfold nextinstr_nf_def nextinstr_def eval_reg_def)
  apply simp
  apply (unfold add64_def)
  apply (erule conjE)
  using cast_lemma1
  by metis


lemma addl_subgoal_ri:
      "bins = BPF_ALU BPF_ADD dst (SOImm src) \<Longrightarrow>
       xins = Paddl_ri rd imm \<Longrightarrow>
       Some bstate = step conf bins rs m ss l is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       corr_registers dst rd \<Longrightarrow>
       imm = ucast (src) \<Longrightarrow>
       reg (IR rd) = Vint n1 \<Longrightarrow>
       ucast n1  = rs (BR dst) \<Longrightarrow>
       reg' (IR rd) = Vint n3 \<Longrightarrow>
       memory_mapping bstate = m' \<and> ucast n3 = (registers bstate)(BR dst)"
  apply (unfold exec_instr_def step)
  apply simp
  apply (unfold eval_alu32_def)
  apply (cases BPF_ADD, simp_all)
  apply (unfold eval_alu32_aux1_def)
  apply (unfold Let_def)
  apply (cases BPF_ADD, simp_all)
  apply (unfold add64_def add32_def)
  apply (unfold nextinstr_nf_def nextinstr_def eval_reg_def)
  apply simp
  apply (unfold add64_def)
  apply (erule conjE)
  using cast_lemma2 
  by metis


lemma addq_subgoal_rr:
      "bins = BPF_ALU64 BPF_ADD dst (SOReg src) \<Longrightarrow>
       xins = Paddq_rr rd ri \<Longrightarrow>
       Some bstate = step conf bins rs m ss l is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       corr_registers dst rd \<Longrightarrow>
       corr_registers src ri \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       reg (IR ri) = Vlong n2 \<Longrightarrow>
       n1  = rs (BR dst) \<Longrightarrow>
       n2  = rs (BR src) \<Longrightarrow>
       reg' (IR rd) = Vlong n3 \<Longrightarrow>
       memory_mapping bstate = m' \<and> ucast n3 = (registers bstate)(BR dst)"
  apply (unfold exec_instr_def step)
  apply simp
  apply (unfold eval_alu64_def)
  apply (cases BPF_ADD, simp_all)
  apply (unfold eval_alu64_aux4_def)
  apply (unfold Let_def)
  apply (cases BPF_ADD, simp_all)
  apply (unfold add64_def)
  apply (unfold nextinstr_nf_def nextinstr_def eval_reg_def)
  apply simp
  apply (erule conjE)
  apply (rule conjI)
  apply (cases "is_v1", simp_all)
  apply(cases "dst = BR10")
  apply auto[1]
  apply auto[1]
  apply (cases "is_v1", simp_all)
  apply(cases "dst = BR10", simp_all)
  apply auto[1]
    (*ADD64, stack pointer*)
  sorry
 

lemma subq_subgoal_rr:
      "bins = BPF_ALU64 BPF_SUB dst (SOReg src) \<Longrightarrow>
       xins = Psubq_rr rd ri \<Longrightarrow>
       Some bstate = step conf bins rs m ss l is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       corr_registers dst rd \<Longrightarrow>
       corr_registers src ri \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       reg (IR ri) = Vlong n2 \<Longrightarrow>
       n1  = rs (BR dst) \<Longrightarrow>
       n2  = rs (BR src) \<Longrightarrow>
       reg' (IR rd) = Vlong n3 \<Longrightarrow>
       memory_mapping bstate = m' \<and> ucast n3 = (registers bstate)(BR dst)"
  apply (unfold exec_instr_def step)
  apply simp
  apply (unfold eval_alu64_def)
  apply (cases BPF_SUB, simp_all)
  apply (unfold eval_alu64_aux1_def)
  apply (unfold Let_def)
  apply (cases BPF_SUB, simp_all)
  apply (unfold sub64_def)
  apply (unfold nextinstr_nf_def nextinstr_def eval_reg_def)
  by simp

lemma subl_subgoal_ri:
      "bins = BPF_ALU BPF_SUB dst (SOImm src) \<Longrightarrow>
       xins = Psubl_ri rd imm \<Longrightarrow>
       Some bstate = step conf bins rs m ss l is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       corr_registers dst rd \<Longrightarrow>
       imm = ucast (src) \<Longrightarrow>
       reg (IR rd) = Vint n1 \<Longrightarrow>
       ucast n1  = rs (BR dst) \<Longrightarrow>
       reg' (IR rd) = Vint n3 \<Longrightarrow>
       memory_mapping bstate = m' \<and> ucast n3 = (registers bstate)(BR dst)"
  apply (unfold exec_instr_def step)
  apply simp
  apply (unfold eval_alu32_def)
  apply (cases BPF_SUB, simp_all)
  apply (unfold eval_alu32_aux1_def)
  apply (unfold Let_def)
  apply (cases BPF_SUB, simp_all)
  apply (unfold sub32_def )
  apply (unfold nextinstr_nf_def nextinstr_def eval_reg_def)
  apply simp
  apply (unfold add64_def)
  apply (erule conjE)
  apply (rule conjI)
  apply (cases "is_v1", simp_all)
  apply (cases "is_v1", simp_all)
  using cast_lemma2 
  sorry


lemma movq_subgoal_rr:
      "bins = BPF_ALU64 BPF_MOV dst (SOReg src) \<Longrightarrow>
       xins = Pmovq_rr rd ri \<Longrightarrow>
       Some bstate = step conf bins rs m ss l is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       corr_registers dst rd \<Longrightarrow>
       corr_registers src ri \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       reg (IR ri) = Vlong n2 \<Longrightarrow>
       n1  = rs (BR dst) \<Longrightarrow>
       n2  = rs (BR src) \<Longrightarrow>
       reg' (IR rd) = Vlong n3 \<Longrightarrow>
       memory_mapping bstate = m' \<and> ucast n3 = (registers bstate)(BR dst)"
(*memory_mapping bstate = m' \<and> (reg' (IR rd)) = Vlong ((registers bstate)(BR dst))"*)
  apply (unfold exec_instr_def step)
  apply simp
  apply (unfold eval_alu64_def)
  apply (unfold eval_alu64_aux1_def)
  apply (unfold Let_def)
  apply (unfold nextinstr_nf_def nextinstr_def eval_reg_def)
  by simp

lemma movq_subgoal_ri:
      "bins = BPF_ALU64 BPF_MOV dst (SOImm src) \<Longrightarrow>
       xins = Pmovq_ri rd imm \<Longrightarrow>
       Some bstate = step conf bins rs m ss l is_v1 \<Longrightarrow>
       Next reg' m' = exec_instr xins sz reg m \<Longrightarrow> 
       corr_registers dst rd \<Longrightarrow>
       imm = ucast (src) \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       ucast n1  = rs (BR dst) \<Longrightarrow>
       reg' (IR rd) = Vlong n3 \<Longrightarrow>
       memory_mapping bstate = m' \<and> ucast n3 = (registers bstate)(BR dst)"
  apply (unfold exec_instr_def step)
  apply simp
  apply (unfold eval_alu64_def)
  apply (cases BPF_MOV, simp_all)
  apply (unfold nextinstr_def)
  apply (erule conjE)
  apply (rule conjI)
  apply (metis (no_types, lifting) option.case_eq_if option.discI option.sel rbpf_state.select_convs(2))
  apply(unfold eval_alu64_aux1_def add64_def) 
  by simp

end
