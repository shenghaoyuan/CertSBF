theory bpfConsistencyAux
  imports Main Interpreter x64Semantics 
  x64Assembler x64DecodeProof
begin

(*lemma "bop = BPF_ADD \<Longrightarrow> xop = Paddl_rr \<Longrightarrow> *)

(*u8_of_ireg rd = ucast(bpf_ireg2u4 dst) \<Longrightarrow>
u8_of_ireg ri = ucast(bpf_ireg2u4 src) \<Longrightarrow>*)

definition bpf_to_x64_reg:: "bpf_ireg \<Rightarrow> ireg" where
"bpf_to_x64_reg br = (
  case br of
  BR0 \<Rightarrow> x64Syntax.RAX |
  BR1 \<Rightarrow> x64Syntax.RDI |
  BR2 \<Rightarrow> x64Syntax.RSI |
  BR3 \<Rightarrow> x64Syntax.RDX |
  BR4 \<Rightarrow> x64Syntax.RCX |
  BR5 \<Rightarrow> x64Syntax.R8 |
  BR6 \<Rightarrow> x64Syntax.RBX |
  BR7 \<Rightarrow> x64Syntax.R13 |
  BR8 \<Rightarrow> x64Syntax.R14 |
  BR9 \<Rightarrow> x64Syntax.R15 |
  BR10 \<Rightarrow> x64Syntax.RBP
)"

lemma addl_subgoal_rr:
      "bins = BPF_ALU BPF_ADD dst (SOReg src) \<Longrightarrow>
       xins = Paddl_rr rd ri \<Longrightarrow>
       (BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       corr_registers dst rd \<Longrightarrow>
       corr_registers src ri \<Longrightarrow>
       reg (IR rd) = Vint n1 \<Longrightarrow>
       reg (IR ri) = Vint n2 \<Longrightarrow>
       ucast n1 = rs (BR dst) \<Longrightarrow>
       ucast n2  = rs (BR src) \<Longrightarrow>
       reg' (IR rd) = Vint n3 \<Longrightarrow>
       ucast n3 = rs'(BR dst)"
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
       (BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       corr_registers dst rd \<Longrightarrow>
       imm = ucast (src) \<Longrightarrow>
       reg (IR rd) = Vint n1 \<Longrightarrow>
       ucast n1  = rs (BR dst) \<Longrightarrow>
       reg' (IR rd) = Vint n3 \<Longrightarrow>
       ucast n3 = rs'(BR dst)"
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
       (BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       corr_registers dst rd \<Longrightarrow>
       corr_registers src ri \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       reg (IR ri) = Vlong n2 \<Longrightarrow>
       n1  = rs (BR dst) \<Longrightarrow>
       n2  = rs (BR src) \<Longrightarrow>
       reg' (IR rd) = Vlong n3 \<Longrightarrow>
       ucast n3 = rs'(BR dst)"
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
  apply (cases "is_v1", simp_all)
  apply(cases "dst = BR10")
  apply auto[1]
  apply (cases "is_v1", simp_all)
  apply(cases "dst = BR10", simp_all)
  apply auto[1]
    (*ADD64, stack pointer*)
  sorry
 



(*
definition rel_reg :: "bpf_ireg => ireg => bool" where
"rel_reg br ir = " *)


(*
Inductive star (ge: genv): state -> trace -> state -> Prop :=
  | star_refl: forall s,
      star ge s E0 s
  | star_step: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      star ge s1 t s3.*)

inductive small_step ::"instruction list * outcome \<Rightarrow> instruction list * outcome \<Rightarrow> bool"(infix "\<rightarrow>" 55)
  where
    Seq1:"(l#ls,Stuck)\<rightarrow>(ls,Stuck)"|
    Seq2:"(l#ls,Next rs m)\<rightarrow>(ls,exec_instr l 0 rs m)"

inductive star::"('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl:"star r x x"|
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

abbreviation small_steps::"instruction list * outcome \<Rightarrow> instruction list * outcome \<Rightarrow> bool"(infix "\<rightarrow>*" 55)
  where "x \<rightarrow>* y == star small_step x y "

lemma "([Pmovl_rr rd r1],Stuck) \<rightarrow>* ([], Stuck) = True"
  by (meson Seq1 star.refl star.step)

lemma "([Psubq_rr rd r1], Next rs m) \<rightarrow>* ([], Stuck) = False"
  apply (meson Seq2 star.step) using exec_instr_def
  by (smt (verit) instruction.simps(6259) list.distinct(1) list.inject outcome.distinct(1) prod.inject small_step.simps star.simps)

fun exec_instrs :: "instruction list \<Rightarrow> outcome \<Rightarrow> outcome" where
"exec_instrs [] st = st" |
"exec_instrs (h#t) st = (
  case st of
  Stuck \<Rightarrow> Stuck |
  Next rs m \<Rightarrow>
  let st1 = exec_instr h 0 rs m in
    exec_instrs t st1
)" 

(**r 
definition per_jit_sub_reg64 :: "bpf_ireg => bpf_ireg => x64_bin"

per_jit_sub_reg64 dst src = bl \<Longrightarrow> (**r JIT + x64_encode *)
x64decode bl = Some (sz, xins) \<Longrightarrow>

*)


lemma subq_subgoal_rr_aux1:
      "bins = BPF_ALU64 BPF_SUB dst (SOReg src) \<Longrightarrow>
       xins = Psubq_rr rd ri \<Longrightarrow>
       (BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       rd = (bpf_to_x64_reg dst)\<Longrightarrow>
       ri = (bpf_to_x64_reg src) \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       reg (IR ri) = Vlong n2 \<Longrightarrow>
       n1  = rs (BR dst) \<Longrightarrow>
       n2  = rs (BR src) \<Longrightarrow>
       Vlong (rs' (BR dst)) = reg' (IR (bpf_to_x64_reg dst))"
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

lemma subq_subgoal_rr_aux2_1:"xins = Psubq_rr dst src \<Longrightarrow> Next reg' m' = exec_instr xins sz reg m \<Longrightarrow> \<forall> r \<noteq> dst . reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def, cases "xins", simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def) 
  by auto

lemma subq_subgoal_rr_aux2_2:"xins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow> Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
       \<forall> r \<noteq> bpf_to_x64_reg dst. reg' (IR r) = reg (IR r)"
  using subq_subgoal_rr_aux2_1 by blast

lemma subq_subgoal_rr_aux2_3:" r1 \<noteq> r2 \<longrightarrow> bpf_to_x64_reg r1 \<noteq> bpf_to_x64_reg r2 "
  apply(unfold bpf_to_x64_reg_def)
  apply(rule impI)
  apply(cases r1)
    apply(cases r2, simp_all)
           apply(cases r2, simp_all)
    apply(cases r2, simp_all)
         apply(cases r2, simp_all)
    apply(cases r2, simp_all)
       apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  done

lemma subq_subgoal_rr_aux2:"xins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow> Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
       \<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  using subq_subgoal_rr_aux2_3 subq_subgoal_rr_aux2_2 by metis


lemma subq_subgoal_rr_aux3:"bins = BPF_ALU64 BPF_SUB dst (SOReg src) \<Longrightarrow> (BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1 \<Longrightarrow>
       \<forall> r \<noteq> dst. rs' (BR r) = rs (BR r)"
  apply(cases "bins",simp_all)
  apply(unfold eval_alu64_def,simp)
  by (unfold eval_alu64_aux1_def, simp)


definition per_jit_sub_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> x64_bin option" where
"per_jit_sub_reg64 dst src = (
  let ins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    x64_encode ins
)"

lemma subq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_SUB dst (SOReg src)" and
       a1:"per_jit_sub_reg64 dst src = Some bl" and
       a2:"list_in_list bl pc l_bin" and
       a3:"x64_decode pc l_bin = Some (length l_bin, xins)" and
       a4:"(BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1" and
       a5:"Next reg' m'  = exec_instr xins sz reg m" and
       a6:"(\<forall> r. Vlong (rs (BR r)) = reg (IR (bpf_to_x64_reg r)))" 
  shows "(\<forall> r. Vlong (rs' (BR r)) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b0:"xins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using x64_encode_decode_consistency per_jit_sub_reg64_def a1 a2 a3 by fastforce
    moreover have b1:"Vlong (rs (BR dst)) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs (BR src)) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' (BR dst)) = reg' (IR (bpf_to_x64_reg dst))" using subq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 by force
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 subq_subgoal_rr_aux2 by simp
    have b5:"\<forall> r \<noteq> dst. Vlong (rs'(BR r)) = Vlong (rs (BR r))" using a0 a4 subq_subgoal_rr_aux3 by simp
    have b6:"\<forall> r \<noteq> dst. Vlong (rs (BR r)) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' (BR r)) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed

lemma subl_subgoal_ri:
      "bins = BPF_ALU BPF_SUB dst (SOImm src) \<Longrightarrow>
       xins = Psubl_ri rd imm \<Longrightarrow>
       (BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       corr_registers dst rd \<Longrightarrow>
       imm = ucast (src) \<Longrightarrow>
       reg (IR rd) = Vint n1 \<Longrightarrow>
       ucast n1  = rs (BR dst) \<Longrightarrow>
       reg' (IR rd) = Vint n3 \<Longrightarrow>
       ucast n3 = rs'(BR dst)"
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
  apply (cases "is_v1", simp_all)
  apply (cases "is_v1", simp_all)
  using cast_lemma2 
  sorry


lemma movq_subgoal_rr:
      "bins = BPF_ALU64 BPF_MOV dst (SOReg src) \<Longrightarrow>
       xins = Pmovq_rr rd ri \<Longrightarrow>
       (BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       corr_registers dst rd \<Longrightarrow>
       corr_registers src ri \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       reg (IR ri) = Vlong n2 \<Longrightarrow>
       n1  = rs (BR dst) \<Longrightarrow>
       n2  = rs (BR src) \<Longrightarrow>
       reg' (IR rd) = Vlong n3 \<Longrightarrow>
       ucast n3 = rs'(BR dst)"
(*memory_mapping bstate = m' \<and> (reg' (IR rd)) = Vlong (rs'(BR dst))"*)
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
       (BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1 \<Longrightarrow>
       Next reg' m' = exec_instr xins sz reg m \<Longrightarrow> 
       corr_registers dst rd \<Longrightarrow>
       imm = ucast (src) \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       ucast n1  = rs (BR dst) \<Longrightarrow>
       reg' (IR rd) = Vlong n3 \<Longrightarrow>
       ucast n3 = rs'(BR dst)"
  apply (unfold exec_instr_def step)
  apply simp
  apply (unfold eval_alu64_def)
  apply (cases BPF_MOV, simp_all)
  apply (unfold nextinstr_def)
  apply (erule conjE)
  apply (metis (no_types, lifting) option.case_eq_if option.discI option.sel rbpf_state.select_convs(2))
  apply(unfold eval_alu64_aux1_def add64_def) 
  by simp

end
