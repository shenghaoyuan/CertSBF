theory bpfConsistencyAux
  imports Main Interpreter x64Semantics 
  x64Assembler x64DecodeProof Mem JITCommType
begin


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
(*
lemma hh1: assumes a0:" (xins, (Next reg m)) \<rightarrow>* ([], (Next reg'' m''))" and
  a1:"length xins \<ge> (2::nat)"
shows" \<exists> reg' m'. (xins, (Next reg m)) \<rightarrow>* (last xs, (Next reg' m')) \<and> (last xs, (Next reg' m')) \<rightarrow>* ([], (Next reg'' m''))  "
  apply(induction "xins")
   apply auto
apply(rule small_steps.induct)*)

(*
  BPF_DIV, BPF_MOD,  
  BPF_LSH, BPF_RSH,
  BPF_ARSH 
*)
section    \<open> BPF_ALU64 \<close> 
subsection    \<open> BPF_ALU64 auxs\<close> 

lemma aluq_subgoal_rr_aux1:
     "op1 \<in> {BPF_SUB, BPF_ADD, BPF_MOV, BPF_AND, BPF_XOR, BPF_OR} \<Longrightarrow>
     bins = BPF_ALU64 op1 dst (SOReg src) \<Longrightarrow>
     xins = (let op2 = (case op1 of 
        BPF_SUB \<Rightarrow> Psubq_rr | BPF_ADD \<Rightarrow> Paddq_rr | BPF_MOV \<Rightarrow> Pmovq_rr | BPF_AND \<Rightarrow> Pandq_rr | BPF_XOR \<Rightarrow> Pxorq_rr | 
        BPF_OR \<Rightarrow> Porq_rr ) in op2 rd ri) \<Longrightarrow>
     (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
     Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
     rd = (bpf_to_x64_reg dst) \<Longrightarrow>
     ri = (bpf_to_x64_reg src) \<Longrightarrow>
     reg (IR rd) = Vlong n1 \<Longrightarrow>
     reg (IR ri) = Vlong n2 \<Longrightarrow>
     n1  = rs dst \<Longrightarrow>
     n2  = rs src \<Longrightarrow> 
     Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
  apply (unfold exec_instr_def step)
  apply simp
  apply(cases op1,simp_all)
  apply (unfold eval_alu64_def eval_alu64_aux1_def eval_alu64_aux2_def Let_def)
  apply (unfold sub64_def add64_def and64_def xor64_def or64_def)
  apply (unfold nextinstr_nf_def nextinstr_def eval_reg_def)
  by simp_all

lemma aluq_subgoal_rr_aux2_1:"op1 \<in> {Psubq_rr, Pmovq_rr,Paddq_rr, Pandq_rr, Pxorq_rr, Porq_rr} \<Longrightarrow> 
    xins = op1 dst src \<Longrightarrow> Next reg' m' = exec_instr xins sz reg m \<Longrightarrow> 
    \<forall> r\<noteq>dst. reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def, cases "xins", simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def sub64_def and64_def xor64_def or64_def) 
  by auto

lemma aluq_subgoal_rr_aux2_2:"op1 \<in> {Psubq_rr, Pmovq_rr, Paddq_rr, Pandq_rr, Pxorq_rr, Porq_rr} \<Longrightarrow> 
    xins = op1 (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow> Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
    \<forall> r \<noteq> bpf_to_x64_reg dst. reg' (IR r) = reg (IR r)"
  using aluq_subgoal_rr_aux2_1 by blast

lemma aluq_subgoal_rr_aux2:"op1 \<in> {Psubq_rr, Pmovq_rr, Paddq_rr, Pandq_rr, Pxorq_rr, Porq_rr} \<Longrightarrow> xins = op1 (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow> Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
       \<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  using bpf_to_x64_reg_corr aluq_subgoal_rr_aux2_2 by metis

lemma aluq_subgoal_rr_aux3:"op2 \<in> {BPF_SUB, BPF_MOV, BPF_ADD, BPF_AND, BPF_XOR, BPF_OR} \<Longrightarrow>
    bins = BPF_ALU64 op2 dst (SOReg src) \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
    \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(cases op2)
  apply(unfold eval_alu64_def,simp)
  by (unfold eval_alu64_aux1_def, simp_all)

subsection   \<open> BPF_ALU64 ADD64\<close>  

lemma addq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_ADD dst (SOReg src)" and
       a1:"per_jit_add_reg64_1 dst src = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decode (unat pc) l_bin = Some (length l_bin, xins)" and
       a4:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
       a5:"Next reg' m'  = exec_instr xins sz reg m" and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" 
  shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b0:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using x64_encode_decode_consistency per_jit_add_reg64_1_def a1 a2 a3 by fastforce
    moreover have b1:"Vlong (rs dst) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using aluq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 by force
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 aluq_subgoal_rr_aux3 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed


subsection   \<open> BPF_ALU64 SUB64\<close> 

lemma subq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_SUB dst (SOReg src)" and
       a1:"per_jit_sub_reg64 dst src = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decode (unat pc) l_bin = Some (length l_bin, xins)" and
       a4:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
       a5:"Next reg' m'  = exec_instr xins sz reg m" and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" 
  shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b0:"xins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using x64_encode_decode_consistency per_jit_sub_reg64_def a1 a2 a3 by fastforce
    moreover have b1:"Vlong (rs dst) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using aluq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 by force
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 aluq_subgoal_rr_aux3 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed

subsection   \<open> BPF_ALU64 AND64\<close>

lemma andq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_AND dst (SOReg src)" and
       a1:"per_jit_and_reg64 dst src = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decode (unat pc) l_bin = Some (length l_bin, xins)" and
       a4:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
       a5:"Next reg' m'  = exec_instr xins sz reg m" and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" 
  shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b0:"xins = Pandq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using x64_encode_decode_consistency per_jit_and_reg64_def a1 a2 a3 by fastforce
    moreover have b1:"Vlong (rs dst) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using aluq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 by force
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 aluq_subgoal_rr_aux3 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed


subsection   \<open> BPF_ALU64 MOV64\<close>

lemma movq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_MOV dst (SOReg src)" and
       a1:"per_jit_mov_reg64 dst src = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decode (unat pc) l_bin = Some (length l_bin, xins)" and
       a4:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
       a5:"Next reg' m'  = exec_instr xins sz reg m" and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" 
  shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b0:"xins = Pmovq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using x64_encode_decode_consistency per_jit_mov_reg64_def a1 a2 a3 by fastforce
    moreover have b1:"Vlong (rs dst) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using aluq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 by force
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 aluq_subgoal_rr_aux3 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed


subsection   \<open> BPF_ALU64 XOR64\<close>

lemma xorq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_XOR dst (SOReg src)" and
       a1:"per_jit_xor_reg64 dst src = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decode (unat pc) l_bin = Some (length l_bin, xins)" and
       a4:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
       a5:"Next reg' m'  = exec_instr xins sz reg m" and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" 
  shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b0:"xins = Pxorq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using x64_encode_decode_consistency per_jit_xor_reg64_def a1 a2 a3 by fastforce
    moreover have b1:"Vlong (rs dst) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using aluq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 by force
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 aluq_subgoal_rr_aux3 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed

subsection   \<open> BPF_ALU64 OR64\<close> 

lemma orq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_OR dst (SOReg src)" and
       a1:"per_jit_or_reg64 dst src = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decode (unat pc) l_bin = Some (length l_bin, xins)" and
       a4:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
       a5:"Next reg' m'  = exec_instr xins sz reg m" and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" 
  shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b0:"xins = Porq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using x64_encode_decode_consistency per_jit_or_reg64_def a1 a2 a3 by fastforce
    moreover have b1:"Vlong (rs dst) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using aluq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 by force
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 aluq_subgoal_rr_aux3 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed



end
