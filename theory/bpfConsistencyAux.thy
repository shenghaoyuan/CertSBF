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
  BPF_DIV, BPF_MOD,  
  BPF_LSH, BPF_RSH,
  BPF_ARSH 
*)

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

(*
lemma addq_subgoal_rr:
      "bins = BPF_ALU64 BPF_ADD dst (SOReg src) \<Longrightarrow>
       xins = Paddq_rr rd ri \<Longrightarrow>
       (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
       Next reg' m' = exec_instr xins sz reg m \<Longrightarrow> 
       rd = bpf_to_x64_reg dst \<Longrightarrow>
       ri = bpf_to_x64_reg src \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       reg (IR ri) = Vlong n2 \<Longrightarrow>
       n1  = rs dst \<Longrightarrow>
       n2  = rs src \<Longrightarrow>
       Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
  apply (unfold exec_instr_def step,simp_all)
  apply (unfold eval_alu64_def)
  apply (cases BPF_ADD, simp_all)
  apply (unfold add64_def eval_alu64_aux1_def Let_def)
  apply (cases BPF_ADD)
  apply (unfold nextinstr_nf_def nextinstr_def eval_reg_def)
  by simp_all

lemma addq_subgoal_rr_aux2_1:"xins = Paddq_rr dst src \<Longrightarrow> Next reg' m' = exec_instr xins sz reg m \<Longrightarrow> \<forall> r \<noteq> dst . reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def, cases "xins", simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def) 
  by auto

lemma addq_subgoal_rr_aux2_2:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow> Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
       \<forall> r \<noteq> bpf_to_x64_reg dst. reg' (IR r) = reg (IR r)"
  using addq_subgoal_rr_aux2_1 by blast

lemma addq_subgoal_rr_aux2:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow> Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
       \<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  using bpf_to_x64_reg_corr addq_subgoal_rr_aux2_2 by metis

lemma addq_subgoal_rr_aux3:"bins = BPF_ALU64 BPF_ADD dst (SOReg src) \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
       \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(unfold eval_alu64_def,simp)
  by (unfold eval_alu64_aux1_def, simp)

*)

subsubsection   \<open> BPF_ALU64 ADD64\<close>  

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


subsubsection   \<open> BPF_ALU64 SUB64\<close> 

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

subsubsection   \<open> BPF_ALU64 AND64\<close>

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

(*
lemma subq_subgoal_rr_aux1:
     "bins = BPF_ALU64 BPF_SUB dst (SOReg src) \<Longrightarrow>
     xins = Psubq_rr rd ri \<Longrightarrow>
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

lemma subq_subgoal_rr_aux2:"xins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow> Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
       \<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  using bpf_to_x64_reg_corr subq_subgoal_rr_aux2_2 by metis


lemma subq_subgoal_rr_aux3:"bins = BPF_ALU64 BPF_SUB dst (SOReg src) \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
       \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(unfold eval_alu64_def,simp)
  by (unfold eval_alu64_aux1_def, simp)
*)


subsubsection   \<open> BPF_ALU64 MOV64\<close>

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


subsubsection   \<open> BPF_ALU64 XOR64\<close>

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

subsubsection   \<open> BPF_ALU64 OR64\<close> 

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

  subsubsection   \<open> BPF_ALU64 SHL64\<close>


lemma add_sub_consistency:"add64 (Vlong a) (Vlong b) = Vlong c \<Longrightarrow> sub64 (Vlong c) (Vlong a) = (Vlong b) "
  using add64_def sub64_def by auto

(*lemma interp2_aux1:
  assumes a0:"length xins = (2::nat)" and 
          a1:"result = interp2 n xins (Next reg m)"
        shows "result = Next reg' m' \<longrightarrow> n\<ge>2"
proof (rule ccontr)
  assume a2:"\<not> (result = Next reg' m' \<longrightarrow> n\<ge>2)"
  let ?res_ok = "Next reg' m'"
  have a3:"\<not> (\<not> result = ?res_ok \<or> (n\<ge>2))" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> n<2" using a3 by simp
   then show "False"
   proof
     have b0:"n<2" using a4 conjE by simp
     have b2: "interp2 n xins (Next reg m) = Stuck"using a0 exec_instr_def 
       by (smt (verit, del_insts) b0 interp2.elims interp2.simps(2) length_0_conv less_2_cases nat.inject outcome.simps(4) zero_neq_numeral)
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed

lemma interp2_aux2:
  assumes a0:"length xins = (2::nat)" and 
          a1:"result = interp2 n xins (Next reg m)"
        shows "result = Next reg' m' \<longrightarrow> (exec_instr (xins!0) 1 reg m) \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next reg' m' \<longrightarrow> (exec_instr (xins!0) 1 reg m) \<noteq> Stuck)"
  let ?tmp = "(exec_instr (xins!0) 1 reg m) "
  let ?res_ok = "Next reg' m'"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1:"xins\<noteq>[]" using a0 by auto
     have b2: "interp2 n xins (Next reg m) = Stuck"using a0 b0 b1 exec_instr_def 
       by (smt (verit, del_insts) interp2.elims nth_Cons_0 outcome.case(2) outcome.simps(4))
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed

(*interp2 n (drop 1 xins) (Next reg' m') = (exec_instr (xins!1) 1 reg' m')*)
lemma interp2_aux3:
  assumes a0:"length xins = (2::nat)" and 
          a1:"result = interp2 n xins (Next reg m)" and
          a2:"Next reg' m' = (exec_instr (xins!0) 1 reg m)"
        shows "result = Next reg'' m'' \<longrightarrow> (exec_instr (xins!1) 1 reg' m') \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next reg'' m'' \<longrightarrow> (exec_instr (xins!1) 1 reg' m') \<noteq> Stuck)"
  let ?tmp = "(exec_instr (xins!1) 1 reg' m') "
  let ?res_ok = "Next reg'' m''"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1:"xins\<noteq>[]" using a0 by auto
     have b2:"interp2 (n-1) (drop 1 xins) (Next reg' m') = (exec_instr (xins!1) 1 reg' m')" using a0 a1 a2 b1 
       by (smt (verit, ccfv_threshold) Cons_nth_drop_Suc One_nat_def Suc_n_not_le_n drop_eq_Nil interp2.elims lessI list.inject numeral_2_eq_2 outcome.case(2) outcome.simps(4))
     have b3: "interp2 (n-1) (drop 1 xins) (Next reg' m') = Stuck"using a0 b0 b1 exec_instr_def a2
       using interp2.elims nth_Cons_0 outcome.case(2) outcome.simps(4) using b2 by simp
     have b4: "interp2 n xins (Next reg m) = Stuck" using a0 a1 b3 exec_instr_def a2 b1
       by (smt (verit) Cons_nth_drop_Suc One_nat_def Suc_n_not_le_n assms(3) drop0 drop_eq_Nil interp2.elims list.inject list_consists_2 numeral_2_eq_2 outcome.case(2) outcome.simps(4) zero_less_Suc)
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed


lemma interp2_aux4:"n > 0 \<Longrightarrow> interp2 n [] (Next reg m) = Next reg m"
  by (metis Suc_pred interp2.simps(2))


lemma interp2_aux4: assumes a0:"Next reg2 m2 = interp2 n xins (Next reg m)" and
  a1:"length xins = (2::nat)"
shows" \<exists> reg' m'. Next reg' m' = (exec_instr (xins!0) 1 reg m) \<and> Next reg2 m2 = (exec_instr (xins!1) 1 reg' m')  "
proof-
  have b0:"n\<ge>2" using a0 a1 interp2_aux1 by blast
  from a0 a1 have "\<exists> result1. result1 = (exec_instr (xins!0) 1 reg m)" by simp
  then obtain result1 where " result1 = (exec_instr (xins!0) 1 reg m)" by simp
  have b1:"result1 \<noteq> Stuck" using interp2_aux2 a0 a1 
    by (metis \<open>(result1::outcome) = exec_instr ((xins::instruction list) ! (0::nat)) (1::64 word) (reg::preg \<Rightarrow> val) (m::64 word \<Rightarrow> 8 word option option)\<close> a0 a1)
  from b1 have "\<exists> reg' m'. Next reg' m' = result1" 
    by (metis outcome.exhaust)
  then obtain reg' m' where "Next reg' m' = result1" by blast
  have "\<exists> result2. result2 = (exec_instr (xins!1) 1 reg' m')" by simp
  then obtain result2 where " result2 = (exec_instr (xins!1) 1 reg' m')" by simp
  have b3:"result2 \<noteq> Stuck" using interp2_aux3 a0 a1 
    by (metis \<open>(result1::outcome) = exec_instr ((xins::instruction list) ! (0::nat)) (1::64 word) (reg::preg \<Rightarrow> val) (m::64 word \<Rightarrow> 8 word option option)\<close> \<open>(result2::outcome) = exec_instr ((xins::instruction list) ! (1::nat)) (1::64 word) (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option)\<close> \<open>Next (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option) = (result1::outcome)\<close>)
  then obtain reg'' m'' where "Next reg'' m'' = result2" 
    by (metis outcome.exhaust)
  have b4:"Next reg'' m'' = Next reg2 m2" using b1 interp2_aux4 interp2_aux1 try
  show ?thesis using a0 a1 b0 
    using \<open>(result1::outcome) = exec_instr ((xins::instruction list) ! (0::nat)) (1::64 word) (reg::preg \<Rightarrow> val) (m::64 word \<Rightarrow> 8 word option option)\<close> \<open>(result2::outcome) = exec_instr ((xins::instruction list) ! (1::nat)) (1::64 word) (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option)\<close> \<open>Next (reg''::preg \<Rightarrow> val) (m''::64 word \<Rightarrow> 8 word option option) = (result2::outcome)\<close> \<open>Next (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option) = (result1::outcome)\<close> b4 by blast
qed
lemma shift_subgoal_rr_aux1_1:"Next reg'' m'' = interp2 n xins (Next reg m) \<Longrightarrow> length xins = (2::nat) \<Longrightarrow> \<exists> reg' m'. Next reg' m' = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = (exec_instr (xins!1) 1 reg' m')  "
  using interp2_aux4 by simp


lemma shift_subgoal_rr_aux1_2:
  assumes a0:"length xins = (2::nat)" and a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m)" and a1:" Next reg'' m'' = (exec_instr (xins!1) 1 reg' m')"
  shows "Next reg'' m'' = interp2 n xins (Next reg m)"
  sorry

lemma shift_subgoal_rr_aux2:
  assumes a0:"xins = [(Pmovq_rr src (x64Syntax.RCX)),(Pshlq_r dst)]" and 
    a1:"Next reg'' m'' = interp2 n xins (Next reg m) " 
  shows " m'' = m"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 shift_subgoal_rr_aux2_3 
    by (meson shift_subgoal_rr_aux1_1)
qed


lemma push_pop_subgoal_rr_aux2_2:
  assumes a0:"xins = [Ppushl_r x64Syntax.RCX, Ppopl x64Syntax.RCX]" and 
    a1:"Next reg'' m'' = interp2 n xins (Next reg m)" and
    a2:"storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) \<noteq> None "
  shows "reg'' (IR x64Syntax.RCX) = reg (IR x64Syntax.RCX)"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 a2 push_pop_subgoal_rr_aux2_1 shift_subgoal_rr_aux1_1
    by metis
qed
*)

lemma interp3_aux2:
  assumes a0:"length xins = (2::nat)" and 
          a1:"result = interp3 xins (Next reg m)"
        shows "result = Next reg' m' \<longrightarrow> (exec_instr (xins!0) 1 reg m) \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next reg' m' \<longrightarrow> (exec_instr (xins!0) 1 reg m) \<noteq> Stuck)"
  let ?tmp = "(exec_instr (xins!0) 1 reg m) "
  let ?res_ok = "Next reg' m'"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1:"xins\<noteq>[]" using a0 by auto
     have b2: "interp3 xins (Next reg m) = Stuck"using a0 b0 b1 exec_instr_def 
       by (smt (verit, del_insts) interp3.elims nth_Cons_0 outcome.case(2) outcome.simps(4))
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed


lemma interp3_aux3:
  assumes a0:"length xins = (2::nat)" and 
          a1:"result = interp3 xins (Next reg m)" and
          a2:"Next reg' m' = (exec_instr (xins!0) 1 reg m)"
        shows "result = Next reg'' m'' \<longrightarrow> (exec_instr (xins!1) 1 reg' m') \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next reg'' m'' \<longrightarrow> (exec_instr (xins!1) 1 reg' m') \<noteq> Stuck)"
  let ?tmp = "(exec_instr (xins!1) 1 reg' m') "
  let ?res_ok = "Next reg'' m''"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1:"xins\<noteq>[]" using a0 by auto
     have b2:"interp3 (drop 1 xins) (Next reg' m') = (exec_instr (xins!1) 1 reg' m')" using a0 a1 a2 b0 b1 
       by (metis Cons_nth_drop_Suc Suc_eq_plus1 drop_eq_Nil interp3.simps(1) interp3.simps(2) le_refl lessI nat_1_add_1 outcome.simps(4))
     have b3: "interp3 (drop 1 xins) (Next reg' m') = Stuck"using a0 b0 b1 exec_instr_def a2
       using interp2.elims nth_Cons_0 outcome.case(2) outcome.simps(4) using b2 by simp
     have b4: "interp3 xins (Next reg m) = Stuck" using a0 a1 b3 exec_instr_def a2 
       by (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc_1 assms(3) drop_all eq_imp_le interp3.simps(2) lessI list_consists_2 outcome.simps(4))
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed

lemma interp3_aux4:"interp3 [] (Next reg m) = Next reg m"
  by simp

lemma interp3_aux5: assumes a0:"Next reg2 m2 = interp3 xins (Next reg m)" and
  a1:"length xins = (2::nat)"
shows" \<exists> reg' m'. Next reg' m' = (exec_instr (xins!0) 1 reg m) \<and> Next reg2 m2 = (exec_instr (xins!1) 1 reg' m')  "
proof-
  from a0 a1 have "\<exists> result1. result1 = (exec_instr (xins!0) 1 reg m)" by simp
  then obtain result1 where " result1 = (exec_instr (xins!0) 1 reg m)" by simp
  have b1:"result1 \<noteq> Stuck" using interp3_aux2 a0 a1 
    by (metis \<open>(result1::outcome) = exec_instr ((xins::instruction list) ! (0::nat)) (1::64 word) (reg::preg \<Rightarrow> val) (m::64 word \<Rightarrow> 8 word option option)\<close> a0 a1)
  from b1 have "\<exists> reg' m'. Next reg' m' = result1" 
    by (metis outcome.exhaust)
  then obtain reg' m' where "Next reg' m' = result1" by blast
  have "\<exists> result2. result2 = (exec_instr (xins!1) 1 reg' m')" by simp
  then obtain result2 where " result2 = (exec_instr (xins!1) 1 reg' m')" by simp
  have b3:"result2 \<noteq> Stuck" using interp3_aux3 a0 a1 
    by (metis \<open>(result1::outcome) = exec_instr ((xins::instruction list) ! (0::nat)) (1::64 word) (reg::preg \<Rightarrow> val) (m::64 word \<Rightarrow> 8 word option option)\<close> \<open>(result2::outcome) = exec_instr ((xins::instruction list) ! (1::nat)) (1::64 word) (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option)\<close> \<open>Next (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option) = (result1::outcome)\<close>)
  then obtain reg'' m'' where "Next reg'' m'' = result2" 
    by (metis outcome.exhaust)
  have b4:"Next reg'' m'' = Next reg2 m2" using interp3_aux4 a1 
    by (metis Suc_eq_plus1 \<open>(result1::outcome) = exec_instr ((xins::instruction list) ! (0::nat)) (1::64 word) (reg::preg \<Rightarrow> val) (m::64 word \<Rightarrow> 8 word option option)\<close> \<open>(result2::outcome) = exec_instr ((xins::instruction list) ! (1::nat)) (1::64 word) (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option)\<close> \<open>Next (reg''::preg \<Rightarrow> val) (m''::64 word \<Rightarrow> 8 word option option) = (result2::outcome)\<close> \<open>Next (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option) = (result1::outcome)\<close> a0 add.commute add.right_neutral interp3.simps(2) list_consists_2 outcome.simps(4))
  show ?thesis using a0 a1 
    using \<open>(result1::outcome) = exec_instr ((xins::instruction list) ! (0::nat)) (1::64 word) (reg::preg \<Rightarrow> val) (m::64 word \<Rightarrow> 8 word option option)\<close> \<open>(result2::outcome) = exec_instr ((xins::instruction list) ! (1::nat)) (1::64 word) (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option)\<close> \<open>Next (reg''::preg \<Rightarrow> val) (m''::64 word \<Rightarrow> 8 word option option) = (result2::outcome)\<close> \<open>Next (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option) = (result1::outcome)\<close> b4 by blast
qed

lemma shift_subgoal_rr_aux1_1:"Next reg'' m'' = interp3 xins (Next reg m) \<Longrightarrow> length xins = (2::nat) \<Longrightarrow> \<exists> reg' m'. Next reg' m' = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = (exec_instr (xins!1) 1 reg' m')  "
  using interp3_aux5 by simp

lemma shift_subgoal_rr_aux2_1:"xins = Pmovq_rr src (x64Syntax.RCX) \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> m'' = m "
  apply(unfold exec_instr_def) by simp

lemma shift_subgoal_rr_aux2_2:"xins = Pshlq_r dst \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> m'' = m"
  apply(unfold exec_instr_def) by simp

lemma shift_subgoal_rr_aux2_3:
  assumes a0:"xins = [(Pmovq_rr src (x64Syntax.RCX)),(Pshlq_r dst)]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " 
  shows " m'' = m"
  using shift_subgoal_rr_aux2_1 shift_subgoal_rr_aux2_2 
  by (metis One_nat_def a0 a1 a2 nth_Cons_0 nth_Cons_Suc)

lemma shift_subgoal_rr_aux2:
  assumes a0:"xins = [(Pmovq_rr src (x64Syntax.RCX)),(Pshlq_r dst)]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " 
  shows " m'' = m"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 shift_subgoal_rr_aux2_3 
    by (meson shift_subgoal_rr_aux1_1)
qed

lemma reg_rsp_consist:"dst = (bpf_to_x64_reg r) \<Longrightarrow> dst \<noteq> x64Syntax.RSP"
  apply(cases r) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)

lemma shift_subgoal_rr_aux3_1:"xins = Pmovq_rr (bpf_to_x64_reg src) (x64Syntax.RCX) \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> reg'' (IR SP) = reg (IR SP) "
  apply(unfold exec_instr_def reg_rsp_consist bpf_to_x64_reg_corr) 
  using nextinstr_def reg_rsp_consist by fastforce

lemma shift_subgoal_rr_aux3_2:"xins = Pshlq_r (bpf_to_x64_reg dst) \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> reg'' (IR SP) = reg (IR SP) "
  apply(unfold exec_instr_def reg_rsp_consist bpf_to_x64_reg_corr) 
  using nextinstr_def reg_rsp_consist sorry

lemma shift_subgoal_rr_aux3_3:
  assumes a0:"xins = [(Pmovq_rr (bpf_to_x64_reg src) (x64Syntax.RCX)),(Pshlq_r (bpf_to_x64_reg dst))]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " 
  shows " reg'' (IR SP) = reg (IR SP) "
  using shift_subgoal_rr_aux3_1 shift_subgoal_rr_aux3_2 reg_rsp_consist
  by (metis One_nat_def a0 a1 a2 nth_Cons_0 nth_Cons_Suc)

lemma shift_subgoal_rr_aux3:
  assumes a0:"xins = [(Pmovq_rr (bpf_to_x64_reg src) (x64Syntax.RCX)),(Pshlq_r (bpf_to_x64_reg dst))]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " 
  shows "reg'' (IR SP) = reg (IR SP)"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 shift_subgoal_rr_aux3_3 
    by (meson shift_subgoal_rr_aux1_1)
qed

lemma push_pop_subgoal_rr_aux1:
  assumes a0:"xins = [Ppushl_r x64Syntax.RCX, Ppopl x64Syntax.RCX]" and 
          a1:"result = (exec_instr (xins!0) 1 reg m)"
        shows "result = Next reg' m' \<longrightarrow> storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) \<noteq> None"
proof (rule ccontr)
  assume a2:"\<not> (result = Next reg' m' \<longrightarrow> storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) \<noteq> None)"
  let ?tmp = "storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) "
  let ?res_ok = "Next reg' m'"
  have a3:"\<not> (\<not> result = ?res_ok \<or> (?tmp \<noteq> None))" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = None" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = None" using a4 conjE by simp
     have b2: "exec_push 1 M32 m reg (reg (IR x64Syntax.RCX)) = Stuck"using a0 exec_instr_def 
       by (simp add: b0 exec_push_def)
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed

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
  have b2_1:"(exec_instr (xins!0) 1 reg m) = Next reg' m' \<longrightarrow> storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) \<noteq> None" using push_pop_subgoal_rr_aux1 a0 a1 by blast
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
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and
    a2:"storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) \<noteq> None "
  shows "reg'' (IR x64Syntax.RCX) = reg (IR x64Syntax.RCX)"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 a2 push_pop_subgoal_rr_aux2_1 shift_subgoal_rr_aux1_1
    by metis
qed

lemma shift_subgoal_rr_aux4_1:
  assumes a0:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr src (x64Syntax.RCX),Pshlq_r dst, Ppopl x64Syntax.RCX]" and 
    a1:"Next reg'' m'' = interp2 n xins (Next reg m)" and
    a2:"storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR ireg.RCX)) \<noteq> None "
  shows "reg'' (IR x64Syntax.RCX) = reg (IR x64Syntax.RCX)"
proof-
  have b0:"length xins = (4::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 a2 push_pop_subgoal_rr_aux2_1 shift_subgoal_rr_aux1_1
    sorry
qed



(*proof-
  from a0 a2 have "\<exists> reg' m'. Next reg' m' = exec_push 1 M32 m reg (reg (IR x64Syntax.RCX))" 
    using exec_instr_def push_pop_subgoal_rr_aux2_1 
    using a3 exec_push_def by force
  then obtain reg' m' where d0:" Next reg' m' = exec_push 1 M32 m reg (reg (IR x64Syntax.RCX))" by auto
  thus ?thesis using d0 push_pop_subgoal_rr_aux2_1 shift_subgoal_rr_aux1_1 try
*)


(*sp consisency*)
(*  let "?sp'"= "add64 (reg' (IR SP)) (vlong_of_memory_chunk M32)"
  have c1:"?sp' = reg (IR SP)" using add64_def sub64_def sorry*)


lemma shift_subgoal_rr_aux4_2:"xins = [Pmovq_rr src (x64Syntax.RCX),Pshlq_r dst] \<Longrightarrow> 
    Next reg'' m'' = interp3 xins (Next reg m) \<Longrightarrow> 
    \<forall> r . r \<notin> {dst,x64Syntax.RCX} \<longrightarrow> reg' (IR r) = reg (IR r)"
  sorry

lemma shift_subgoal_rr_aux4:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr src (x64Syntax.RCX),Pshlq_r dst,Ppopl x64Syntax.RCX] \<Longrightarrow> 
    Next reg'' m'' = interp3 xins (Next reg m) \<Longrightarrow> 
    \<forall> r\<noteq>dst. reg' (IR r) = reg (IR r)"
  sorry


lemma shift_subgoal_rr_aux5:
     "bins = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow>
     xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr ri (x64Syntax.RCX),Pshlq_r rd,Ppopl x64Syntax.RCX] \<Longrightarrow>
     (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
     Next reg' m' = interp3 xins (Next reg m) \<Longrightarrow>
     rd = (bpf_to_x64_reg dst) \<Longrightarrow>
     ri = (bpf_to_x64_reg src) \<Longrightarrow>
     reg (IR rd) = Vlong n1 \<Longrightarrow>
     reg (IR ri) = Vlong n2 \<Longrightarrow>
     n1  = rs dst \<Longrightarrow>
     n2  = rs src \<Longrightarrow> 
     Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
  sorry

lemma shift_subgoal_rr_aux6:"
    bins = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
    \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(unfold eval_alu64_def,simp)
  by (unfold eval_alu64_aux2_def, simp_all)

lemma test1:
  assumes 
       a1:"Some bl = x64_encode (Porq_rr dst src)" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decode (unat pc) l_bin = Some (length l_bin, xins)"  
     shows "xins = Porq_rr dst src"
  using x64_encode_decode_consistency 
  by (metis a1 a2 a3 option.sel prod.inject)

value "x64_decodes 2 (Option.the(x64_encodes_suffix ([Pmovq_rr x64Syntax.RAX x64Syntax.RBX,Pnop])))"
value "x64_decodes 0 (Option.the(x64_encodes_suffix ([Pnop,Pnop])))"
value "map snd [(1::nat,Pnop),(3::nat,Pmovq_rr x64Syntax.RAX x64Syntax.RBX)]"


value "x64_encodes_suffix [Pmovq_rr src dst,Pmovq_rr src dst]"
value "x64_decodes 0 (Option.the(x64_encodes_suffix [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RAX) (x64Syntax.RCX),
  Pshlq_r (x64Syntax.RBX),Ppopl x64Syntax.RCX]))"
value "x64_decodes 0 (Option.the(x64_encodes_suffix [Ppushl_r x64Syntax.RCX, Pmovq_rr (bpf_to_x64_reg src) (x64Syntax.RCX),
Pshlq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]))"

lemma test2:
  assumes 
       a1:"Some bl = x64_encodes_suffix [Pnop]" and
       a2:"list_in_list bl 0 l_bin" and
       a3:"x64_decodes 0 l_bin = Some v" and
       a4:"xins = map snd v"  
     shows "xins = [Pnop]"
  using x64_encodes_decodes_consistency a1 a2 a3 a4 by simp


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
  have b:"Some bl = x64_encodes_suffix [Ppushl_r x64Syntax.RCX, Pmovq_rr (bpf_to_x64_reg src) (x64Syntax.RCX),Pshlq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" 
    using a0 a1 a7 per_jit_shift_reg64_def by simp
  moreover have b0:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (bpf_to_x64_reg src) (x64Syntax.RCX),Pshlq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" 
    using x64_encodes_decodes_consistency per_jit_shift_reg64_def a1 a2 a3 
    using a8 calculation by presburger
    moreover have b1:"Vlong (rs dst) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using shift_subgoal_rr_aux5 b0 b1 b2 a0 a4 a5 by force
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 shift_subgoal_rr_aux4 by simp
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 shift_subgoal_rr_aux6 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed



 (*Vlong (rs (BPC)) = reg PC \<Longrightarrow>*)
(*lemma ja_subgoal_aux1:
      "bins = BPF_JA off \<Longrightarrow>
       xins = Pjmp d \<Longrightarrow>
       (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
       Next reg' m' = exec_instr xins sz reg m \<Longrightarrow> 
       d = ucast(off::i16)\<Longrightarrow>
       pc = reg' PC"
  apply (unfold exec_instr_def step)
  apply simp
  apply (unfold eval_pc_def nextinstr_def add64_def)
  apply(simp_all)
  apply(erule conjE)+
  apply(cases "reg RIP", simp_all)
  using cast_lemma4 by auto
*)

lemma ja_subgoal_aux2:"xins = Pjmp d \<Longrightarrow> Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
       \<forall> r. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  apply(unfold exec_instr_def, cases "xins", simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def) 
  by auto

lemma ja_subgoal_aux3:"bins = BPF_JA off \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 cur_cu remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
       \<forall> r. rs' r = rs r"
  by(cases "bins",simp_all)

lemma ja_subgoal_generic:
  assumes a0:"bins = BPF_JA off" and
       a1:"per_jit_ja (ucast off) = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decode (unat pc) l_bin = Some (length l_bin, xins)" and
       a4:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
       a5:"Next reg' m' = exec_instr xins sz reg m" and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" 
  shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b0:"xins = Pjmp (ucast off)" using x64_encode_decode_consistency per_jit_ja_def a1 a2 a3 get_relative_offset_def by fastforce
  moreover have b2:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" using a6 by simp
    have b4:"\<forall> r. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 ja_subgoal_aux2 by simp
    have b5:"\<forall> r. Vlong (rs' r) = Vlong (rs r)" using a0 a4 ja_subgoal_aux3 by simp
    have b6:"\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b7 by fastforce
  qed


lemma load_subgoal_aux1:
      "bins = BPF_LDX chk dst src (b_off::i16) \<Longrightarrow>
       xins = Pmov_mr (Addrmode (Some ri) None (x_off::u32)) rd chk \<Longrightarrow>
       rd = (bpf_to_x64_reg dst)\<Longrightarrow>
       ri = (bpf_to_x64_reg src) \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       reg (IR ri) = Vlong n2 \<Longrightarrow>
       n1  = rs dst \<Longrightarrow>
       n2  = rs src \<Longrightarrow>
       (BPF_OK pc rs' mem' ss' is_v1 cur_cu remain_cu) = step fuel bins rs mem ss is_v1 cur_cu remain_cu \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       m = mem \<Longrightarrow>
       m' = mem'"
  apply (unfold exec_instr_def step)
  apply(cases xins)
  apply simp_all
  apply (unfold eval_load_def Let_def cast_lemma6, simp_all)
  apply (simp add: exec_load_def eval_addrmode64_def add64_def nextinstr_nf_def nextinstr_def)
  by (metis (mono_tags, lifting) bpf_state.distinct(1) bpf_state.inject option.case_eq_if outcome.distinct(1) outcome.inject)

lemma load_subgoal_aux2_1:
  assumes a0:"bins = BPF_LDX chk dst src b_off" and 
          a1:"step fuel bins rs mem ss is_v1 cur_cu remain_cu = result"
        shows "result = (BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) \<longrightarrow> Mem.loadv chk mem (Vlong (eval_snd_op_u64 (SOReg src) rs + scast b_off)) \<noteq> Some Vundef"
proof (rule ccontr)
  assume a2:"\<not> (result = (BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) \<longrightarrow> (Mem.loadv chk mem (Vlong (eval_snd_op_u64 (SOReg src) rs + scast b_off)) \<noteq> Some Vundef))"
  let ?x = "eval_snd_op_u64 (SOReg src) rs + scast b_off"
  let ?tmp = "Mem.loadv chk mem (Vlong ?x)"
  let ?res_ok = "(BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu)"
  have a3:"\<not> (\<not> result = ?res_ok \<or> (?tmp \<noteq> Some Vundef))" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Some Vundef" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Some Vundef" using a4 conjE by simp
     have b1:"eval_load chk dst src b_off rs mem = None"  using eval_load_def b0 by simp
     have b2: "step fuel bins rs mem ss is_v1 cur_cu remain_cu = BPF_EFlag"using a0 b1 eval_load_def by simp
     thus "False" using b2 
       by (metis a1 a4 bpf_state.distinct(3))
   qed
 qed

lemma load_subgoal_aux2_2:
  assumes a0:"bins = BPF_LDX chk dst src b_off" and 
          a1:"step fuel bins rs mem ss is_v1 cur_cu remain_cu = result"
        shows "result = (BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) \<longrightarrow> Mem.loadv chk mem (Vlong (eval_snd_op_u64 (SOReg src) rs + scast b_off)) \<noteq> None"
proof (rule ccontr)
  assume a2:"\<not> (result = (BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) \<longrightarrow> (Mem.loadv chk mem (Vlong (eval_snd_op_u64 (SOReg src) rs + scast b_off)) \<noteq> None))"
  let ?x = "eval_snd_op_u64 (SOReg src) rs + scast b_off"
  let ?tmp = "Mem.loadv chk mem (Vlong ?x)"
  let ?res_ok = "(BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu)"
  have a3:"\<not> (\<not> result = ?res_ok \<or> (?tmp \<noteq> None))" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = None" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = None" using a4 conjE by simp
     have b1:"eval_load chk dst src b_off rs mem = None"  using eval_load_def b0 by simp
     have b2: "step fuel bins rs mem ss is_v1 cur_cu remain_cu = BPF_EFlag"using a0 b1 eval_load_def by simp
     thus "False" using b2 
       using a1 a4 by auto
   qed
 qed

lemma load_subgoal_aux2_3:
  assumes a0:"bins = BPF_LDX chk dst src b_off" and 
          a1:"step fuel bins rs mem ss is_v1 cur_cu remain_cu = result"
        shows "result = (BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) \<longrightarrow> Mem.loadv chk mem (Vlong (eval_snd_op_u64 (SOReg src) rs + scast b_off)) \<notin> {None, Some Vundef} "
  using load_subgoal_aux2_1 load_subgoal_aux2_2 a0 a1 by auto

lemma load_subgoal_aux2_4:
  assumes a0:"bins = BPF_LDX chk dst src b_off" and 
          a1:"step fuel bins rs mem ss is_v1 cur_cu remain_cu = result"
        shows "result = (BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) \<longrightarrow> eval_load chk dst src b_off rs mem \<noteq> None"
proof (rule ccontr)
  assume a2:"\<not> (result = (BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) \<longrightarrow> eval_load chk dst src b_off rs mem \<noteq> None)"
  let ?res_ok = "(BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu)"
  have a3:"\<not> (\<not> result = ?res_ok \<or> (eval_load chk dst src b_off rs mem \<noteq> None))" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> (eval_load chk dst src b_off rs mem = None)" using a3 by simp
   then show "False"
   proof
     have b1:"eval_load chk dst src b_off rs mem = None" using a4 conjE by simp
     have b2: "step fuel bins rs mem ss is_v1 cur_cu remain_cu = BPF_EFlag"using a0 b1 eval_load_def by simp
     thus "False" using b2 a1 a0 a2 by auto
   qed
 qed

(*lemma load_subgoal_aux2:
      "bins = BPF_LDX chk dst src (b_off::i16) \<Longrightarrow>
       xins = Pmov_mr (Addrmode (Some ri) None (x_off::u32)) rd chk \<Longrightarrow>
       rd = (bpf_to_x64_reg dst)\<Longrightarrow>
       ri = (bpf_to_x64_reg src) \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       reg (IR ri) = Vlong n2 \<Longrightarrow>
       n1  = rs dst \<Longrightarrow>
       n2  = rs src \<Longrightarrow>
       b_off = scast x_off \<Longrightarrow>
       (BPF_OK pc rs' mem' ss' is_v1 cur_cu remain_cu) = step fuel bins rs mem ss is_v1 cur_cu remain_cu \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       m = mem \<Longrightarrow>
       Mem.loadv chk mem (Vlong (eval_snd_op_u64 (SOReg src) rs + scast (scast b_off)))\<noteq> None \<Longrightarrow>
       scast x_off = scast (scast x_off) \<Longrightarrow>
       Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
  apply (unfold exec_instr_def step)
  apply(cases xins)
  apply simp_all
  apply (simp add: exec_load_def eval_addrmode64_def add64_def nextinstr_nf_def nextinstr_def)
  apply (cases "loadv chk mem (Vlong (rs src + scast x_off))")
   apply simp
  apply (cases "loadv chk mem (Vlong (rs src + scast (scast x_off)))")
  apply simp_all
  using  load_subgoal_aux2_1
*)


lemma load_subgoal_rr_aux2:
  assumes a0:"bins = BPF_LDX chk dst src b_off" and
       a1:"xins = Pmov_mr (Addrmode (Some ri) None x_off) rd chk" and
       a2:"rd = (bpf_to_x64_reg dst)" and
       a3:"ri = (bpf_to_x64_reg src)" and
       a4:"reg (IR rd) = Vlong n1" and
       a5:"reg (IR ri) = Vlong n2" and
       a6:"n1 = rs dst" and
       a7:"n2 = rs dst" and
       a8:"x_off = ucast b_off " and
       a9:"(BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs mem ss is_v1 cur_cu remain_cu" and
       a10:"Next reg' m' = exec_instr xins sz reg m" and
       a11:"m = mem" 
       shows "Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
proof-
  let ?t = "Addrmode (Some (bpf_to_x64_reg src)) None x_off"
  have "xins = Pmov_mr ?t rd chk" using Orderings.ord.ord_less_eq_trans Extraction.exE_realizer a0 apply simp
    using a1 a3 by fastforce
  let ?x = "eval_snd_op_u64 (SOReg src) rs + scast b_off"
  let ?tmp = "Mem.loadv chk mem (Vlong ?x)"
  have b0:"step fuel bins rs mem ss is_v1 cur_cu remain_cu = (BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) \<longrightarrow> ?tmp \<noteq> None" 
    using load_subgoal_aux2_2 using a0 a11 by blast
  have b1:"?tmp \<noteq> None" using b0 a9 by simp
  have b2:"Next reg' m' = exec_load sz chk m ?t reg (IR (bpf_to_x64_reg dst))" using exec_instr_def a1 apply (cases "xins") 
                        apply blast apply simp_all by (simp add: a10 a2 a3)
  have b3:"Next reg' m' = (case loadv chk m (eval_addrmode64 (?t) reg) 
           of None \<Rightarrow> Stuck | Some (v::val) \<Rightarrow> Next (nextinstr_nf sz (reg(IR (bpf_to_x64_reg dst) := v))) m) "
    using exec_load_def by (simp add: b2)
  (*have b4:"Next reg' m' = (case loadv chk m (Vlong (rs src + scast x_off)) of None \<Rightarrow> Stuck
        | Some (v::val) \<Rightarrow> Next (nextinstr_nf sz (reg(IR (bpf_to_x64_reg dst) := v))) m)"
    using eval_addrmode64_def b3 add64_def nextinstr_nf_def using a3 a5 a7 sorry*)
  have b4:"Next reg' m' = (case loadv chk m (Vlong (rs src + scast x_off)) of None \<Rightarrow> Stuck | 
    Some (v::val) \<Rightarrow> Next (nextinstr_nf sz (reg(IR (bpf_to_x64_reg dst) := v))) m)" 
    using exec_load_def eval_addrmode64_def b3 add64_def nextinstr_nf_def nextinstr_def a3 a5 a7 a11 sorry
  have b5:"Next reg' m' = Next (nextinstr_nf sz (reg(IR (bpf_to_x64_reg dst) := Option.the(?tmp)))) m" using b4 b1 apply (cases "bins")
    apply simp_all using a0  apply simp_all using a8 option.sel sorry
  have b6:" reg'(IR (bpf_to_x64_reg dst)) = Option.the(?tmp)" using nextinstr_nf_def nextinstr_def b5 by simp
  have c0:"eval_load chk dst src b_off rs mem \<noteq> None" using eval_load_def a0 load_subgoal_aux2_4 a9 by metis
  let ?rss' = "eval_load chk dst src b_off rs mem"
 (*have c1_1:"?tmp  \<noteq> None \<or> ?tmp \<noteq> Some Vundef" using a9 load_subgoal_aux2_3 by blast
  let "?tmpd" = "Option.the ?tmp"
  have " \<exists> x y. eval_load chk dst src b_off rs mem \<noteq> None \<longrightarrow> ?tmp = Some (Vlong x) \<or> ?tmp = Some (Vint y) " using c1_1 eval_load_def impI *)
(*
  fix v1 assume "?tmp = Some(Vlong v1)" 
  have c1_1:"(Option.the(?rss') dst) = v1" using a0 a9 the_def eval_load_def Let_def 
    using loadv (chk) (mem) (Vlong (eval_snd_op_u64 (SOReg (src)) (rs) + scast (b_off))) = Some (Vlong (v1)) by force
  fix v2 assume "?tmp = Some(Vint v2)" 
  have c1_2:"(Option.the(?rss') dst) = ucast v2" using a0 a9 the_def eval_load_def Let_def 
    using loadv (chk) (mem) (Vlong (eval_snd_op_u64 (SOReg (src)) (rs) + scast (b_off))) = Some (Vint (v2)) by force
  fix v3 assume "?tmp = None" 
 *)
  have c1:"Vlong ((Option.the(?rss') dst)) = Option.the(?tmp)" (*using a0 a9 the_def eval_load_def Let_def c0 cast_lemma6*)
  proof (cases ?tmp)
    case None
    have d1:"eval_load chk dst src b_off rs mem = None" using eval_load_def 
      using None b1 by blast
    then show ?thesis using c0 d1 by simp
  next
    case (Some a)
      then show ?thesis 
    proof(cases a)
      case Vundef
        have d1:"eval_load chk dst src b_off rs mem = None" using eval_load_def 
          using Some Vundef by auto
          then show ?thesis using c0 d1 by simp
       next
         case (Vlong b)
         then show ?thesis using eval_load_def
           using Some by auto
       next
         case (Vint c)
         then show ?thesis using eval_load_def Let_def c0 sorry
           by simp
       next
         case (Vbyte c)
         have d1:"eval_load chk dst src b_off rs mem = None" using eval_load_def 
          using Some Vbyte by auto
          then show ?thesis using c0 d1 by simp
       next
         case (Vshort c)
         have d1:"eval_load chk dst src b_off rs mem = None" using eval_load_def 
           using Some Vshort by auto
           then show ?thesis using c0 d1 by simp
       qed
     qed
  have c3:"Option.the(?rss')dst = rs' dst" using the_def sorry
  have c4:"Vlong (rs' dst) = Option.the(?tmp)" using c3 c1 by simp
  thus ?thesis using c4 b6 by simp
qed


lemma load_subgoal_rr_aux3_1:"xins = Pmov_mr (Addrmode (Some src) None (b_off)) dst chk \<Longrightarrow> 
  Next reg' m' = exec_instr xins sz reg m \<Longrightarrow> \<forall> r \<noteq> dst. reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def, cases "xins", simp_all)
  apply(unfold exec_load_def eval_addrmode64_def nextinstr_nf_def nextinstr_def add64_def) 
  apply(cases "Addrmode (Some src) None b_off")
  subgoal for x1 x2 x3 apply(simp_all) apply(cases x1,simp_all)
    apply (cases "reg (IR src)",simp_all) 
        apply(cases "loadv chk m Vundef",simp_all)
    subgoal for a apply(cases "loadv chk m Vundef",simp_all)
      done
    subgoal for b apply(cases "loadv chk m Vundef",simp_all)
      done
    subgoal for c apply(cases "loadv chk m Vundef",simp_all)
      done
    subgoal for x4 apply(cases "loadv chk m (Vlong (x4 + scast x3))",simp_all)
      done
    done
  done

lemma loadq_subgoal_rr_aux3: 
  assumes a0:"xins = Pmov_mr (Addrmode (Some (bpf_to_x64_reg src)) None (ucast (b_off))) (bpf_to_x64_reg dst) chk" and
          a1:"Next reg' m' = exec_instr xins sz reg m" 
        shows " \<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
 using cast_lemma6 a0 by (metis a1 bpf_to_x64_reg_corr load_subgoal_rr_aux3_1)

lemma loadq_subgoal_rr_aux4:"bins = BPF_LDX chk dst src b_off \<Longrightarrow> (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
       \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases "bins",simp_all)
  apply(unfold eval_load_def,simp)
  apply(cases "loadv chk m (Vlong (rs src + scast b_off))" ,simp_all)
  subgoal for a apply(cases a)
  by simp_all
  done

lemma loadq_subgoal_rr_generic:
  assumes a0:"bins = BPF_LDX chk dst src b_off" and
       a1:"per_jit_load_reg64 dst src chk b_off = Some bl" and
       a2:"list_in_list bl (unat pc) l_bin" and
       a3:"x64_decode (unat pc) l_bin = Some (length l_bin, xins)" and
       a4:"(BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs mem ss is_v1 cur_cu remain_cu" and
       a5:"Next reg' m' = exec_instr xins sz reg m" and
       a6:"(\<forall> r. Vlong (rs r) = reg (IR (bpf_to_x64_reg r)))" and
       a7:"m = mem"
  shows "(\<forall> r. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b0:"xins = Pmov_mr (Addrmode (Some (bpf_to_x64_reg src)) None (ucast (b_off))) (bpf_to_x64_reg dst) chk" using x64_encode_decode_consistency per_jit_load_reg64_def a1 a2 a3 by fastforce
    moreover have b1:"Vlong (rs dst) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using load_subgoal_rr_aux2 b0 b1 b2 a0 a1 a2 a3 a4 a5 a6 a7 sorry
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 loadq_subgoal_rr_aux3 by blast
    have b5:"\<forall> r \<noteq> dst. Vlong (rs' r) = Vlong (rs r)" using a0 a4 loadq_subgoal_rr_aux4 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' r) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed

lemma addl_subgoal_rr:
      "bins = BPF_ALU BPF_ADD dst (SOReg src) \<Longrightarrow>
       xins = Paddl_rr rd ri \<Longrightarrow>
       (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       rd = bpf_to_x64_reg dst \<Longrightarrow>
       ri = bpf_to_x64_reg src \<Longrightarrow>
       reg (IR rd) = Vint n1 \<Longrightarrow>
       reg (IR ri) = Vint n2 \<Longrightarrow>
       ucast n1 = rs dst \<Longrightarrow>
       ucast n2  = rs src \<Longrightarrow>
       reg' (IR rd) = Vint n3 \<Longrightarrow>
       ucast n3 = rs'dst"
  apply (unfold exec_instr_def step)
  apply simp
  apply (unfold eval_alu32_def)
  apply (unfold eval_alu32_aux1_def)
  apply (unfold Let_def)
  apply (unfold add64_def add32_def)
  apply (unfold nextinstr_nf_def nextinstr_def eval_reg_def)
  apply simp
  apply (unfold add64_def)
  apply (erule conjE)
  using cast_lemma2
  



lemma addl_subgoal_ri:
      "bins = BPF_ALU BPF_ADD dst (SOImm src) \<Longrightarrow>
       xins = Paddl_ri rd imm \<Longrightarrow>
       (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
       Next reg' m' = exec_instr xins sz reg m \<Longrightarrow> 
       rd = bpf_to_x64_reg dst \<Longrightarrow>
       imm = ucast (src) \<Longrightarrow>
       reg (IR rd) = Vint n1 \<Longrightarrow>
       ucast n1  = rs dst \<Longrightarrow>
       reg' (IR rd) = Vint n3 \<Longrightarrow>
       ucast n3 = rs'dst"
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


lemma subl_subgoal_ri:
      "bins = BPF_ALU BPF_SUB dst (SOImm src) \<Longrightarrow>
       xins = Psubl_ri rd imm \<Longrightarrow>
       (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       rd = bpf_to_x64_reg dst \<Longrightarrow>
       imm = ucast (src) \<Longrightarrow>
       reg (IR rd) = Vint n1 \<Longrightarrow>
       ucast n1  = rs dst \<Longrightarrow>
       reg' (IR rd) = Vint n3 \<Longrightarrow>
       ucast n3 = rs'dst"
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

end
