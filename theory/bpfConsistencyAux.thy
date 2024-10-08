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


lemma interp3_aux2:
  assumes a0:"xins\<noteq>[]" and 
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
     have b2: "interp3 xins (Next reg m) = Stuck"using a0 b0 exec_instr_def 
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

lemma interp3_length4_aux1:
  assumes a0:"xins\<noteq>[]" and 
          a1:"result = interp3 xins (Next reg m)" and
          a2:"Next reg' m' = (exec_instr (xins!0) 1 reg m)"
        shows "result = Next reg'' m'' \<longrightarrow> interp3 (tl xins) (Next reg' m') \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next reg'' m'' \<longrightarrow> interp3 (tl xins) (Next reg' m') \<noteq> Stuck)"
  let ?tmp = "interp3 (tl xins) (Next reg' m') "
  let ?res_ok = "Next reg'' m''"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1:"xins\<noteq>[]" using a0 by auto
     have b2:"interp3 (tl xins) (Next reg' m') = interp3 (xins) (Next reg m)" using a0 a1 a2 b0 b1 
       by (metis assms(3) hd_conv_nth interp3.simps(2) list.exhaust list.sel(1) list.sel(3) outcome.simps(4))
     have b3: "interp3 (tl xins) (Next reg' m') = Stuck"using a0 b0 b1 exec_instr_def a2
       using interp2.elims nth_Cons_0 outcome.case(2) outcome.simps(4) using b2 by simp
     have b4: "interp3 xins (Next reg m) = Stuck" using a0 a1 b3 exec_instr_def a2 
       using b2 by argo
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
  have b1_1:"xins\<noteq>[]" using a1 by auto
  have b1:"result1 \<noteq> Stuck" using interp3_aux2 a0 b1_1 
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

lemma interp3_length4_aux2:
  assumes a0:"length xins = (4::nat)" and 
          a1:"result = interp3 xins (Next reg m)" and
          a2:"Next reg2 m2 = interp3 (take 2 xins) (Next reg m)"
        shows "result = Next reg'' m'' \<longrightarrow> interp3 (drop 2 xins) (Next reg2 m2) \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next reg'' m'' \<longrightarrow> interp3 (drop 2 xins) (Next reg2 m2) \<noteq> Stuck)"
  let ?tmp = "interp3 (drop 2 xins) (Next reg2 m2) "
  let ?res_ok = "Next reg'' m''"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1:"(take 2 xins) @ (drop 2 xins)= xins" using a0
       by (simp add: Cons_nth_drop_Suc numeral_3_eq_3 numeral_nat(2))
     let ?tmplist = "take 2 xins"
     have b2_1:"?tmplist = [(xins!0)]@[(xins!1)]" 
       by (metis One_nat_def Suc_1 a0 append_Nil less_1_mult less_2_cases_iff numeral_Bit0_eq_double take_0 take_Suc_conv_app_nth zero_less_numeral)
     have b2_2:"length ?tmplist = (2::nat)" 
       by (simp add: b2_1)
     have b2_3:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (xins!0) 1 reg m) \<and> Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1 )" using a2 b2_2 b2_1 interp3_aux5 
       by (metis Cons_eq_appendI One_nat_def append_Nil assms(3) nth_Cons_0 nth_Cons_Suc)
     then obtain reg1 m1 where b2_4:"Next reg1 m1 = (exec_instr (xins!0) 1 reg m) \<and> Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1 )" by auto
     have b2_5:"Next reg1 m1 = (exec_instr (xins!0) 1 reg m)" using b2_3 using b2_4 by blast
     have b2_6:" Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1 )" using b2_3 using b2_4 by blast
     have b2_7:"[xins!0]@[xins!1] @ (drop 2 xins)= xins" using a0
       by (simp add: Cons_nth_drop_Suc numeral_3_eq_3 numeral_nat(2))
     have b2:"interp3 (drop 2 xins) (Next reg2 m2) = interp3 (xins) (Next reg m)" using a0 a1 a2 a3 b0 
       using append_Cons append_Nil assms(3) b2_5 b2_6 b2_7 interp3.simps(2) outcome.simps(4) by metis
     have b3: "interp3 (drop 2 xins) (Next reg2 m2) = Stuck"using a0 b0 b1 exec_instr_def a2
       using interp2.elims nth_Cons_0 outcome.case(2) outcome.simps(4) by auto
     have b4: "interp3 xins (Next reg m) = Stuck" using a0 a1 b3 exec_instr_def a2 
       using b2 by argo
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed

(*
lemma interp3_length4_aux2:
  assumes a0:"length xins = (4::nat)" and 
          a1:"result = interp3 xins (Next reg m)" and
          a2:"Next reg1 m1 = (exec_instr (xins!0) 1 reg m)" and
          a3:"Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1)" (*"Next reg' m' = interp3 (take 2 xins) (Next reg m)"*)
        shows "result = Next reg'' m'' \<longrightarrow> interp3 (drop 2 xins) (Next reg2 m2) \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next reg'' m'' \<longrightarrow> interp3 (drop 2 xins) (Next reg2 m2) \<noteq> Stuck)"
  let ?tmp = "interp3 (drop 2 xins) (Next reg2 m2) "
  let ?res_ok = "Next reg'' m''"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1:"[xins!0]@[xins!1] @ (drop 2 xins)= xins" using a0
       by (simp add: Cons_nth_drop_Suc numeral_3_eq_3 numeral_nat(2))
     have b2:"interp3 (drop 2 xins) (Next reg2 m2) = interp3 (xins) (Next reg m)" using a0 a1 a2 a3 b0 b1 
       by (metis append_Cons append_Nil assms(3) assms(4) interp3.simps(2) outcome.simps(4))
     have b3: "interp3 (drop 2 xins) (Next reg2 m2) = Stuck"using a0 b0 b1 exec_instr_def a2
       using interp2.elims nth_Cons_0 outcome.case(2) outcome.simps(4) using b2 by simp
     have b4: "interp3 xins (Next reg m) = Stuck" using a0 a1 b3 exec_instr_def a2 
       using b2 by argo
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed
*)

lemma interp3_length4_aux3:
  assumes a0:"length xins = (4::nat)" and 
          a1:"result = interp3 xins (Next reg m)" and
          a2:"Next reg1 m1 = (exec_instr (xins!0) 1 reg m)" and
          a3:"Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1)" and
          a4:"Next reg' m' = (exec_instr (xins!2) 1 reg2 m2)"  (*"Next reg' m' = interp3 (butlast xins) (Next reg m)"*)
        shows "result = Next reg'' m'' \<longrightarrow> (exec_instr (xins!3) 1 reg' m') \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next reg'' m'' \<longrightarrow> (exec_instr (xins!3) 1 reg' m') \<noteq> Stuck)"
  let ?tmp = "(exec_instr (xins!3) 1 reg' m') "
  let ?res_ok = "Next reg'' m''"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1:"[(xins!0)]@[(xins!1)]@[(xins!2)]@[(xins!3)] = xins"
       using a0 
       by (metis Cons_eq_appendI One_nat_def append_Nil last.simps list.discI list_consists_4)
     have b2:"exec_instr (xins!3) 1 reg' m' = interp3 (xins) (Next reg m)" using a0 a1 a2 a3 a4 b0 b1 
       by (metis Cons_eq_appendI append_Nil assms(3) assms(4) assms(5) interp3.simps(1) interp3.simps(2) interp3_length4_aux1 list.sel(3) outcome.simps(4))
     have b4: "interp3 xins (Next reg m) = Stuck" using a0 a1 b2 exec_instr_def a2 
       by simp
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed

lemma interp3_aux6:
  assumes a0:"length xins > i" and 
          a1:"result = interp3 xins (Next reg m)" and
          a2:"Next reg' m' = interp3 (take i xins) (Next reg m)"
        shows "result = Next reg'' m'' \<longrightarrow> (exec_instr (xins!(i+1)) 1 reg' m') \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next reg'' m'' \<longrightarrow> (exec_instr (xins!(i+1)) 1 reg' m') \<noteq> Stuck)"
  let ?tmp = "(exec_instr (xins!(i+1)) 1 reg' m') "
  let ?res_ok = "Next reg'' m''"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1:"length xins - i > 0" using a0 by auto
     have b2:"interp3 [xins!(i+1)] (Next reg' m') = (exec_instr (xins!(i+1)) 1 reg' m')" using a0 a1 a2 b0 b1 
       by (metis Cons_nth_drop_Suc Suc_eq_plus1 drop_eq_Nil interp3.simps(1) interp3.simps(2) le_refl lessI nat_1_add_1 outcome.simps(4))
     have b3: "interp3 [xins!(i+1)] (Next reg' m') = Stuck"using a0 b0 b1 exec_instr_def a2
       using interp2.elims nth_Cons_0 outcome.case(2) outcome.simps(4) using b2 by simp
     have b4: "interp3 (take (i+1) xins) (Next reg m) = Stuck" using a0 a1 b3 exec_instr_def a2 
       sorry
     have b5: "interp3 xins (Next reg m) = Stuck" using b4 sorry
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed

lemma interp3_aux7: assumes a0:"Next reg2 m2 = interp3 xins (Next reg m)" and
  a1:"length xins = (4::nat)"
shows" \<exists> reg' m'. Next reg' m' = (exec_instr (xins!0) 1 reg m) \<and> Next reg2 m2 = (exec_instr (xins!1) 1 reg' m')  "
proof-
  from a0 a1 have "\<exists> result1. result1 = (exec_instr (xins!0) 1 reg m)" by simp
  then obtain result1 where " result1 = (exec_instr (xins!0) 1 reg m)" by simp
  have b1_1:"xins\<noteq>[]" using a1 by auto
  have b1:"result1 \<noteq> Stuck" using interp3_aux2 a0 b1_1 
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


lemma run_trans: "\<forall> A B C as bs. interp3 as A  = B \<and> interp3 bs B = C \<longrightarrow> interp3 (as @ bs) A = C"
  proof-
  {
    fix B C as bs
    have "\<forall> A. interp3 as A  = B \<and> interp3 bs B = C \<longrightarrow> interp3 (as @ bs) A = C"
      proof(induct as)
        case Nil then show ?case by simp
      next
        case (Cons c cs)
        assume a0: "\<forall>A. interp3 cs A = B \<and> interp3 bs B = C \<longrightarrow> interp3 (cs @ bs) A = C"
        show ?case
          proof-
            fix A
            have "interp3 (c # cs) A  = B \<and> interp3 bs B = C \<longrightarrow> interp3 ((c # cs) @ bs) A = C"
            proof
              assume b0: "interp3 (c # cs) A = B \<and> interp3 bs B = C"

              from b0 obtain A' where b2: "interp3 [c] A  = A' \<and> interp3 cs A' = B" 
              proof(cases A)
                case (Next x11 x12)
                then show ?thesis sorry
              next
                case Stuck
                then show ?thesis sorry
              qed
              with a0 b0 have "interp3 (cs @ bs) A' = C"
                using local.Cons by blast
              with b2 show "interp3 ((c # cs) @ bs) A = C" 
                by simp
            qed
          then show ?thesis using a0 by auto
          qed
      qed
  }
  then show ?thesis by auto
  qed


lemma run_trans: "\<forall> A B C as bs. interp4 as A  = B \<and> interp4 bs B = C \<longrightarrow> interp4 (as @ bs) A = C"
  proof-
  {
    fix B C as bs
    have "\<forall> A. interp4 as A  = B \<and> interp4 bs B = C \<longrightarrow> interp4 (as @ bs) A = C"
      proof(induct as)
        case Nil then show ?case by simp
      next
        case (Cons c cs)
        assume a0: "\<forall>A. interp4 cs A = B \<and> interp4 bs B = C \<longrightarrow> interp4 (cs @ bs) A = C"
        show ?case
          proof-
            fix A
            have "interp4 (c # cs) A  = B \<and> interp4 bs B = C \<longrightarrow> interp4 ((c # cs) @ bs) A = C"
            proof
              assume b0: "interp4 (c # cs) A = B \<and> interp4 bs B = C"
              from b0 obtain A' where b2: "interp4 [c] A  = A' \<and> interp4 cs A' = B" by simp
              with a0 b0 have "interp4 (cs @ bs) A' = C"
                using local.Cons by blast
              with b2 show "interp4 ((c # cs) @ bs) A = C" 
                by simp
            qed
          then show ?thesis using a0 by auto
          qed
      qed
  }
  then show ?thesis by auto
  qed

lemma shift_subgoal_rr_aux1_1:"Next reg'' m'' = interp3 xins (Next reg m) \<Longrightarrow> length xins = (2::nat) \<Longrightarrow> \<exists> reg' m'. Next reg' m' = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = (exec_instr (xins!1) 1 reg' m')  "
  using interp3_aux5 by simp

lemma shift_subgoal_rr_aux2_1:"xins = Pmovq_rr (x64Syntax.RCX) src  \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> m'' = m "
  apply(unfold exec_instr_def) by simp

lemma shift_subgoal_rr_aux2_2:"xins = Pshlq_r dst \<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> m'' = m"
  apply(unfold exec_instr_def) by simp

lemma shift_subgoal_rr_aux2_3:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX) src),(Pshlq_r dst)]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " 
  shows " m'' = m"
  using shift_subgoal_rr_aux2_1 shift_subgoal_rr_aux2_2 
  by (metis One_nat_def a0 a1 a2 nth_Cons_0 nth_Cons_Suc)

lemma shift_subgoal_rr_aux2:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX) src),(Pshlq_r dst)]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " 
  shows " m'' = m"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 shift_subgoal_rr_aux2_3 
    by (meson shift_subgoal_rr_aux1_1)
qed

lemma reg_rsp_consist:"r = (bpf_to_x64_reg dst) \<Longrightarrow> r \<noteq> x64Syntax.RSP"
  apply(cases dst) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)

lemma shift_subgoal_rr_aux3_1:"xins = Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src)\<Longrightarrow> 
    Next reg'' m'' = (exec_instr xins 1 reg m) \<Longrightarrow> reg'' (IR SP) = reg (IR SP) "
  apply(unfold exec_instr_def reg_rsp_consist bpf_to_x64_reg_corr) 
  using nextinstr_def reg_rsp_consist by fastforce

lemma shift_subgoal_rr_aux3_2:"xins = Pshlq_r (bpf_to_x64_reg dst) \<Longrightarrow> 
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
  (* no dealing with Vundef ? *)
  done
lemma shift_subgoal_rr_aux3_3:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src)),(Pshlq_r (bpf_to_x64_reg dst))]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " 
  shows " reg'' (IR SP) = reg (IR SP) "
  using shift_subgoal_rr_aux3_1 shift_subgoal_rr_aux3_2 reg_rsp_consist
  by (metis One_nat_def a0 a1 a2 nth_Cons_0 nth_Cons_Suc)

lemma shift_subgoal_rr_aux3:
  assumes a0:"xins = [(Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src)),(Pshlq_r (bpf_to_x64_reg dst))]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " 
  shows "reg'' (IR SP) = reg (IR SP)"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 shift_subgoal_rr_aux3_3 
    by (meson shift_subgoal_rr_aux1_1)
qed

lemma push_pop_subgoal_rr_aux1:
  assumes a0:"hd xins = Ppushl_r x64Syntax.RCX" and 
          a1:"result = (exec_instr (hd xins) 1 reg m)"
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
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" 
  shows "reg'' (IR x64Syntax.RCX) = reg (IR x64Syntax.RCX)"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 push_pop_subgoal_rr_aux2_1 shift_subgoal_rr_aux1_1
    by metis
qed

lemma push_pop_subgoal_rr_aux2_3:
  assumes a0:"hd xins = Ppushl_r x64Syntax.RCX" and 
          a1:"last xins = Ppopl x64Syntax.RCX"and
          a2:"interp3 (butlast(tl xins)) (Next reg' m') = Next reg2 m'"and
          a3:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m') " and
          (*a3:"Next reg'' m'' = interp3 xins (Next reg m)" and*)
          a5:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
          a6:"reg' (IR SP) =  reg2 (IR SP)"
  shows "reg'' (IR x64Syntax.RCX) = reg (IR x64Syntax.RCX)"
proof-
  let ?midlist = "butlast(tl xins)"
  have "xins = [Ppushl_r x64Syntax.RCX]@?midlist@[Ppopl x64Syntax.RCX]" using a0 a1
    by (metis append_Cons append_Nil append_butlast_last_id hd_Nil_eq_last instruction.distinct(5787) last_ConsL last_tl list.collapse)
  have b0:"Next reg' m' = exec_push 1 M32 m reg (reg (IR x64Syntax.RCX))" using exec_instr_def a0 
    using exec_push_def a5 a0 
    by (smt (z3) a1 hd_Nil_eq_last hd_conv_nth instruction.distinct(5787) instruction.simps(6295))
  (*then obtain reg' m' where b0:"Next reg' m' = exec_push 1 M32 m reg (reg (IR x64Syntax.RCX))" by blast*)
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
  have b5:"interp3 (butlast(xins)) (Next reg m) = Next reg2 m'" using a2 a5 
    by (smt (verit) Cons_eq_appendI \<open>(xins::instruction list) = [Ppushl_r ireg.RCX] @ butlast (tl xins) @ [Ppopl ireg.RCX]\<close> a0 butlast_append hd_conv_nth interp3.elims list.distinct(1) list.inject list.sel(3) outcome.simps(4))
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

lemma hh1: assumes a0:"Next reg'' m'' = interp3 xins (Next reg m)" and
  a1:"length xins \<ge> (2::nat)"
shows" \<exists> reg' m'. Next reg' m' = interp3 (butlast xins) (Next reg m) \<and> Next reg'' m'' = (exec_instr (last xins) 1 reg' m')   "
  sorry


(*lemma hh2: assumes a0:"Next reg'' m'' = interp3 xins (Next reg m)" and
  a1:"length xins \<ge> (2::nat)" and
  a2:"length xins \<ge> (2::nat)"
shows" \<exists> reg' m'. Next reg' m' = interp3 (butlast xins) (Next reg m) \<and> Next reg'' m'' = (exec_instr (last xins) 1 reg' m')   "
  sorry
*)


lemma hh2:
  assumes a0:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src),Pshlq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and
    a2:"Next reg' m' = (exec_instr (xins!0) 1 reg m)"
  shows "\<exists> reg2 m2. interp3 (butlast(tl xins)) (Next reg' m') = Next reg2 m2"
  sorry



lemma shift_subgoal_rr_aux4_1:
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
  have b2:"\<exists> reg2 m2. interp3 ?midlist (Next reg' m') = Next reg2 m2" using hh2 b1 a0 a1 
    by (smt (verit) One_nat_def Suc_eq_plus1 Suc_leI Suc_le_mono b0 butlast.simps(2) exec_instr_def hh1 instruction.case(60) interp3.elims interp3.simps(2) list.distinct(1) list.sel(1) list.size(3) list.size(4) nat_1_add_1 nth_Cons_0 numeral_2_eq_2 outcome.simps(4) zero_less_Suc)
  then obtain reg2 m2 where b3:"interp3 ?midlist (Next reg' m') = Next reg2 m2" by auto
  have b4:"m2 = m'" using shift_subgoal_rr_aux2 by (metis b3)
  have b5:"reg' (IR SP) =  reg2 (IR SP)" using shift_subgoal_rr_aux3 b3 by metis
  have b6:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " using a0 by (simp add: b0 exec_instr_def)
  have b7_1:"length xins \<ge> (2::nat)" using a0 by simp
  have b7_2:"Next reg2 m2 = interp3 (butlast xins) (Next reg m)" using b3 b0 a0 by (simp add: b6)
  have b7:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m2)" using hh1 b7_1 b7_2 by (metis a1 outcome.inject)
  have b8:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m')" using b7 b4 by simp
  thus ?thesis using a3 a4 b4 b5 b6 b8 a1 push_pop_subgoal_rr_aux2_3
    by (metis a0 b3 butlast.simps(2) list.distinct(1) list.sel(3))
qed



lemma shift_subgoal_rr_aux4_2:"xins = Pmovq_rr (x64Syntax.RCX) src \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r . r \<noteq> x64Syntax.RCX \<longrightarrow> reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def)
  by auto

lemma  shift_subgoal_rr_aux4_3:"xins = Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src) \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r. bpf_to_x64_reg r \<noteq> x64Syntax.RCX \<longrightarrow> reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def)
  by simp

lemma shift_subgoal_rr_aux4_4:"xins = Pshlq_r dst \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r . r \<noteq> dst \<longrightarrow> reg' (IR r) = reg (IR r)"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def)
  by auto

lemma  shift_subgoal_rr_aux4_5:"xins = Pshlq_r (bpf_to_x64_reg dst) \<Longrightarrow> 
    Next reg' m' = (exec_instr xins 1 reg m)\<Longrightarrow> 
    \<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def)
  by simp

lemma shift_subgoal_rr_aux4_6:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src),Pshlq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX] \<Longrightarrow> 
    Next reg'' m'' = interp3 xins (Next reg m) \<Longrightarrow> 
    \<forall> r . r \<notin> {(bpf_to_x64_reg dst), x64Syntax.RCX} \<longrightarrow> reg'' (IR r) = reg (IR r)"
  using shift_subgoal_rr_aux4_5 shift_subgoal_rr_aux4_3 shift_subgoal_rr_aux1_1 sorry

lemma shift_subgoal_rr_aux4:
  assumes a0:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src) ,Pshlq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX] " and
    a1:"Next reg'' m'' = interp3 xins (Next reg m) " 
  shows" \<forall> r \<noteq> dst. reg'' (IR  (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
proof-
  have b0:"reg'' (IR x64Syntax.RCX) = reg (IR x64Syntax.RCX)" using a0 a1 shift_subgoal_rr_aux4_1 by simp
  have b1:"\<forall> r . r \<notin> {(bpf_to_x64_reg dst), x64Syntax.RCX} \<longrightarrow> reg'' (IR r) = reg (IR r)" using shift_subgoal_rr_aux4_6 a0 a1 by simp
  have b2:"\<forall> r . r \<noteq> (bpf_to_x64_reg dst) \<longrightarrow> reg'' (IR r) = reg (IR r)" using b0 b1 by auto
  thus ?thesis using b2 by simp
qed

lemma shift_subgoal_rr_aux5_1:
     "bins = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow>
     xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX) ri,Pshlq_r rd,Ppopl x64Syntax.RCX] \<Longrightarrow>
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

lemma shift_subgoal_rr_aux5:
  assumes a0:"bins = BPF_ALU64 BPF_LSH dst (SOReg src)" and
     a1:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX) ri,Pshlq_r rd,Ppopl x64Syntax.RCX]" and
     a2:"(BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu" and
     a3:"Next reg' m' = interp3 xins (Next reg m)" and
     a4:"rd = (bpf_to_x64_reg dst)" and
     a5:"ri = (bpf_to_x64_reg src)" and
     a6:"reg (IR rd) = Vlong n1" and
     a7:"reg (IR ri) = Vlong n2" and
     a8:"n1  = rs dst" and
     a9:"n2  = rs src"
     shows "Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
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

value "x64_decodes 0 (Option.the(x64_encodes_suffix ([Pmovq_rr x64Syntax.RAX x64Syntax.RBX,Pnop])))"
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
  have b:"Some bl = x64_encodes_suffix [Ppushl_r x64Syntax.RCX, Pmovq_rr(x64Syntax.RCX) (bpf_to_x64_reg src),Pshlq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" 
    using a0 a1 a7 per_jit_shift_reg64_def by simp
  moreover have b0:"xins = [Ppushl_r x64Syntax.RCX, Pmovq_rr (x64Syntax.RCX)(bpf_to_x64_reg src),Pshlq_r (bpf_to_x64_reg dst),Ppopl x64Syntax.RCX]" 
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



 
  

end
