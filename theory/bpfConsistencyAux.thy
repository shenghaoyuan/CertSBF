theory bpfConsistencyAux
  imports Main Interpreter x64Semantics 
  x64Assembler x64DecodeProof Mem
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

lemma bpf_to_x64_reg_corr[simp]:" r1 \<noteq> r2 \<longrightarrow> bpf_to_x64_reg r1 \<noteq> bpf_to_x64_reg r2 "
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

lemma load_subgoal_aux1:
      "bins = BPF_LDX chk dst src (b_off::i16) \<Longrightarrow>
       xins = Pmov_mr (Addrmode (Some ri) None (x_off::u32)) rd chk \<Longrightarrow>
       rd = (bpf_to_x64_reg dst)\<Longrightarrow>
       ri = (bpf_to_x64_reg src) \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       reg (IR ri) = Vlong n2 \<Longrightarrow>
       n1  = rs (BR dst) \<Longrightarrow>
       n2  = rs (BR src) \<Longrightarrow>
       (BPF_OK rs' mem' ss' conf is_v1) = step conf bins rs mem ss is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       m = mem \<Longrightarrow>
       m' = mem'"
  apply (unfold exec_instr_def step)
  apply(cases xins)
  apply simp_all
  apply (unfold eval_load_def Let_def cast_lemma5, simp_all)
  apply (simp add: exec_load_def eval_addrmode64_def add64_def nextinstr_nf_def nextinstr_def)
  by (metis (mono_tags, lifting) bpf_state.distinct(1) bpf_state.inject option.case_eq_if outcome.distinct(1) outcome.inject)

lemma load_subgoal_aux2_1:
  assumes a0:"bins = BPF_LDX chk dst src b_off" and 
          a1:"step conf bins rs mem ss is_v1 = result"
        shows "result = (BPF_OK rs' mem' ss' conf is_v1) \<longrightarrow> Mem.loadv chk mem (Vlong (eval_snd_op_u64 (SOReg src) rs + scast b_off)) \<noteq> Some Vundef"
proof (rule ccontr)
  assume a2:"\<not> (result = (BPF_OK rs' mem' ss' conf is_v1) \<longrightarrow> (Mem.loadv chk mem (Vlong (eval_snd_op_u64 (SOReg src) rs + scast b_off)) \<noteq> Some Vundef))"
  let ?x = "eval_snd_op_u64 (SOReg src) rs + scast b_off"
  let ?tmp = "Mem.loadv chk mem (Vlong ?x)"
  let ?res_ok = "(BPF_OK rs' mem' ss' conf is_v1)"
  have a3:"\<not> (\<not> result = ?res_ok \<or> (?tmp \<noteq> Some Vundef))" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Some Vundef" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Some Vundef" using a4 conjE by simp
     have b1:"eval_load chk dst src b_off rs mem = None"  using eval_load_def b0 by simp
     have b2: "step conf bins rs mem ss is_v1 = BPF_EFlag"using a0 b1 eval_load_def by simp
     thus "False" using b2 
       by (metis a1 a2 bpf_state.simps(3))
   qed
 qed

lemma load_subgoal_aux2_2:
  assumes a0:"bins = BPF_LDX chk dst src b_off" and 
          a1:"step conf bins rs mem ss is_v1 = result"
        shows "result = (BPF_OK rs' mem' ss' conf is_v1) \<longrightarrow> Mem.loadv chk mem (Vlong (eval_snd_op_u64 (SOReg src) rs + scast b_off)) \<noteq> None"
proof (rule ccontr)
  assume a2:"\<not> (result = (BPF_OK rs' mem' ss' conf is_v1) \<longrightarrow> (Mem.loadv chk mem (Vlong (eval_snd_op_u64 (SOReg src) rs + scast b_off)) \<noteq> None))"
  let ?x = "eval_snd_op_u64 (SOReg src) rs + scast b_off"
  let ?tmp = "Mem.loadv chk mem (Vlong ?x)"
  let ?res_ok = "(BPF_OK rs' mem' ss' conf is_v1)"
  have a3:"\<not> (\<not> result = ?res_ok \<or> (?tmp \<noteq> None))" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = None" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = None" using a4 conjE by simp
     have b1:"eval_load chk dst src b_off rs mem = None"  using eval_load_def b0 by simp
     have b2: "step conf bins rs mem ss is_v1 = BPF_EFlag"using a0 b1 eval_load_def by simp
     thus "False" using b2 
       by (metis a1 a2 bpf_state.simps(3))
   qed
 qed

lemma load_subgoal_aux2_3:
  assumes a0:"bins = BPF_LDX chk dst src b_off" and 
          a1:"step conf bins rs mem ss is_v1 = result"
        shows "result = (BPF_OK rs' mem' ss' conf is_v1) \<longrightarrow> Mem.loadv chk mem (Vlong (eval_snd_op_u64 (SOReg src) rs + scast b_off)) \<notin> {None, Some Vundef} "
  using load_subgoal_aux2_1 load_subgoal_aux2_2 a0 a1 by auto

lemma load_subgoal_aux2_4:
  assumes a0:"bins = BPF_LDX chk dst src b_off" and 
          a1:"step conf bins rs mem ss is_v1 = result"
        shows "result = (BPF_OK rs' mem' ss' conf is_v1) \<longrightarrow> eval_load chk dst src b_off rs mem \<noteq> None"
proof (rule ccontr)
  assume a2:"\<not> (result = (BPF_OK rs' mem' ss' conf is_v1) \<longrightarrow> eval_load chk dst src b_off rs mem \<noteq> None)"
  let ?res_ok = "(BPF_OK rs' mem' ss' conf is_v1)"
  have a3:"\<not> (\<not> result = ?res_ok \<or> (eval_load chk dst src b_off rs mem \<noteq> None))" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> (eval_load chk dst src b_off rs mem = None)" using a3 by simp
   then show "False"
   proof
     have b1:"eval_load chk dst src b_off rs mem = None" using a4 conjE by simp
     have b2: "step conf bins rs mem ss is_v1 = BPF_EFlag"using a0 b1 eval_load_def by simp
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
       n1  = rs (BR dst) \<Longrightarrow>
       n2  = rs (BR src) \<Longrightarrow>
       b_off = scast x_off \<Longrightarrow>
       (BPF_OK rs' mem' ss' conf is_v1) = step conf bins rs mem ss is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       m = mem \<Longrightarrow>
       Mem.loadv chk mem (Vlong (eval_snd_op_u64 (SOReg src) rs + scast (scast b_off)))\<noteq> None \<Longrightarrow>
       scast x_off = scast (scast x_off) \<Longrightarrow>
       Vlong (rs' (BR dst)) = reg' (IR (bpf_to_x64_reg dst))"
  apply (unfold exec_instr_def step)
  apply(cases xins)
  apply simp_all
  apply (unfold eval_load_def Let_def cast_lemma5, simp_all)
apply (simp add: exec_load_def)
  apply (simp add: exec_load_def eval_addrmode64_def add64_def nextinstr_nf_def nextinstr_def)
  apply (cases "loadv chk mem (Vlong (rs (BR src) + scast x_off))")
   apply simp
  apply (cases "loadv chk mem (Vlong (rs (BR src) + scast (scast x_off)))")
  apply simp_all
  using cast_lemma5  load_subgoal_aux2_1
*)


lemma load_subgoal_rr_aux2:
  assumes a0:"bins = BPF_LDX chk dst src b_off" and
       a1:"xins = Pmov_mr (Addrmode (Some ri) None x_off) rd chk" and
       a2:"rd = (bpf_to_x64_reg dst)" and
       a3:"ri = (bpf_to_x64_reg src)" and
       a4:"reg (IR rd) = Vlong n1" and
       a5:"reg (IR ri) = Vlong n2" and
       a6:"n1 = rs (BR dst)" and
       a7:"n2 = rs (BR src)" and
       a8:"x_off = ucast b_off " and
       a9:"(BPF_OK rs' mem' ss conf is_v1) = step conf bins rs mem ss is_v1" and
       a10:"Next reg' m' = exec_instr xins sz reg m" and
       a11:"m = mem" 
       shows "Vlong (rs' (BR dst)) = reg' (IR (bpf_to_x64_reg dst))"
proof-
  let ?t = "Addrmode (Some (bpf_to_x64_reg src)) None x_off"
  have "xins = Pmov_mr ?t rd chk" using Orderings.ord.ord_less_eq_trans Extraction.exE_realizer a0 apply simp
    using a1 a3 by fastforce
  let ?x = "eval_snd_op_u64 (SOReg src) rs + scast b_off"
  let ?tmp = "Mem.loadv chk mem (Vlong ?x)"
  have b0:"step conf bins rs mem ss is_v1 = (BPF_OK rs' mem' ss conf is_v1) \<longrightarrow> ?tmp \<noteq> None" 
    using load_subgoal_aux2_2 using a0 a11 by blast
  have b1:"?tmp \<noteq> None" using b0 a9 by simp
  have b2:"Next reg' m' = exec_load sz chk m ?t reg (IR (bpf_to_x64_reg dst))" using exec_instr_def a1 apply (cases "xins") 
                        apply blast apply simp_all by (simp add: a10 a2 a3)
  have b3:"Next reg' m' = (case loadv chk m (eval_addrmode64 (?t) reg) 
           of None \<Rightarrow> Stuck | Some (v::val) \<Rightarrow> Next (nextinstr_nf sz (reg(IR (bpf_to_x64_reg dst) := v))) m) "
    using exec_load_def by (simp add: b2)
  have b4:"Next reg' m' = (case loadv chk m (Vlong (rs (BR src) + scast x_off)) of None \<Rightarrow> Stuck
        | Some (v::val) \<Rightarrow> Next (nextinstr_nf sz (reg(IR (bpf_to_x64_reg dst) := v))) m)"
    using eval_addrmode64_def b3 add64_def nextinstr_nf_def using a3 a5 a7 by force
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
  have c1_1:"(Option.the(?rss') (BR dst)) = v1" using a0 a9 the_def eval_load_def Let_def 
    using \<open>loadv (chk) (mem) (Vlong (eval_snd_op_u64 (SOReg (src)) (rs) + scast (b_off))) = Some (Vlong (v1))\<close> by force
  fix v2 assume "?tmp = Some(Vint v2)" 
  have c1_2:"(Option.the(?rss') (BR dst)) = ucast v2" using a0 a9 the_def eval_load_def Let_def 
    using \<open>loadv (chk) (mem) (Vlong (eval_snd_op_u64 (SOReg (src)) (rs) + scast (b_off))) = Some (Vint (v2))\<close> by force
  fix v3 assume "?tmp = None" 
 *)
  have c1:"Vlong ((Option.the(?rss') (BR dst))) = Option.the(?tmp)" (*using a0 a9 the_def eval_load_def Let_def c0 cast_lemma6*)
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
  have c2:" (BPF_OK rs' mem' ss conf is_v1) = (BPF_OK ((Option.the(?rss'))#BPC <-- (1+ (Option.the(?rss') BPC))) mem ss conf is_v1) " 
    using c0 Let_def a9 a0 by auto
  have c3:"Option.the(?rss')(BR dst) = rs' (BR dst)" using the_def c2 by simp
  have c4:"Vlong (rs' (BR dst)) = Option.the(?tmp)" using c3 c1 by simp
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

lemma loadq_subgoal_rr_aux4:"bins = BPF_LDX chk dst src b_off \<Longrightarrow> (BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1 \<Longrightarrow>
       \<forall> r \<noteq> dst. rs' (BR r) = rs (BR r)"
  apply(cases "bins",simp_all)
  apply(unfold eval_load_def,simp)
  apply(cases "loadv chk m (Vlong (rs (BR src) + scast b_off))" ,simp_all)
  subgoal for a apply(cases a)
  by simp_all
  done

definition per_jit_load_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> memory_chunk \<Rightarrow> off_ty \<Rightarrow>x64_bin option" where
"per_jit_load_reg64 dst src chk off = (
  let ins = Pmov_mr (Addrmode (Some (bpf_to_x64_reg src)) None (ucast (off))) (bpf_to_x64_reg dst) chk in
    x64_encode ins
)"

lemma loadq_subgoal_rr_generic:
  assumes a0:"bins = BPF_LDX chk dst src b_off" and
       a1:"per_jit_load_reg64 dst src chk b_off = Some bl" and
       a2:"list_in_list bl pc l_bin" and
       a3:"x64_decode pc l_bin = Some (length l_bin, xins)" and
       a4:"(BPF_OK rs' mem' ss' conf is_v1) = step conf bins rs mem ss is_v1" and
       a5:"Next reg' m'  = exec_instr xins sz reg m" and
       a6:"(\<forall> r. Vlong (rs (BR r)) = reg (IR (bpf_to_x64_reg r)))" and
       a7:"m = mem"
  shows "(\<forall> r. Vlong (rs' (BR r)) = reg' (IR (bpf_to_x64_reg r)))"
proof -
  have b0:"xins = Pmov_mr (Addrmode (Some (bpf_to_x64_reg src)) None (ucast (b_off))) (bpf_to_x64_reg dst) chk" using x64_encode_decode_consistency per_jit_load_reg64_def a1 a2 a3 by fastforce
    moreover have b1:"Vlong (rs (BR dst)) = reg (IR (bpf_to_x64_reg dst))" using a6 spec by simp
    moreover have b2:"Vlong (rs (BR src)) = reg (IR (bpf_to_x64_reg src))" using a6 spec by simp
    hence b3:"Vlong (rs' (BR dst)) = reg' (IR (bpf_to_x64_reg dst))" using load_subgoal_rr_aux2 b0 b1 b2 a0 a1 a2 a3 a4 a5 a6 a7 sorry
    have b4:"\<forall> r \<noteq> dst. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 loadq_subgoal_rr_aux3 by blast
    have b5:"\<forall> r \<noteq> dst. Vlong (rs'(BR r)) = Vlong (rs (BR r))" using a0 a4 loadq_subgoal_rr_aux4 by blast
    have b6:"\<forall> r \<noteq> dst. Vlong (rs (BR r)) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r \<noteq> dst. Vlong (rs' (BR r)) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
    thus ?thesis using b3 by fastforce
  qed

(*lemma store_subgoal_aux1:
      "bins = BPF_ST chk dst (SOReg src) (b_off::i16) \<Longrightarrow>
       xins = Pmov_rm ri (Addrmode (Some rd) None (x_off::u32)) chk \<Longrightarrow>
       rd = (bpf_to_x64_reg dst)\<Longrightarrow>
       ri = (bpf_to_x64_reg src) \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       reg (IR ri) = Vlong n2 \<Longrightarrow>
       n1  = rs (BR dst) \<Longrightarrow>
       n2  = rs (BR src) \<Longrightarrow>
       (BPF_OK rs' mem' ss' conf is_v1) = step conf bins rs mem ss is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       m = mem \<Longrightarrow>
       scast x_off = scast (scast x_off) \<Longrightarrow>
       m' = mem'"
  apply (unfold exec_instr_def step)
  apply(cases xins)
  apply simp_all
  apply (unfold eval_store_def Let_def cast_lemma5, simp_all)
  apply (simp add: exec_store_def eval_addrmode64_def add64_def nextinstr_nf_def nextinstr_def)
  

lemma store_subgoal_aux1:
      "bins = BPF_ST chk dst (SOReg src) (b_off::i16) \<Longrightarrow>
       xins = Pmov_rm ri (Addrmode (Some rd) None (x_off::u32)) chk \<Longrightarrow>
       rd = (bpf_to_x64_reg dst)\<Longrightarrow>
       ri = (bpf_to_x64_reg src) \<Longrightarrow>
       reg (IR rd) = Vlong n1 \<Longrightarrow>
       reg (IR ri) = Vlong n2 \<Longrightarrow>
       n1  = rs (BR dst) \<Longrightarrow>
       n2  = rs (BR src) \<Longrightarrow>
       (BPF_OK rs' mem' ss' conf is_v1) = step conf bins rs mem ss is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       m = mem \<Longrightarrow>
       scast x_off = scast (scast x_off) \<Longrightarrow>
      Vlong (rs' (BR dst)) = reg' (IR (bpf_to_x64_reg dst))"
  apply (unfold exec_instr_def step)
  apply(cases xins)
  apply simp_all
  apply (unfold eval_store_def Let_def cast_lemma5, simp_all)
  apply (simp add: exec_store_def eval_addrmode64_def add64_def nextinstr_nf_def nextinstr_def)
*) 

lemma subq_subgoal_rr_aux1:
     "bins = BPF_ALU64 BPF_SUB dst (SOReg src) \<Longrightarrow>
     xins = Psubq_rr rd ri \<Longrightarrow>
     (BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1 \<Longrightarrow>
     Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow>
     rd = (bpf_to_x64_reg dst) \<Longrightarrow>
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

lemma subq_subgoal_rr_aux2:"xins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow> Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
       \<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  using bpf_to_x64_reg_corr subq_subgoal_rr_aux2_2 by metis


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

lemma ja_subgoal_aux1:
      "bins = BPF_JA off \<Longrightarrow>
       xins = Pjmp d \<Longrightarrow>
       Vlong (rs (BPC)) = reg PC \<Longrightarrow>
       (BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1 \<Longrightarrow>
       Next reg' m'  = exec_instr xins sz reg m \<Longrightarrow> 
       d = ucast(off::i16)\<Longrightarrow>
      Vlong (rs' (BPC))= reg' PC"
  apply (unfold exec_instr_def step)
  apply simp
  apply (unfold eval_pc_def nextinstr_def add64_def)
  apply(simp_all)
  apply(erule conjE)+
  apply(cases "reg RIP", simp_all)
  using cast_lemma4 by auto

definition per_jit_ja :: "off_ty\<Rightarrow> x64_bin option" where
"per_jit_ja off = (
  let ins = Pjmp (ucast off) in
    x64_encode ins
)"

lemma ja_subgoal_aux2:"xins = Pjmp d \<Longrightarrow> Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
       \<forall> r. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  apply(unfold exec_instr_def, cases "xins", simp_all)
  apply(unfold nextinstr_nf_def nextinstr_def add64_def) 
  by auto

lemma ja_subgoal_aux3:"bins = BPF_JA off \<Longrightarrow> (BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1 \<Longrightarrow>
       \<forall> r. rs' (BR r) = rs (BR r)"
  by(cases "bins",simp_all)

lemma ja_subgoal_generic:
  assumes a0:"bins = BPF_JA off" and
       a1:" per_jit_ja (ucast off) = Some bl" and
       a2:"list_in_list bl pc l_bin" and
       a3:"x64_decode pc l_bin = Some (length l_bin, xins)" and
       a4:"(BPF_OK rs' m' ss' conf is_v1) = step conf bins rs m ss is_v1" and
       a5:"Next reg' m' = exec_instr xins sz reg m" and
       a6:"(\<forall> r. Vlong (rs (BR r)) = reg (IR (bpf_to_x64_reg r))) \<and> Vlong (rs (BPC)) = reg PC" 
  shows "(\<forall> r. Vlong (rs' (BR r)) = reg' (IR (bpf_to_x64_reg r))) \<and> Vlong (rs' (BPC))= reg' PC"
proof -
  have b0:"xins = Pjmp (ucast off)" using x64_encode_decode_consistency per_jit_ja_def a1 a2 a3 by fastforce
  moreover have b1:"Vlong (rs (BPC)) = reg PC" using a6 by simp
  moreover have b2:"(\<forall> r. Vlong (rs (BR r)) = reg (IR (bpf_to_x64_reg r)))" using a6 by simp
    hence b3:"Vlong (rs' (BPC))= reg' PC" using ja_subgoal_aux1 b0 b1 a0 a4 a5 by force
    have b4:"\<forall> r. reg'(IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 b1 a5 ja_subgoal_aux2 by simp
    have b5:"\<forall> r. Vlong (rs'(BR r)) = Vlong (rs (BR r))" using a0 a4 ja_subgoal_aux3 by simp
    have b6:"\<forall> r. Vlong (rs (BR r)) = reg (IR (bpf_to_x64_reg r))" using a6 by blast
    have b7:"(\<forall> r. Vlong (rs' (BR r)) = reg' (IR (bpf_to_x64_reg r)))" by(simp add:b4 b5 b6) 
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
