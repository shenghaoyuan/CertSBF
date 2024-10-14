theory bpfConsistencyAux5
  imports Main Interpreter x64Semantics 
  x64Assembler x64DecodeProof Mem JITCommType
begin
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

qed



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


(*lemma test1:
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
*)


(*apply(unfold exec_instr_def)
  apply(cases xins,simp_all)
  subgoal for x31a apply(cases "divmod64u (tmpreg (IR ireg.RDX)) (tmpreg (IR ireg.RAX)) (tmpreg (IR (bpf_to_x64_reg src))) ", simp_all)
    subgoal for a apply(unfold Let_def nextinstr_nf_def nextinstr_def)
      apply(cases a,simp_all)
     subgoal for aa b apply(cases b, simp_all)
           apply(cases aa,simp_all)
       subgoal for x4 apply(cases b, simp_all)
         apply(cases aa,simp_all)
         done
       subgoal for x3 apply(cases aa, simp_all)
         done
subgoal for x4 apply(cases aa,simp_all)
  done
subgoal for x5 apply(cases aa, simp_all)
  subgoal for x5a 
    apply(unfold divmod64u_def add64_def Let_def)
    apply(cases "tmpreg RIP",simp_all)
    apply(cases "tmpreg (IR ireg.RDX)",simp_all)
subgoal for x5b apply(cases "tmpreg (IR ireg.RAX)",simp_all)
   subgoal for x5c apply(cases "tmpreg (IR (bpf_to_x64_reg src))",simp_all)
     subgoal for x5d apply(split if_splits) sorry
     done
   done
  done*)

(*lemma div_subgoal_rr_aux8_9:
  assumes a0:"last xins = Pdivq_r (bpf_to_x64_reg src)"and
          a1:"interp3 (butlast xins) (Next reg m) = Next reg' m'"and
          a2:"Next reg'' m'' = (exec_instr (last xins) 1 reg' m') " and
          a4:"reg' (IR x64Syntax.RAX) =  reg (IR x64Syntax.RAX)" and
          a6:"reg' (IR x64Syntax.RDX) = Vlong 0" and
          a8:"reg (IR x64Syntax.RAX) = Vlong n1" and 
          a7:"reg' (IR x64Syntax.RAX) =  tmpreg (IR x64Syntax.RAX) \<and> 
              reg' (IR (bpf_to_x64_reg src)) =  tmpreg (IR (bpf_to_x64_reg src)) \<and> 
              tmpreg (IR x64Syntax.RDX) = Vlong 0" and
          a5:"Next tmpreg' mem'' = (exec_instr (last xins) 1 tmpreg mem')" and
          a9:"reg' (IR (bpf_to_x64_reg src))= Vlong n2" 
        shows "reg'' (IR x64Syntax.RAX) = tmpreg' (IR x64Syntax.RAX)"
proof-
  have b0:"reg'' (IR ireg.RAX) = Vlong (ucast (((ucast n1)::u128) div ((ucast n2)::u128)))" using div_subgoal_rr_aux8_3 a0 a6 a8 a9 by (metis a2 a4)
  have b1_1:"reg' (IR x64Syntax.RAX) = Vlong n1" using a4 a8 by simp
  have b1_2:"reg' (IR x64Syntax.RAX) =  tmpreg (IR x64Syntax.RAX)" using a7 by simp
  have b1_3:"reg' (IR (bpf_to_x64_reg src)) =  tmpreg (IR (bpf_to_x64_reg src))" using a7 by simp
  have b1_4:"tmpreg (IR x64Syntax.RDX) = Vlong 0" using a7 by simp
  have b1:"tmpreg' (IR ireg.RAX) = Vlong (ucast (((ucast n1)::u128) div ((ucast n2)::u128)))" 
    using b1_1 a2 div_subgoal_rr_aux8_3 a0 local.b0 b1_2 b1_3 b1_4  by (metis a5 a9)
thus ?thesis using b0 b1 by simp
qed*)

(*
lemma mod_subgoal_rr_aux100_1:
    "bins = BPF_ALU64 BPF_MOD dst (SOReg src) \<Longrightarrow> 
    xins = Pmodq_r ri \<Longrightarrow>
    (BPF_OK pc rs' mem' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow> 
    Next reg' m' = exec_instr xins 1 reg m \<Longrightarrow>
    x64Syntax.RDX = (bpf_to_x64_reg dst) \<Longrightarrow> 
    ri = (bpf_to_x64_reg src) \<Longrightarrow> 
    reg (IR x64Syntax.RDX) = Vlong n1 \<Longrightarrow> 
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

lemma modq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_MOD dst (SOReg src)" and
       a1:"per_jit_div_and_mod_reg64 False dst src = Some bl" and
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
*)
(*
lemma div_subgoal_rr_aux8_9:
  assumes a0:"last xins = Pdivq_r (bpf_to_x64_reg src)"and
          a1:"interp3 (butlast xins) (Next reg m) = Next reg' m'"and
          a2:"Next reg'' m'' = (exec_instr (last xins) 1 reg' m') " and
          a3:"reg' (IR x64Syntax.RDX) = Vlong 0" and
          a4:"reg' (IR x64Syntax.RAX) =  reg (IR x64Syntax.RAX)" and
          a5:"Next tmpreg' mem' = exec_instr (last xins) 1 tmpreg mem" and
          a6: "tmpreg (IR x64Syntax.RDX) = Vlong 0" and
          a7:"tmpreg (IR x64Syntax.RAX) = reg (IR x64Syntax.RAX)" and
          a8:"tmpreg (IR x64Syntax.RAX) = Vlong n1" and 
          a9:"tmpreg (IR (bpf_to_x64_reg src)) = Vlong n2" and 
          a10:"reg' (IR (bpf_to_x64_reg src)) = Vlong n2" 
        shows "reg'' (IR x64Syntax.RAX) = tmpreg' (IR x64Syntax.RAX)"
proof-
  have b0:"tmpreg' (IR ireg.RAX) = Vlong (ucast (((ucast n1)::u128) div ((ucast n2)::u128)))" using div_subgoal_rr_aux8_3 a0 a5 a6 a8 a9 by auto
  have b1_1:"reg' (IR x64Syntax.RAX) = Vlong n1" using a4 a7 a8 by simp
  have b1:"reg'' (IR ireg.RAX) = Vlong (ucast (((ucast n1)::u128) div ((ucast n2)::u128)))" 
    using b1_1 a2 div_subgoal_rr_aux8_3 a0 a5 a3 a10 by blast
thus ?thesis using b0 b1 by simp
qed

*)
(*lemma div_subgoal_rr_aux8_10:
  assumes a0:"xins = [Ppushl_r x64Syntax.RDX, Pxorq_rr x64Syntax.RDX x64Syntax.RDX,Pdivq_r (bpf_to_x64_reg src),Ppopl x64Syntax.RDX]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and
    a2:"Next tmpreg' mem' = exec_instr xins2 1 tmpreg mem" and
    a3:"xins2 = Pdivq_r (bpf_to_x64_reg src)" and
    a4:"reg (IR x64Syntax.RDX)  = Vlong 0" and
    a5:"reg (IR (bpf_to_x64_reg src)) = Vlong n2" and
    a6:"reg (IR x64Syntax.RAX) = Vlong n1" 
  shows "tmpreg' (IR x64Syntax.RAX) = reg'' (IR x64Syntax.RAX) "
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
  have b0_4:"reg1 (IR x64Syntax.RDX) = reg (IR x64Syntax.RDX)" using a0 b0_2 div_subgoal_rr_aux2_1
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
  have b1_6:"reg2 (IR x64Syntax.RDX) = Vlong 0" using exec_instr_def a0 div_subgoal_rr_aux8_8 b1_2 b0_4 a4 by simp
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
  (*have b5_2:"reg2 (IR x64Syntax.RDX) = Vlong 0" should be proved*)
  let ?tmplist = "butlast xins"
  have b6_1:"?tmplist = [Ppushl_r x64Syntax.RDX, Pxorq_rr x64Syntax.RDX x64Syntax.RDX,Pdivq_r (bpf_to_x64_reg src)]" using a0 by simp
  have b6_2:"last ?tmplist = Pdivq_r (bpf_to_x64_reg src)" using b6_1 by simp
  have b6_3:"interp3 (butlast ?tmplist) (Next reg m) = Next reg2 m2" using b2_9 b2_2 b2_3 b2_8 by (simp add: b1_3 b1_4)
  have b6_4:"Next reg3 m3 = (exec_instr (last ?tmplist) 1 reg2 m2)" using b2_9 b6_1 by (simp add: b2_2 b2_3 b2_8)
  (*have b6_5:"reg3 (IR x64Syntax.RDX) = reg2 (IR x64Syntax.RDX)" using div_subgoal_rr_aux2_3 using b2_9 b2_2 a0 sorry*)
  have b6_6:"reg2 (IR x64Syntax.RDX) = Vlong 0" using b1_6 by simp
  have b6_7:"reg2 (IR x64Syntax.RAX) = reg (IR x64Syntax.RAX)" using b1 b0 by simp
  (*have b6_8:"\<exists> tmpreg' m'. Next tmpreg' m'' = exec_instr (last ?tmplist) 1 reg m'" sorry
  then obtain tmpreg' m' where b6_9:"Next tmpreg' m'' = exec_instr (last ?tmplist) 1 reg m'" by auto*)
  have b6_10:"reg' (IR (bpf_to_x64_reg src)) = Vlong n2" using a5 div_subgoal_rr_aux2_3 a2 a3 sorry
  have b6_11:"reg (IR x64Syntax.RAX) = reg (IR x64Syntax.RAX)" by simp
  have b6_12:"reg (IR x64Syntax.RDX) = Vlong 0" using a4 by simp
  have b6_13:""
  have b6:" reg' (IR x64Syntax.RAX) = reg3 (IR x64Syntax.RAX)" 
    using b6_1 b6_2 b6_3 b6_4 b6_6 b6_7 b6_10 b6_11 a0 a2 a3 a4 a5 b6_12 div_subgoal_rr_aux8_9 a6 try
  have b5:" reg' (IR x64Syntax.RAX) = reg3 (IR x64Syntax.RAX)" using b5_1 a0 a1 a3 a2 div_subgoal_rr_aux8_4 b0_1 b1_2 b2_2 using b0_4 a4 by blast
  thus ?thesis using b5 b4 by auto
qed
*)
(*lemma div_subgoal_rr_aux8_2:
  assumes a0:"xins = [Ppushl_r x64Syntax.RDX, Pxorq_rr x64Syntax.RDX x64Syntax.RDX,Pdivq_r (bpf_to_x64_reg src),Ppopl x64Syntax.RDX]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and
    a2:"Next reg' m' = exec_instr xins2 1 tmpreg tmpm" and
    a3:"xins2 = Pdivq_r (bpf_to_x64_reg src)" and
    a4:"reg (IR x64Syntax.RDX)  = Vlong 0" and
    a5:"reg (IR (bpf_to_x64_reg src)) = Vlong n2" and
    a6:"reg (IR x64Syntax.RAX) = Vlong n1" 
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
  have b0_4:"reg1 (IR x64Syntax.RDX) = reg (IR x64Syntax.RDX)" using a0 b0_2 div_subgoal_rr_aux2_1
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
  have b1_6:"reg2 (IR x64Syntax.RDX) = Vlong 0" using exec_instr_def a0 div_subgoal_rr_aux8_8 b1_2 b0_4 a4 by simp
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
  (*have b5_2:"reg2 (IR x64Syntax.RDX) = Vlong 0" should be proved*)
  let ?tmplist = "butlast xins"
  have b6_1:"?tmplist = [Ppushl_r x64Syntax.RDX, Pxorq_rr x64Syntax.RDX x64Syntax.RDX,Pdivq_r (bpf_to_x64_reg src)]" using a0 by simp
  have b6_2:"last ?tmplist = Pdivq_r (bpf_to_x64_reg src)" using b6_1 by simp
  have b6_3:"interp3 (butlast ?tmplist) (Next reg m) = Next reg2 m2" using b2_9 b2_2 b2_3 b2_8 by (simp add: b1_3 b1_4)
  have b6_4:"Next reg3 m3 = (exec_instr (last ?tmplist) 1 reg2 m2)" using b2_9 b6_1 by (simp add: b2_2 b2_3 b2_8)
  (*have b6_5:"reg3 (IR x64Syntax.RDX) = reg2 (IR x64Syntax.RDX)" using div_subgoal_rr_aux2_3 using b2_9 b2_2 a0 sorry*)
  have b6_6:"reg2 (IR x64Syntax.RDX) = Vlong 0" using b1_6 by simp
  have b6_7:"reg2 (IR x64Syntax.RAX) = reg (IR x64Syntax.RAX)" using b1 b0 by simp
  (*have b6_8:"\<exists> tmpreg' m'. Next tmpreg' m'' = exec_instr (last ?tmplist) 1 reg m'" sorry
  then obtain tmpreg' m' where b6_9:"Next tmpreg' m'' = exec_instr (last ?tmplist) 1 reg m'" by auto*)
  have b6_10:"reg' (IR (bpf_to_x64_reg src)) = Vlong n2" using a5 div_subgoal_rr_aux2_3 a2 a3 sorry
  have b6_11:"reg (IR x64Syntax.RAX) = reg (IR x64Syntax.RAX)" by simp
  have b6_12:"reg (IR x64Syntax.RDX) = Vlong 0" using a4 by simp
  have b6:" reg' (IR x64Syntax.RAX) = reg3 (IR x64Syntax.RAX)" 
    using b6_1 b6_2 b6_3 b6_4 b6_6 b6_7 b6_10 b6_11 a0 a2 a3 a4 a5 b6_12 div_subgoal_rr_aux8_9 a6
  have b5:" reg' (IR x64Syntax.RAX) = reg3 (IR x64Syntax.RAX)" using b5_1 a0 a1 a3 a2 div_subgoal_rr_aux8_4 b0_1 b1_2 b2_2 using b0_4 a4 by blast
  thus ?thesis using b5 b4 by auto
qed
*)



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



(*lemma div_subgoal_rr_aux100:
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
    have b3:"Vlong (rs' dst)  =  reg' (IR x64Syntax.RAX)" using div_subgoal_rr_aux8_10 b0 a3 b3_0 b1 a1 by metis
    thus ?thesis using a4 by simp
qed*)



(*lemma sar_subgoal_rr_aux5_1:
     "bins = BPF_ALU64 BPF_ARSH dst (SOReg src) \<Longrightarrow>
     xins = Pshrq_r rd \<Longrightarrow>
     (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
     Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
     rd = (bpf_to_x64_reg dst) \<Longrightarrow>
     x64Syntax.RCX = (bpf_to_x64_reg src) \<Longrightarrow>
     reg (IR rd) = Vlong n1 \<Longrightarrow>
     reg (IR ri) = Vlong n2 \<Longrightarrow>
     n1  = rs dst \<Longrightarrow>
     n2  = rs src \<Longrightarrow> 
     Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
  apply(unfold exec_instr_def)
  apply(cases xins,simp_all)
  subgoal for x46 apply(cases is_v1,simp_all)
     apply(cases "eval_alu64 BPF_ARSH dst (SOReg src) rs enable_instruction_meter",simp_all)
     apply(unfold nextinstr_nf_def nextinstr_def add64_def shl64_def eval_alu64_def,simp_all)
     apply(cases "reg (IR ireg.RCX)",simp_all)
         apply(unfold eval_alu64_aux2_def Let_def eval_reg_def)
         apply(cases BPF_ARSH,simp_all)
         apply(cases "reg RIP",simp_all)
    sorry
  done
*)


(*lemma shr_subgoal_rr_aux5_1:
     "bins = BPF_ALU64 BPF_RSH dst (SOReg src) \<Longrightarrow>
     xins = Pshrq_r rd \<Longrightarrow>
     (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
     Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
     rd = (bpf_to_x64_reg dst) \<Longrightarrow>
     x64Syntax.RCX = (bpf_to_x64_reg src) \<Longrightarrow>
     reg (IR rd) = Vlong n1 \<Longrightarrow>
     reg (IR ri) = Vlong n2 \<Longrightarrow>
     n1  = rs dst \<Longrightarrow>
     n2  = rs src \<Longrightarrow> 
     Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
  apply(unfold exec_instr_def)
  apply(cases xins,simp_all)
  subgoal for x46 apply(cases is_v1,simp_all)
     apply(cases "eval_alu64 BPF_RSH dst (SOReg src) rs enable_instruction_meter",simp_all)
     apply(unfold nextinstr_nf_def nextinstr_def add64_def shl64_def eval_alu64_def,simp_all)
     apply(cases "reg (IR ireg.RCX)",simp_all)
         apply(unfold eval_alu64_aux2_def Let_def eval_reg_def)
         apply(cases BPF_RSH,simp_all)
         apply(cases "reg RIP",simp_all)
    sorry
  done
*)

(*lemma shl_subgoal_rr_aux5_1:
     "bins = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow>
     xins = Pshlq_r rd \<Longrightarrow>
     (BPF_OK pc rs' m' ss' is_v1 (cur_cu+1) remain_cu) = step fuel bins rs m ss is_v1 cur_cu remain_cu \<Longrightarrow>
     Next reg' m' = exec_instr xins sz reg m \<Longrightarrow>
     rd = (bpf_to_x64_reg dst) \<Longrightarrow>
     x64Syntax.RCX = (bpf_to_x64_reg src) \<Longrightarrow>
     reg (IR rd) = Vlong n1 \<Longrightarrow>
     reg (IR ri) = Vlong n2 \<Longrightarrow>
     n1  = rs dst \<Longrightarrow>
     n2  = rs src \<Longrightarrow> 
     Vlong (rs' dst) = reg' (IR (bpf_to_x64_reg dst))"
  apply(unfold exec_instr_def)
  apply(cases xins,simp_all)
  subgoal for x46 apply(cases is_v1,simp_all)
     apply(cases "eval_alu64 BPF_LSH dst (SOReg src) rs enable_instruction_meter",simp_all)
     apply(unfold nextinstr_nf_def nextinstr_def add64_def shl64_def eval_alu64_def,simp_all)
     apply(cases "reg (IR ireg.RCX)",simp_all)
         apply(unfold eval_alu64_aux2_def Let_def eval_reg_def)
         apply(cases BPF_LSH,simp_all)
         apply(cases "reg RIP",simp_all)
    sorry
  done
 *)
end