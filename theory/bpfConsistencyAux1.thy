theory bpfConsistencyAux1
  imports Main Interpreter x64Semantics 
  x64Assembler x64DecodeProof Mem JITCommType
begin

subsection   \<open> BPF_ALU64 list auxs\<close>

lemma add_sub_consistency:"add64 (Vlong a) (Vlong b) = Vlong c \<Longrightarrow> sub64 (Vlong c) (Vlong a) = (Vlong b) "
  using add64_def sub64_def by auto

lemma interp3_list_aux1:
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

lemma interp3_list_aux2:
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


lemma interp3_list_aux3:"interp3 [] (Next reg m) = Next reg m"
  by simp

lemma interp3_length2_aux1: assumes a0:"Next reg2 m2 = interp3 xins (Next reg m)" and
  a1:"length xins = (2::nat)"
shows" \<exists> reg' m'. Next reg' m' = (exec_instr (xins!0) 1 reg m) \<and> Next reg2 m2 = (exec_instr (xins!1) 1 reg' m')  "
proof-
  from a0 a1 have "\<exists> reg' m'. Next reg' m' = (exec_instr (xins!0) 1 reg m)" 
    by (metis interp3_list_aux1 length_0_conv outcome.exhaust zero_neq_numeral)
  then obtain reg' m' where "Next reg' m' = (exec_instr (xins!0) 1 reg m)" by blast
  have "\<exists> reg'' m''. Next reg'' m'' = (exec_instr (xins!1) 1 reg' m')" 
    by (metis \<open>Next (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option) = exec_instr ((xins::instruction list) ! (0::nat)) (1::64 word) (reg::preg \<Rightarrow> val) (m::64 word \<Rightarrow> 8 word option option)\<close> a0 a1 interp3_list_aux2 outcome.exhaust)
  then obtain reg'' m'' where " Next reg'' m'' = (exec_instr (xins!1) 1 reg' m')"
    by auto
  have b4:"Next reg'' m'' = Next reg2 m2" using  a1 interp3_list_aux3
    by (metis One_nat_def \<open>Next (reg''::preg \<Rightarrow> val) (m''::64 word \<Rightarrow> 8 word option option) = exec_instr ((xins::instruction list) ! (1::nat)) (1::64 word) (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option)\<close> \<open>Next (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option) = exec_instr ((xins::instruction list) ! (0::nat)) (1::64 word) (reg::preg \<Rightarrow> val) (m::64 word \<Rightarrow> 8 word option option)\<close> a0 interp3.simps(2) list_consists_2 outcome.simps(4))
  show ?thesis using a0 a1 
    using \<open>Next (reg''::preg \<Rightarrow> val) (m''::64 word \<Rightarrow> 8 word option option) = exec_instr ((xins::instruction list) ! (1::nat)) (1::64 word) (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option)\<close> \<open>Next (reg'::preg \<Rightarrow> val) (m'::64 word \<Rightarrow> 8 word option option) = exec_instr ((xins::instruction list) ! (0::nat)) (1::64 word) (reg::preg \<Rightarrow> val) (m::64 word \<Rightarrow> 8 word option option)\<close> b4 by blast
  qed

lemma interp3_length2_aux2:"Next reg'' m'' = interp3 xins (Next reg m) \<Longrightarrow> length xins = (2::nat) \<Longrightarrow> \<exists> reg' m'. Next reg' m' = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = (exec_instr (xins!1) 1 reg' m')  "
  using interp3_length2_aux1 by simp

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
     have b2_3:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (xins!0) 1 reg m) \<and> Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1 )" using a2 b2_2 b2_1 interp3_length2_aux1 
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

lemma interp3_length4_aux3:
  assumes a0:"length xins = (4::nat)" and 
          a1:"result = interp3 xins (Next reg m)" and
          a2:"Next reg3 m3 = interp3 (butlast xins) (Next reg m)"
        shows "result = Next reg'' m'' \<longrightarrow> (exec_instr (last xins) 1 reg3 m3) \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next reg'' m'' \<longrightarrow> (exec_instr (last xins) 1 reg3 m3) \<noteq> Stuck)"
  let ?tmp = "(exec_instr (last xins) 1 reg3 m3) "
  let ?res_ok = "Next reg'' m''"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1_1:"(last xins) = (xins!3)" using a0 
       by (metis One_nat_def Suc_eq_plus1 Suc_numeral add_2_eq_Suc diff_Suc_1' last_conv_nth length_Suc_conv list.simps(3) list.size(3) list_consists_4 semiring_norm(5))
     have b1_2: "(butlast xins) = [xins!0]@[xins!1]@[xins!2]" using b1_1 a0 
       by (metis One_nat_def append_Cons append_Nil butlast.simps(2) list.simps(3) list_consists_4)
     have b1_3:"length xins >0" using a0 by simp
     let ?tmplist = "(butlast xins)"
     have b2_1:"?tmplist = [(?tmplist!0)]@(tl ?tmplist)" using b1_2 by simp
     have b2_2:"length ?tmplist > 0" using b2_1 by fastforce
     have b2_3:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (xins!0) 1 reg m)" using b1_3 interp3_list_aux1 
       by (metis a1 a4 bot_nat_0.extremum_strict list.size(3) outcome.exhaust)
     have b2_4:"(?tmplist!0) = (xins!0)" using b2_2 nth_butlast by blast
     have b2_5:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (?tmplist!0) 1 reg m) \<and> Next reg3 m3 = interp3 (tl ?tmplist) (Next reg1 m1) " 
       using b2_4 a1 a2 b2_2 b2_1  
       by (metis append.left_neutral append_Cons assms(3) b2_3 interp3.simps(2) outcome.case(1))
     then obtain reg1 m1 where b2_4:" Next reg1 m1 = (exec_instr (?tmplist!0) 1 reg m) \<and> Next reg3 m3 = interp3 (tl ?tmplist) (Next reg1 m1)" by auto
     let ?tmplist2 = "[xins!1]@[xins!2]"
     have b3_0:"length ?tmplist2 = (2::nat)" by simp
     have b3_1:"?tmplist2 = tl ?tmplist" by (simp add: b1_2)
     have b3_2:"Next reg3 m3 = interp3 (?tmplist2) (Next reg1 m1)" using b2_4 b3_1 by simp
     have b3_3:"\<exists> reg2 m2. Next reg2 m2 = (exec_instr (?tmplist2!0) 1 reg1 m1) \<and> Next reg3 m3 = (exec_instr (?tmplist2!1) 1 reg2 m2)" 
       using a2 b2_2 b2_1 interp3_length2_aux1 b3_1 b3_2 b3_0 by blast
     have b2:"(exec_instr (last xins) 1 reg3 m3)  = interp3 (xins) (Next reg m)" using a0 a1 a2 a3 b0 
       by (smt (z3) Suc_eq_plus1 add_2_eq_Suc append_Cons append_Nil b1_2 b2_4 b3_0 b3_1 diff_Suc_1' interp3.simps(2) interp3_list_aux2 interp3_length2_aux1 last_conv_nth last_tl length_0_conv length_Suc_conv list.sel(3) list.simps(3) list.size(3) list_consists_4 nth_Cons_0 outcome.case(1) outcome.inject zero_neq_numeral)
     have b3: "(exec_instr (last xins) 1 reg3 m3)  = Stuck"using a0 b0 exec_instr_def a2
       using interp2.elims nth_Cons_0 outcome.case(2) outcome.simps(4) by auto
     have b4: "interp3 xins (Next reg m) = Stuck" using a0 a1 b3 exec_instr_def a2 
       using b2 by argo
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed

lemma interp3_length4_aux4:
  assumes a0:"length xins = (4::nat)" and 
          a1:"Next reg'' m''= interp3 xins (Next reg m)" 
        shows "\<exists> reg' m'. Next reg' m' = interp3 (take 2 xins) (Next reg m) \<and> Next reg'' m'' = interp3 (drop 2 xins) (Next reg' m')"
proof-
     have b1_1:"(last xins) = (xins!3)" using a0 
       by (metis One_nat_def Suc_eq_plus1 Suc_numeral add_2_eq_Suc diff_Suc_1' last_conv_nth length_Suc_conv list.simps(3) list.size(3) list_consists_4 semiring_norm(5))
     have b1_2: "(butlast xins) = [xins!0]@[xins!1]@[xins!2]" using b1_1 a0 
       by (metis One_nat_def append_Cons append_Nil butlast.simps(2) list.simps(3) list_consists_4)
     have b1_3:"length xins >0" using a0 by simp
     have b2_3:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (xins!0) 1 reg m)" using b1_3 interp3_list_aux1 
       by (metis a1 bot_nat_0.extremum_strict list.size(3) outcome.exhaust)
     have b2_5:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = interp3 (tl xins) (Next reg1 m1) " 
       using a1
       by (metis b1_3 b2_3 interp3.elims length_greater_0_conv list.sel(3) nth_Cons_0 outcome.case(1))
     then obtain reg1 m1 where b2_6:" Next reg1 m1 = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = interp3 (tl xins) (Next reg1 m1)" by auto
     have b3_3:"\<exists> reg2 m2. Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1)"using exec_instr_def a0 
       by (metis (no_types, opaque_lifting) Suc_eq_plus1 add.commute add.right_neutral b2_6 diff_Suc_1' interp3_list_aux1 list.sel(3) list_consists_4 neq_Nil_conv nth_Cons_numeral numeral_eq_one_iff outcome.exhaust)
     then obtain reg2 m2 where b3_4:"Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1)" by auto
     have b4_1:"take 2 xins = [xins!0]@[xins!1]" by (simp add: a0 numeral_2_eq_2 take_Suc_conv_app_nth)
     have b4:"Next reg2 m2 = interp3 (take 2 xins) (Next reg m)" using a0 b3_4 b4_1 b2_6 
       by (metis append_Cons append_Nil interp3.simps(2) interp3_list_aux3 outcome.case(1))
     have b5_1:"[xins!0]@[xins!1] @ (drop 2 xins)= xins" using a0
       by (simp add: Cons_nth_drop_Suc numeral_3_eq_3 numeral_nat(2))
     have b5_2:"interp3 (drop 2 xins) (Next reg2 m2) = interp3 (xins) (Next reg m)" using a0 a1 b5_1 b4
       using append_Cons append_Nil interp3.simps(2) outcome.simps(4) by (metis b2_6 b3_4)
     have b5:"\<exists> reg2 m2. Next reg2 m2 = interp3 (take 2 xins) (Next reg m) \<and> Next reg'' m'' = interp3 (drop 2 xins) (Next reg2 m2)" 
       using b5_2 b4 using a1 by force
     thus ?thesis by fastforce
   qed


lemma interp3_length4_aux6:
  assumes a0:"length xins = (4::nat)" and 
          a1:"Next reg'' m''= interp3 xins (Next reg m)" 
        shows "\<exists> reg' m'. Next reg' m' = interp3 (butlast xins) (Next reg m) \<and> Next reg'' m'' = (exec_instr (last xins) 1 reg' m')"
proof-
     have b1_1:"(last xins) = (xins!3)" using a0 
       by (metis One_nat_def Suc_eq_plus1 Suc_numeral add_2_eq_Suc diff_Suc_1' last_conv_nth length_Suc_conv list.simps(3) list.size(3) list_consists_4 semiring_norm(5))
     have b1_2: "(butlast xins) = [xins!0]@[xins!1]@[xins!2]" using b1_1 a0 
       by (metis One_nat_def append_Cons append_Nil butlast.simps(2) list.simps(3) list_consists_4)
     have b1_3:"length xins >0" using a0 by simp
     have b2_3:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (xins!0) 1 reg m)" using b1_3 interp3_list_aux1 
       by (metis a1 bot_nat_0.extremum_strict list.size(3) outcome.exhaust)
     have b2_5:"\<exists> reg1 m1. Next reg1 m1 = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = interp3 (tl xins) (Next reg1 m1) " 
       using a1
       by (metis b1_3 b2_3 interp3.elims length_greater_0_conv list.sel(3) nth_Cons_0 outcome.case(1))
     then obtain reg1 m1 where b2_6:" Next reg1 m1 = (exec_instr (xins!0) 1 reg m) \<and> Next reg'' m'' = interp3 (tl xins) (Next reg1 m1)" by auto
     have b3_3:"\<exists> reg2 m2. Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1)"using exec_instr_def a0 
       by (metis (no_types, opaque_lifting) Suc_eq_plus1 add.commute add.right_neutral b2_6 diff_Suc_1' interp3_list_aux1 list.sel(3) list_consists_4 neq_Nil_conv nth_Cons_numeral numeral_eq_one_iff outcome.exhaust)
     then obtain reg2 m2 where b3_4:"Next reg2 m2 = (exec_instr (xins!1) 1 reg1 m1)" by auto
     have b4_1:"take 2 xins = [xins!0]@[xins!1]" by (simp add: a0 numeral_2_eq_2 take_Suc_conv_app_nth)
     have b4:"Next reg2 m2 = interp3 (take 2 xins) (Next reg m)" using a0 b3_4 b4_1 b2_6 
       by (metis append_Cons append_Nil interp3.simps(2) interp3_list_aux3 outcome.case(1))
     have b5_1:"[xins!0]@[xins!1] @ (drop 2 xins)= xins" using a0
       by (simp add: Cons_nth_drop_Suc numeral_3_eq_3 numeral_nat(2))
     have b5_2:"interp3 (drop 2 xins) (Next reg2 m2) = interp3 (xins) (Next reg m)" using a0 a1 b5_1 b4
       using append_Cons append_Nil interp3.simps(2) outcome.simps(4) by (metis b2_6 b3_4)
     have b5_3:"\<exists> reg2 m2. Next reg2 m2 = interp3 (take 2 xins) (Next reg m) \<and> Next reg'' m'' = interp3 (drop 2 xins) (Next reg2 m2)" 
       using b5_2 b4 using a1 by force
     then obtain reg2 m2 where b5:"Next reg2 m2 = interp3 (take 2 xins) (Next reg m) \<and> Next reg'' m'' = interp3 (drop 2 xins) (Next reg2 m2)" by auto
     have b6_1:"\<exists> reg3 m3. Next reg3 m3 = (exec_instr (xins!2) 1 reg2 m2) " using b5 a0 a1 
       by (metis One_nat_def Suc_1 append_Cons append_Nil b1_2 b5_1 butlast.simps(2) interp3_list_aux1 list.simps(3) nth_Cons_Suc outcome.exhaust)
     then obtain reg3 m3 where b6_2:"Next reg3 m3 = (exec_instr (xins!2) 1 reg2 m2)" by auto
     have b6_3:"take 3 xins = [xins!0]@[xins!1]@[xins!2]" using a0 
       by (simp add: One_nat_def Suc_1 add_One numeral_3_eq_3 numeral_nat(2) take_Suc_conv_app_nth)
     have b6_3:"Next reg3 m3 = interp3 (take 3 xins) (Next reg m)" using a0 b5 b6_2 b6_3 
       by (metis (no_types, lifting) append_Cons append_Nil b2_6 b3_4 b4 interp3.simps(2) interp3_list_aux3 outcome.case(1))
     have b6_4:"[xins!0]@[xins!1]@[xins!2]@[last xins] = xins"
       using append_butlast_last_id b1_2 b1_3 by fastforce
     have b6_5:"butlast xins = take 3 xins" using a0
       by (metis Suc_length_conv append_Cons append_Nil b1_2 butlast_conv_take length_butlast list.size(3) numeral_3_eq_3)
     have b6:"Next reg3 m3 = interp3 (take 3 xins) (Next reg m) \<and> Next reg'' m'' = (exec_instr (last xins) 1 reg3 m3)" using a0 b6_3 b6_4 b5 b5_1 b6_2 
       by (smt (verit, del_insts) Cons_eq_appendI One_nat_def Suc_length_conv eq_Nil_appendI interp3_length2_aux1 list.size(3) nth_Cons_0 nth_Cons_Suc numeral_2_eq_2 outcome.inject same_append_eq)     
     thus ?thesis using b6 b6_5 by auto
   qed

lemma interp3_length4_aux5:
  assumes a0:"length xins = (4::nat)" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and
    a2:"Next reg' m' = (exec_instr (xins!0) 1 reg m)"
  shows "\<exists> reg2 m2. interp3 (butlast(tl xins)) (Next reg' m') = Next reg2 m2"
proof -
  have b0:"xins\<noteq>[]" using a0 by auto
  have "\<exists> reg3 m3. Next reg3 m3 = interp3 (butlast xins) (Next reg m) \<and> Next reg'' m'' = (exec_instr (last xins) 1 reg3 m3)" using interp3_length4_aux6 a0 a1 by blast
  then obtain reg3 m3 where b1_1:"Next reg3 m3 = interp3 (butlast xins) (Next reg m) \<and> Next reg'' m'' = (exec_instr (last xins) 1 reg3 m3)" by auto
  let ?tmplist = "butlast xins"
  have b1_3:"(xins!0) = ?tmplist!0" using a0 
    by (simp add: nth_butlast numeral_3_eq_3)
  have b1_2:"Next reg3 m3 = interp3 ?tmplist (Next reg m)" using b1_1 by auto
  have b1_3:"interp3 (tl ?tmplist) (Next reg' m') \<noteq> Stuck" using interp3_length4_aux1 b0 a2 b1_2 b1_3
    by (metis interp3_list_aux3 list.sel(2) outcome.distinct(1))
  have b1:"\<exists> reg2 m2. interp3 (tl ?tmplist) (Next reg' m') = Next reg2 m2" using b1_3
    by (meson outcome.exhaust)
  have b2:"butlast(tl xins) = tl ?tmplist" using List.butlast_tl a0 by blast
  thus ?thesis using b2 b1 by simp
  qed

lemma push_pop_subgoal_rr_aux1:
  assumes a0:"hd xins = Ppushl_r tmpreg" and 
          a1:"result = (exec_instr (hd xins) 1 reg m)" and
          a2:"tmpreg \<in> {x64Syntax.RDX, x64Syntax.RAX, x64Syntax.RCX}"
        shows "result = Next reg' m' \<longrightarrow> storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR tmpreg)) \<noteq> None"
proof (rule ccontr)
  assume a2:"\<not> (result = Next reg' m' \<longrightarrow> storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR tmpreg)) \<noteq> None)"
  let ?tmp = "storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR tmpreg)) "
  let ?res_ok = "Next reg' m'"
  have a3:"\<not> (\<not> result = ?res_ok \<or> (?tmp \<noteq> None))" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = None" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = None" using a4 conjE by simp
     have b2: "exec_push 1 M32 m reg (reg (IR tmpreg)) = Stuck"using a0 exec_instr_def 
       by (simp add: b0 exec_push_def)
     thus "False" using b2 
       using a1 a4 a2 a0 by (simp add: exec_instr_def)
   qed
 qed


lemma push_pop_subgoal_rr_aux2_1:
  assumes a0:"xins = [Ppushl_r tmpreg, Ppopl tmpreg]" and 
    a1:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
    a2:"Next reg'' m'' = (exec_instr (xins!1) 1 reg' m') " and 
    a3:"tmpreg \<in> {x64Syntax.RDX, x64Syntax.RAX, x64Syntax.RCX}"
  shows "reg'' (IR tmpreg) = reg (IR tmpreg)"
proof -
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


lemma push_pop_subgoal_rr_aux2_2:
 assumes a0:"xins = [Ppushl_r tmpreg, Ppopl tmpreg]" and 
    a1:"Next reg'' m'' = interp3 xins (Next reg m)" and
    a2:"tmpreg \<in> {x64Syntax.RDX, x64Syntax.RAX, x64Syntax.RCX}"
  shows "reg'' (IR tmpreg) = reg (IR tmpreg)"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  thus ?thesis using b0 a0 a1 push_pop_subgoal_rr_aux2_1 interp3_length2_aux2 a2
    by metis
qed

lemma push_pop_subgoal_rr_aux2_3:
  assumes a0:"hd xins = Ppushl_r tmpreg" and 
          a1:"last xins = Ppopl tmpreg"and
          a2:"interp3 (butlast(tl xins)) (Next reg' m') = Next reg2 m'"and
          a3:"Next reg'' m'' = (exec_instr (last xins) 1 reg2 m') " and
          a5:"Next reg' m' = (exec_instr (xins!0) 1 reg m) " and
          a6:"reg' (IR SP) =  reg2 (IR SP)" and
          a7:"tmpreg \<in> {x64Syntax.RDX, x64Syntax.RAX, x64Syntax.RCX}"
  shows "reg'' (IR tmpreg) = reg (IR tmpreg)"
proof-
  let ?midlist = "butlast(tl xins)"
  have b0_1:"xins = [Ppushl_r tmpreg]@?midlist@[Ppopl tmpreg]" using a0 a1
    by (metis append_Cons append_Nil append_butlast_last_id hd_Nil_eq_last instruction.distinct(5787) last_ConsL last_tl list.collapse)
  have b0:"Next reg' m' = exec_push 1 M32 m reg (reg (IR tmpreg))" using exec_instr_def a0 
    using exec_push_def a5 a0 
    by (smt (z3) a1 hd_Nil_eq_last hd_conv_nth instruction.distinct(5787) instruction.simps(6295))
  have b1:"Next reg' m' =
    (case storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR tmpreg)) of None \<Rightarrow> Stuck
     | Some (x::64 word \<Rightarrow> 8 word option option) \<Rightarrow>
         Next
          ((undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg(IR SP := sub64 (reg (IR SP)) (vlong_of_memory_chunk M32))))
           (RIP := add64 (undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg(IR SP := sub64 (reg (IR SP)) (vlong_of_memory_chunk M32))) RIP) (Vlong ((1::64 word) + (1::64 word)))))
          x) " using b0 nextinstr_nf_def nextinstr_def exec_push_def by metis
  have b2_1:"(exec_instr (xins!0) 1 reg m) = Next reg' m' \<longrightarrow> storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR tmpreg)) \<noteq> None" using push_pop_subgoal_rr_aux1 a0 a1 
    by (metis b1 option.case(1) outcome.simps(3))
  have b2_2:"storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR tmpreg)) \<noteq> None" using b2_1 a5 by simp
  have b2:"storev M32 m (sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)) (reg (IR tmpreg))= Some m'" using b1 b2_2 by auto
  have b3:"reg' (IR SP) = sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)" using b1 b2 by auto
  let "?sp" = "reg' (IR SP)"
  have b4:"storev M32 m (reg' (IR SP)) (reg (IR tmpreg)) = Some m'" using b2 b3 by simp
  have b5:"interp3 (butlast(xins)) (Next reg m) = Next reg2 m'" using a2 a5 b0_1 a0
    by (metis append_Cons append_Nil butlast.simps(1) butlast.simps(2) interp3.simps(2) list.sel(3) list.simps(3) nth_Cons_0 outcome.case(1))
  have b6:"(exec_instr (last xins) 1 reg2 m') = Next reg'' m''" using a5 a1 a2 a3 b5 by simp
  have c0:"Next reg'' m'' = exec_pop (1::64 word) M32 m' reg2 (IR tmpreg)" using exec_instr_def using b6 a1 by simp
  have c1:"loadv M32 m' (reg' (IR SP)) = Some (reg (IR tmpreg))" using b4 store_load_consistency by simp
  have c2:"loadv M32 m' (reg2 (IR SP)) = Some (reg (IR tmpreg))" using b4 c1 a6 by simp
  let "?v" = " (reg (IR tmpreg))"
  have c3:" Next reg'' m'' =
    (case loadv M32 m' (reg2 (IR SP)) of None \<Rightarrow> Stuck
     | Some (v::val) \<Rightarrow>
         Next
          ((undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg2(IR tmpreg := ?v, IR SP := add64 (reg2 (IR SP)) (vlong_of_memory_chunk M32))))
           (RIP := add64 (undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg2(IR tmpreg := ?v, IR SP := add64 (reg2 (IR SP)) (vlong_of_memory_chunk M32))) RIP) (Vlong ((1::64 word) + (1::64 word)))))
          m')" using nextinstr_nf_def nextinstr_def exec_pop_def 
    using c0 c2 a7 by simp
  have c4:"reg''(IR tmpreg) = ?v" using exec_pop_def c2 c3 a7 by auto
  thus ?thesis using c4 by simp
qed

lemma reg_rsp_consist:"r = (bpf_to_x64_reg dst) \<Longrightarrow> r \<noteq> x64Syntax.RSP"
  apply(cases dst) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)


end