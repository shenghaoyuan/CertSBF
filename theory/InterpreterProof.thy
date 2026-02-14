theory InterpreterProof
imports Interpreter Interpreter2
begin

(** meter' = meter + target_pc - (pc+1) **)
definition cu_invariant::"u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> bool" where
"cu_invariant l_pc remain_cu remain_cu' curr_pc const \<equiv> remain_cu + const = remain_cu' + l_pc - curr_pc"


theorem preserve_cu_invariant:
" st0 = (BPF_st BPF_OK1 l_pc pc rs m ss sv remain_cu) \<Longrightarrow> 
  step1 pc ins rs m ss sv lpc remain_cu = st1 \<Longrightarrow>
  step2 lpc pc ins rs m ss sv remain_cu = st2 \<Longrightarrow>
  st1 = BPF_st BPF_OK1 l_pc1 pc1 rs1 m1 ss1 sv1 remain_cu1 \<Longrightarrow>
  st2 = BPF_st BPF_OK1 l_pc2 pc2 rs2 m2 ss2 sv2 remain_cu2 \<Longrightarrow>
  cu_invariant l_pc1 remain_cu remain_cu2 pc2 (lpc-pc)"
proof-
  assume assm0:"st0 = (BPF_st BPF_OK1 l_pc pc rs m ss sv remain_cu)" and
    assm1:"step1 pc ins rs m ss sv lpc remain_cu = st1" and
    assm2:"step2 lpc pc ins rs m ss sv remain_cu = st2" and
    assm4:"st1 = BPF_st BPF_OK1 l_pc1 pc1 rs1 m1 ss1 sv1 remain_cu1" and
    assm5:"st2 = BPF_st BPF_OK1 l_pc2 pc2 rs2 m2 ss2 sv2 remain_cu2"
then show ?thesis proof(cases ins)
  case (BPF_LD_IMM x11 x12 x13)
  then show ?thesis sorry
(*  proof -
    have "l_pc = pc+1" 
      using assm1 assm4 assm0 
      apply(unfold step1_def Let_def,simp_all) 
      apply(cases ins,simp_all)  defer using local.BPF_LD_IMM apply blast+
      subgoal for x11 x12 x13
        apply(cases "eval_load_imm x11 x12 x13 rs m",simp_all)
        apply(unfold eval_load_imm_def,simp_all)
        apply(cases "loadv M64 m1 (Vlong (ucast (scast x12 + scast x13)))")

         prefer 2 subgoal for a 
          apply(cases "loadv M64 m1 (Vlong (ucast (scast x12 + scast x13)))")*)

next
  case (BPF_LDX x21 x22 x23 x24)
  then show ?thesis sorry
next
  case (BPF_ST x31 x32 x33 x34)
  then show ?thesis sorry
next
  case (BPF_ADD_STK x4)
  then show ?thesis sorry
next
  case (BPF_ALU x51 x52 x53)
  then show ?thesis sorry
next
  case (BPF_NEG32_REG x6)
  then show ?thesis sorry
next
  case (BPF_LE x71 x72)
  then show ?thesis sorry
next
  case (BPF_BE x81 x82)
  then show ?thesis sorry
next
  case (BPF_ALU64 x91 x92 x93)
  then show ?thesis
  proof -
    have b0:"l_pc1 = lpc+1" 
      using assm1 assm4 assm0 
      apply(unfold step1_def Let_def,simp_all) 
      apply(cases ins,simp_all)  using local.BPF_ALU64 apply blast+
      subgoal for x11 x12 x13
        apply(cases sv,simp_all)
         apply(cases "eval_alu64 x11 x12 x13 rs enable_instruction_meter",simp_all)
         apply(unfold eval_alu64_def eval_alu64_aux1_def eval_alu64_aux2_def eval_alu64_aux3_def eval_reg_def Let_def) 
        apply(cases x11,simp_all) 
        apply(cases x13,simp_all) 
        done
      using local.BPF_ALU64 apply blast+
      done

    have b1:"remain_cu2 = remain_cu \<and> pc2 = pc+1"
      using assm2 assm5 
      apply(unfold step2_def Let_def,simp_all) 
      apply(cases ins,simp_all)  using local.BPF_ALU64 apply blast+
      subgoal for x11 x12 x13
        apply(cases sv,simp_all)
         apply(cases "eval_alu64 x11 x12 x13 rs enable_instruction_meter",simp_all)
        apply(unfold eval_alu64_def eval_alu64_aux1_def eval_alu64_aux2_def eval_alu64_aux3_def eval_reg_def Let_def) 
        apply(cases x11,simp_all) 
        apply(cases x13,simp_all) 
        done
      using local.BPF_ALU64 apply blast+
      done
    thus ?thesis using b0 b1 by(unfold cu_invariant_def,simp_all)
  qed
next
  case (BPF_NEG64_REG x10)
  then show ?thesis sorry
next
  case (BPF_HOR64_IMM x111 x112)
  then show ?thesis sorry
next
  case (BPF_PQR x121 x122 x123)
  then show ?thesis sorry
next
  case (BPF_PQR64 x131 x132 x133)
  then show ?thesis sorry
next
  case (BPF_PQR2 x141 x142 x143)
  then show ?thesis sorry
next
  case (BPF_JA x15)
    have b0:"l_pc1 = lpc+1" 
      using assm1 assm4 assm0 
      apply(unfold step1_def Let_def,simp_all) 
      apply(cases ins,simp_all) 
      using local.BPF_JA apply blast+
      done

    have b1:"pc2 = pc + scast x15 + 1" 
      using assm2 assm5 
      apply(unfold step2_def Let_def,simp_all) 
      apply(cases ins,simp_all)  
      using local.BPF_JA apply blast+
          defer 
      using local.BPF_JA apply blast+
      subgoal for x15a 
        apply(subgoal_tac "x15 = x15a")
        prefer 2 using local.BPF_JA apply blast  
        apply(cases "emit_validate_and_profile_instruction_count (pc + scast x15a + 1) pc remain_cu False",simp_all)
        subgoal for a apply(cases a,simp_all)
          done
        done
      done

    have b2:"remain_cu2 = remain_cu + (pc + scast x15 + 1) - (pc + 1)"
      using assm2 assm5 b1
      apply(unfold step2_def Let_def,simp_all) 
      apply(cases ins,simp_all)  
      using local.BPF_JA apply blast+
      subgoal for x15a 
        apply(cases "emit_validate_and_profile_instruction_count (pc + scast x15a + 1) pc remain_cu False",simp_all)
        subgoal for a apply(cases a,simp_all)
        apply(unfold emit_validate_and_profile_instruction_count_def)
          apply(cases "emit_validate_instruction_count pc remain_cu False",simp_all)
          apply(unfold emit_validate_instruction_count_def emit_profile_instruction_count_def,simp_all)
          done
        done
      using local.BPF_JA apply blast+
      done

      (*remain_cu + (lpc-pc) = (remain_cu + (pc + scast x15 + 1) - (pc + 1)) + (lpc+1) - (pc + scast x15 + 1)*)
    have b3:"cu_invariant (lpc+1) remain_cu (remain_cu + (pc + scast x15 + 1) - (pc + 1)) pc2 (lpc-pc)"
      using b2 b1 b0 by(unfold cu_invariant_def,simp_all)
    then show ?thesis 
      using b3 using b0 b2 by blast 
next
  case (BPF_JUMP x161 x162 x163 x164)
  then show ?thesis sorry
next
  case (BPF_CALL_REG x171 x172)
  then show ?thesis sorry
next
  case (BPF_CALL_IMM x181 x182)
  then show ?thesis sorry
next
  case BPF_EXIT
  then show ?thesis sorry
qed
qed

(**remain_cu + target_pc - (pc+1) = remain_cu' **)
                   (** | |**)
(**interp1_remain_cu + (init_lpc-init_pc) = remain_cu' + interp_lpc - pc**)
theorem cu_correct_ok_state:
" st0 = (BPF_st BPF_OK1 l_pc pc rs m ss sv remain_cu) \<Longrightarrow>
  bpf_interp1 n l st0 = st1 \<Longrightarrow> 
  bpf_interp2 n l st0 = st2 \<Longrightarrow>
  st1 = BPF_st BPF_Success1 l_pc' pc' rs' m' ss' sv' remain_cu' \<Longrightarrow>
  st2 = BPF_st BPF_Success1 l_pc'' pc'' rs' m' ss' sv' remain_cu''"
proof (induction n arbitrary: st0 l_pc pc rs m ss sv remain_cu st1 l_pc' pc' rs' m' ss' sv' remain_cu' remain_cu'')
  case 0
  then show ?case by simp
next
  case (Suc n)
 
  have c0:"bpf_interp1 (Suc n) l st0 = st1" using Suc by blast
  have c1:"bpf_interp2 (Suc n) l st0 = st2" using Suc by blast
  have c2:"st0 = BPF_st BPF_OK1 l_pc pc rs m ss sv remain_cu" using Suc by blast
  have c3:"st1 = BPF_st BPF_Success1 l_pc' pc' rs' m' ss' sv' remain_cu'" using Suc by blast

  have "\<exists> st1'. st1' = bpf_interp1 1 l st0" by blast
  then obtain temp_st1 where d0:"temp_st1 = bpf_interp1 1 l st0" by presburger 
  have "\<exists> temp1_l_pc temp1_pc temp1_rs temp1_m temp1_ss temp1_sv temp1_remain_cu. temp_st1 = BPF_st BPF_OK1 temp1_l_pc temp1_pc temp1_rs temp1_m temp1_ss temp1_sv temp1_remain_cu" sorry
  then obtain temp1_l_pc temp1_pc temp1_rs temp1_m temp1_ss temp1_sv temp1_remain_cu where d1:"temp_st1 = BPF_st BPF_OK1 temp1_l_pc temp1_pc temp1_rs temp1_m temp1_ss temp1_sv temp1_remain_cu" by auto

  have "\<exists> temp_st2. temp_st2 = bpf_interp2 1 l st0" by blast
  then obtain temp_st2 where d2:"temp_st2 = bpf_interp2 1 l st0" by presburger 
  have "\<exists> temp2_l_pc temp2_pc temp2_rs temp2_m temp2_ss temp2_sv temp2_remain_cu. temp_st1 = BPF_st BPF_OK1 temp2_l_pc temp2_pc temp2_rs temp2_m temp2_ss temp2_sv temp2_remain_cu" sorry
  then obtain temp2_l_pc temp2_pc temp2_rs temp2_m temp2_ss temp2_sv temp2_remain_cu where d3:"temp_st1 = BPF_st BPF_OK1 temp2_l_pc temp2_pc temp2_rs temp2_m temp2_ss temp2_sv temp2_remain_cu" by auto

  have d4:"temp2_rs = temp1_rs \<and> temp1_m = temp2_m \<and> temp1_ss = temp2_ss \<and> temp1_sv = temp2_sv" sorry

  have e0:"temp1_l_pc =  l_pc + 1" sorry

  have e1:"temp1_l_pc -1 < remain_cu" sorry

  have e2:"temp2_pc = temp1_pc" sorry

  have e3:"remain_cu > l_pc" sorry

  (*have e4:"l_pc > pc" sorry*)
  have e4:"remain_cu > pc" sorry

  have e5:"remain_cu + (l_pc-pc) = temp2_remain_cu + temp1_l_pc - temp2_pc" sorry

 (* have e6:"remain_cu - (pc+1) + pc'' = remain_cu''"
    using e5 e0 by (metis (no_types, lifting) add_diff_eq diff_diff_eq eq_diff_eq) 

  have e7:"remain_cu > pc+1" sorry

  have e8:"remain_cu'' > 0" sorry

  have e9:"pc'' > 0" sorry*)

  have e6:"remain_cu - (pc+1) = temp2_remain_cu - temp2_pc"
    using e5 e0 by (metis (no_types, lifting) add_diff_eq diff_diff_eq eq_diff_eq) 

  have e7:"remain_cu -(pc+1) > 0 " sorry

  have e8:"temp2_remain_cu - temp2_pc > 0" using e6 e7 by auto

  have f0:"bpf_interp1 1 l st0 = temp_st1 \<and> bpf_interp1 n l temp_st1 = st1" sorry

  have f1:"bpf_interp1 n l st0 = temp_st2 \<and> bpf_interp1 n l temp_st2 = st2" sorry


  have "st0 = BPF_st BPF_OK1 l_pc pc rs m ss sv remain_cu \<Longrightarrow>
        bpf_interp1 n l st0 = st1 \<Longrightarrow>
        bpf_interp2 n l st0 = st2 \<Longrightarrow> 
        st1 = BPF_st BPF_Success1 l_pc' pc' rs' m' ss' sv' remain_cu' \<Longrightarrow> 
        st2 = BPF_st BPF_Success1 l_pc'' pc'' rs' m' ss' sv' remain_cu''"
   using Suc by blast


  then show ?case using c0 c1 c2 c3 Suc sorry
qed



theorem cu_correct_err_state:
" st0 = (BPF_st BPF_OK1 l_pc pc rs m ss sv rem_cu) \<Longrightarrow>
  bpf_interp1 n l st0 = st1 \<Longrightarrow> bpf_interp2 n l st0 = st2 \<Longrightarrow> 
  st2 = BPF_st BPF_CU1 l_pc' pc' rs' m' ss' sv' remain_cu' \<Longrightarrow>
  st1 = BPF_st BPF_CU1 l_pc' pc' rs' m' ss' sv' remain_cu''"
  apply (induction n, simp)
  subgoal for n
    sorry
  done

(*lemma hh1:
  assumes a0:"bstate1 = bpf_interp (length bprog+1) bprog (BPF_OK 0 rs m ss sv 0 cu) " and
          a1:"bstate2 = bpf_interp2 (length bprog+1) 0 bprog (BPF_OK 0 rs m ss sv 0 cu) " and
          a2:"bpf_find_instr 0 prog = Some (BPF_ALU64 BPF_ADD dst (SOReg src))" and
          a3:"bpf_find_instr 1 prog = Some BPF_EXIT" and*)

lemma hh1_aux1:
  "step pc ins rs m ss sv cur_cu remain_cu = BPF_Success v \<Longrightarrow> ins = BPF_EXIT"
  apply(unfold step_def Let_def)
apply(cases ins; simp_all)
 subgoal for x11 x12 x13 
    apply(cases "eval_load_imm x11 x12 x13 rs m", simp_all)
    done
  subgoal for x21 x22 x23 x24 apply(cases "eval_load x21 x22 x23 x24 rs m", simp_all)
    done
  subgoal for x31 x32 x33 x34 apply(cases "eval_store x31 x32 x33 x34 rs m", simp_all)
    done
  subgoal for x4 apply(cases sv, simp_all) apply(cases "eval_add64_imm_R10 x4 ss enable_instruction_meter",simp_all)
    apply(cases "eval_add64_imm_R10 x4 ss False",simp_all)
    done
  subgoal for x51 x52 x53 apply(cases sv, simp_all) apply(cases "eval_alu32 x51 x52 x53 rs enable_instruction_meter",simp_all)
    apply(cases "eval_alu32 x51 x52 x53 rs False",simp_all) 
    done
  subgoal for x6 apply(cases "sv",simp_all) apply(cases "eval_neg32 x6 rs enable_instruction_meter",simp_all)
    apply(cases " eval_neg32 x6 rs False",simp_all)
    done
  subgoal for x71 x72 apply(cases sv,simp_all) apply(cases "eval_le x71 x72 rs enable_instruction_meter",simp_all)
    apply(cases "eval_le x71 x72 rs False",simp_all)
    done
  subgoal for x81 x82 apply(cases sv,simp_all) apply(cases "eval_be x81 x82 rs enable_instruction_meter",simp_all)
    apply(cases "eval_be x81 x82 rs False",simp_all)
    done
  subgoal for x91 x92 x93 apply(cases sv,simp_all) apply(cases "eval_alu64 x91 x92 x93 rs enable_instruction_meter",simp_all)
 apply(cases "eval_alu64 x91 x92 x93 rs False",simp_all)
    done
 subgoal for x10 apply(cases sv,simp_all) apply(cases "eval_neg64 x10 rs enable_instruction_meter",simp_all)
 apply(cases "eval_neg64 x10 rs False",simp_all)
   done
subgoal for x111 x112 apply(cases sv,simp_all) apply(cases " eval_hor64 x111 x112 rs enable_instruction_meter",simp_all)
 apply(cases "eval_hor64 x111 x112 rs False",simp_all)
  done
subgoal for x121 x122 x123 apply(cases sv,simp_all) apply(cases " eval_pqr32 x121 x122 x123 rs enable_instruction_meter",simp_all)
 apply(cases " eval_pqr32 x121 x122 x123 rs False",simp_all)
  done
subgoal for x131 x132 x133 apply(cases sv,simp_all) apply(cases "eval_pqr64 x131 x132 x133 rs enable_instruction_meter",simp_all)
 apply(cases "eval_pqr64 x131 x132 x133 rs False",simp_all)
  done
subgoal for x141 x142 x143 apply(cases sv,simp_all) apply(cases "eval_pqr64_2 x141 x142 x143 rs enable_instruction_meter",simp_all)
 apply(cases "eval_pqr64_2 x141 x142 x143 rs False",simp_all)
  done
  subgoal for x161 x162 x163 x164 
    apply(split if_splits,simp_all)
    done
(*    apply(cases "eval_jmp x161 x162 x163 rs enable_instruction_meter",simp_all)
 apply(cases "eval_jmp x161 x162 x163 rs",simp_all)
  done*)
  prefer 2
subgoal for x181 x182 apply(cases sv,simp_all) 
   apply(cases "eval_call_imm x182 rs ss enable_instruction_meter",simp_all)
  subgoal for a 
    apply(cases a,simp_all)
  done
apply(cases "eval_call_imm x182 rs ss False",simp_all)
  subgoal for a apply(cases a,simp_all)
    done
  done
  subgoal for x181 x182 apply(cases sv,simp_all) 
     apply(cases "eval_call_reg x181 x182 rs ss enable_instruction_meter pc",simp_all)
 subgoal for a 
   apply(cases a,simp_all)
   done
apply(cases "eval_call_reg x181 x182 rs ss False pc",simp_all)
 subgoal for a 
   apply(cases a,simp_all)
   done
  done
  done


lemma hh1_aux2:
  "step2 pc ins rs m ss sv cur_cu remain_cu = BPF_OK pc rs' m' ss' sv cur_cu' remain_cu' \<Longrightarrow> cur_cu' = cur_cu+1"
apply(unfold step2_def Let_def)
  apply(cases ins; simp_all)
 subgoal for x11 x12 x13 
    apply(cases "eval_load_imm x11 x12 x13 rs m", simp_all)
    done
  subgoal for x21 x22 x23 x24 apply(cases "eval_load x21 x22 x23 x24 rs m", simp_all)
    done
  subgoal for x31 x32 x33 x34 apply(cases "eval_store x31 x32 x33 x34 rs m", simp_all)
    done
  subgoal for x4 apply(cases sv, simp_all) apply(cases "eval_add64_imm_R10 x4 ss enable_instruction_meter",simp_all)
    apply(cases "eval_add64_imm_R10 x4 ss False",simp_all)
    done
  subgoal for x51 x52 x53 apply(cases sv, simp_all) apply(cases "eval_alu32 x51 x52 x53 rs enable_instruction_meter",simp_all)
    apply(cases "eval_alu32 x51 x52 x53 rs False",simp_all) 
    done
  subgoal for x6 apply(cases "sv",simp_all) apply(cases "eval_neg32 x6 rs enable_instruction_meter",simp_all)
    apply(cases " eval_neg32 x6 rs False",simp_all)
    done
  subgoal for x71 x72 apply(cases sv,simp_all) apply(cases "eval_le x71 x72 rs enable_instruction_meter",simp_all)
    apply(cases "eval_le x71 x72 rs False",simp_all)
    done
  subgoal for x81 x82 apply(cases sv,simp_all) apply(cases "eval_be x81 x82 rs enable_instruction_meter",simp_all)
    apply(cases "eval_be x81 x82 rs False",simp_all)
    done
  subgoal for x91 x92 x93 apply(cases sv,simp_all) apply(cases "eval_alu64 x91 x92 x93 rs enable_instruction_meter",simp_all)
 apply(cases "eval_alu64 x91 x92 x93 rs False",simp_all)
    done
 subgoal for x10 apply(cases sv,simp_all) apply(cases "eval_neg64 x10 rs enable_instruction_meter",simp_all)
 apply(cases "eval_neg64 x10 rs False",simp_all)
   done
subgoal for x111 x112 apply(cases sv,simp_all) apply(cases " eval_hor64 x111 x112 rs enable_instruction_meter",simp_all)
 apply(cases "eval_hor64 x111 x112 rs False",simp_all)
  done
subgoal for x121 x122 x123 apply(cases sv,simp_all) apply(cases " eval_pqr32 x121 x122 x123 rs enable_instruction_meter",simp_all)
 apply(cases " eval_pqr32 x121 x122 x123 rs False",simp_all)
  done
subgoal for x131 x132 x133 apply(cases sv,simp_all) apply(cases "eval_pqr64 x131 x132 x133 rs enable_instruction_meter",simp_all)
 apply(cases "eval_pqr64 x131 x132 x133 rs False",simp_all)
  done
subgoal for x141 x142 x143 apply(cases sv,simp_all) apply(cases "eval_pqr64_2 x141 x142 x143 rs enable_instruction_meter",simp_all)
 apply(cases "eval_pqr64_2 x141 x142 x143 rs False",simp_all)
  done
prefer 2 subgoal for x161 x162 x163 x164 apply(cases "eval_jmp x161 x162 x163 rs enable_instruction_meter",simp_all)
 apply(cases "eval_jmp x161 x162 x163 rs",simp_all)
  using eval_jmp_def try
  prefer 2
subgoal for x181 x182 apply(cases sv,simp_all) 
   apply(cases "eval_call_imm x182 rs ss enable_instruction_meter",simp_all)
  subgoal for a 
    apply(cases a,simp_all)
  done
apply(cases "eval_call_imm x182 rs ss False",simp_all)
  subgoal for a apply(cases a,simp_all)
    done
  done
  subgoal for x181 x182 apply(cases sv,simp_all) 
     apply(cases "eval_call_reg x181 x182 rs ss enable_instruction_meter pc",simp_all)
 subgoal for a 
   apply(cases a,simp_all)
   done
apply(cases "eval_call_reg x181 x182 rs ss False pc",simp_all)
 subgoal for a 
   apply(cases a,simp_all)
   done
  done



(*bpf_find_instr 0 prog = BPF_ALU64 BPF_ADD dst (SOReg src)
  bpf_find_instr 1 prog = BPF_EXIT*)

lemma hh1_aux1:
  "step pc ins rs m ss sv cur_cu remain_cu = BPF_Success v \<Longrightarrow>
   step2 pc ins rs m ss sv cur_cu remain_cu = BPF_Success v"
  apply(cases ins; simp_all)

lemma hh3_aux1:
  assumes a0:"step pc ins rs m ss sv cur_cu remain_cu = BPF_Success v"
  shows "step2 pc ins rs m ss sv cur_cu remain_cu = BPF_Success v"


lemma hh1_aux1:
  assumes a0:"step pc ins rs m ss sv cur_cu remain_cu = BPF_OK pc rs' m' ss' sv (cur_cu+1) remain_cu"
  shows "step2 pc ins rs m ss sv cur_cu remain_cu = BPF_OK pc rs' m' ss' sv cur_cu (cu-n)"
proof(cases ins)
  case (BPF_LD_IMM x11 x12 x13)
  have "eval_load_imm = Some rs'" using 
  then show ?thesis sorry
next
  case (BPF_LDX x21 x22 x23 x24)
  then show ?thesis sorry
next
  case (BPF_ST x31 x32 x33 x34)
  then show ?thesis sorry
next
  case (BPF_ADD_STK x4)
  then show ?thesis sorry
next
  case (BPF_ALU x51 x52 x53)
  then show ?thesis sorry
next
  case (BPF_NEG32_REG x6)
  then show ?thesis sorry
next
  case (BPF_LE x71 x72)
  then show ?thesis sorry
next
  case (BPF_BE x81 x82)
  then show ?thesis sorry
next
  case (BPF_ALU64 x91 x92 x93)
  then show ?thesis sorry
next
  case (BPF_NEG64_REG x10)
  then show ?thesis sorry
next
  case (BPF_HOR64_IMM x111 x112)
  then show ?thesis sorry
next
  case (BPF_PQR x121 x122 x123)
  then show ?thesis sorry
next
  case (BPF_PQR64 x131 x132 x133)
  then show ?thesis sorry
next
  case (BPF_PQR2 x141 x142 x143)
  then show ?thesis sorry
next
  case (BPF_JA x15)
  then show ?thesis sorry
next
  case (BPF_JUMP x161 x162 x163 x164)
  then show ?thesis sorry
next
  case (BPF_CALL_REG x171 x172)
  then show ?thesis sorry
next
  case (BPF_CALL_IMM x181 x182)
  then show ?thesis sorry
next
  case BPF_EXIT
  then show ?thesis sorry
qed


lemma hh1:
  assumes a0:"bstate1 = bpf_interp (length bprog+1) bprog (BPF_OK 0 rs m ss sv 0 cu) " and
          a1:"bstate2 = bpf_interp2 (length bprog+1) 0 bprog (BPF_OK 0 rs m ss sv 0 cu) " and
          a2:"bpf_find_instr 0 prog = Some (BPF_ALU64 BPF_ADD dst (SOReg src))" and
          a3:"bpf_find_instr 1 prog = Some BPF_EXIT" and
          a4:"bstate2 = BPF_CU"
  shows "bstate1 = BPF_CU"
proof -
  have "cu > length bprog" using a0 a2 a3 a4 

lemma hh2:
  assumes a0:"bstate1 = bpf_interp (length bprog+1) bprog (BPF_OK 0 rs m ss sv 0 cu) " and
          a1:"bstate2 = bpf_interp2 (length bprog+1) 0 bprog (BPF_OK 0 rs m ss sv 0 cu) " and
          a2:"bstate1 = BPF_OK pc rs' m ss' sv n cu"  (*n=length bprog*)
  shows "bstate2 = BPF_OK pc rs' m' ss' sv pc (cu-n)"
proof-
  have "n<cu" using a2 sorry


(*        a2:"bpf_find_instr 0 prog = Some (BPF_ALU64 BPF_ADD dst (SOReg src))" and
          a3:"bpf_find_instr 1 prog = Some BPF_EXIT" and*)



lemma hh3:
  assumes a0:"bstate1 = bpf_interp (unat cu+1) bprog (BPF_OK 0 rs m ss sv 0 cu) " and
          a1:"bstate2 = bpf_interp2 (unat cu+1) 0 bprog (BPF_OK 0 rs m ss sv 0 cu) " and
          a2:"bpf_find_prog (unat cu+1) 0 bprog = Some [BPF_ALU64 BPF_ADD dst (SOReg src),BPF_EXIT]" and
          a3:"bstate2 = BPF_Success v"
  shows "bstate1 = BPF_Success v"
proof -
  from a1 a2 have "\<exists> s'. s' = step2 0 (BPF_ALU64 BPF_ADD dst (SOReg src)) rs m ss sv 0 cu " by blast
  then obtain s' where c0:"s' = step2 0 (BPF_ALU64 BPF_ADD dst (SOReg src)) rs m ss sv 0 cu" by auto
  have "\<exists> s''. bpf_interp2 (unat cu+1) 0 bprog s'' = bstate2"  using a1 by blast
  then obtain s'' where c1:"s'' = "

(*

fun bpf_interp :: "nat \<Rightarrow> u64 \<Rightarrow> bpf_bin \<Rightarrow> bpf_state \<Rightarrow> bpf_state" where
"bpf_interp 0 _ _ _ =  BPF_EFlag" | 
"bpf_interp (Suc n) remain_cu prog st  = (
  case st of
  BPF_EFlag \<Rightarrow> BPF_EFlag |
  BPF_Err \<Rightarrow> BPF_Err |
  BPF_Success v \<Rightarrow> BPF_Success v |
  BPF_OK pc rs m ss sv cur_cu  \<Rightarrow> (
    if unat pc < length prog then
      if cur_cu \<ge> remain_cu then
        BPF_EFlag
      else
        case bpf_find_instr (unat pc) prog of
        None \<Rightarrow> BPF_Err |
        Some ins \<Rightarrow> bpf_interp n remain_cu prog (step pc ins rs m ss sv (cur_cu+1) remain_cu) 
    else BPF_Err))"
*)

(*

fun step2 :: "u64 \<Rightarrow> bpf_instruction \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> stack_state \<Rightarrow> SBPFV \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> bpf_state" where
"step2 pc ins rs m ss sv cur_cu remain_cu = ( let is_v1 = (case sv of V1 \<Rightarrow> True | _ \<Rightarrow> False) in
  case ins of
  BPF_ALU bop d sop \<Rightarrow> (
    case eval_alu32 bop d sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu ) |

  BPF_ALU64 bop d sop \<Rightarrow> (
    case eval_alu64 bop d sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu ) |

  BPF_ADD_STK i \<Rightarrow> (
    case eval_add64_imm_R10 i ss is_v1 of
    None \<Rightarrow> BPF_Err |
    Some ss' \<Rightarrow> BPF_OK (pc+1) rs m ss' sv cur_cu ) |

  BPF_LE dst imm \<Rightarrow> (
    case eval_le dst imm rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu ) |

  BPF_BE dst imm \<Rightarrow> (
    case eval_be dst imm rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu ) |

  BPF_NEG32_REG dst \<Rightarrow> (
    case eval_neg32 dst rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu ) |

  BPF_NEG64_REG dst \<Rightarrow> (
    case eval_neg64 dst rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu ) |

  BPF_LDX chk dst sop off \<Rightarrow> (
    case eval_load chk dst sop off rs m of
    None \<Rightarrow> BPF_EFlag |
    Some rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu ) |

  BPF_ST chk dst sop off \<Rightarrow> (
    case eval_store chk dst sop off rs m of
    None \<Rightarrow> BPF_EFlag |
    Some m' \<Rightarrow> BPF_OK (pc+1) rs m' ss sv cur_cu ) |

  BPF_LD_IMM dst imm1 imm2  \<Rightarrow> (
    case eval_load_imm dst imm1 imm2 rs m of
    None \<Rightarrow> BPF_EFlag |
    Some rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu ) |

  BPF_PQR pop dst sop \<Rightarrow> (
    case eval_pqr32 pop dst sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu ) |

  BPF_PQR64 pop dst sop \<Rightarrow> (
    case eval_pqr64 pop dst sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu ) |

  BPF_PQR2 pop dst sop \<Rightarrow> (
    case eval_pqr64_2 pop dst sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu ) |

  BPF_HOR64_IMM dst imm \<Rightarrow> (
    case eval_hor64 dst imm rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu ) |

  BPF_JA off  \<Rightarrow>
    BPF_OK (pc + scast off + 1) rs m ss sv cur_cu  |

  BPF_JUMP cond bpf_ireg snd_op off  \<Rightarrow> (
    if eval_jmp cond bpf_ireg snd_op rs then
      BPF_OK (pc + scast off + 1) rs m ss sv cur_cu 
    else
      BPF_OK (pc + 1) rs m ss sv cur_cu ) |

  BPF_CALL_IMM src imm \<Rightarrow> (
    case eval_call_imm imm rs ss is_v1  of
    None \<Rightarrow> BPF_EFlag |
    Some (pc, rs', ss') \<Rightarrow> BPF_OK pc rs' m ss' sv cur_cu ) |

  BPF_CALL_REG src imm \<Rightarrow> (
    case eval_call_reg src imm rs ss is_v1 pc of
    None \<Rightarrow> BPF_EFlag |
    Some (pc', rs', ss') \<Rightarrow> BPF_OK pc' rs' m ss' sv (cur_cu+1) ) |
  BPF_EXIT \<Rightarrow> (
    if call_depth ss = 0 then
      if cur_cu >  remain_cu then
        BPF_EFlag
      else
        BPF_Success (rs BR1)
    else (
      let (pc', rs', ss') = eval_exit rs ss is_v1 in
        BPF_OK pc' rs' m ss' sv cur_cu ))
)"


fun bpf_interp2 :: "nat \<Rightarrow> last_pc \<Rightarrow>  insn_meter \<Rightarrow> bpf_bin \<Rightarrow> bpf_state \<Rightarrow> bpf_state" where
"bpf_interp2 0 _ _ _ _ = BPF_EFlag" | 
"bpf_interp2 (Suc fuel) l_pc remain_cu prog st = (
  case st of
  BPF_EFlag \<Rightarrow> BPF_EFlag |
  BPF_Err \<Rightarrow> BPF_Err |
  BPF_Success v \<Rightarrow> BPF_Success v |
  BPF_OK pc rs m ss sv cur_pc  \<Rightarrow> (
    if (instruction_meter_checkpoint_distance + l_pc \<le> cur_pc) \<and> cur_pc + 1 > remain_cu then BPF_EFlag
    else
      let l_pc' = if instruction_meter_checkpoint_distance + l_pc \<le> cur_pc then cur_pc else l_pc in 
      if unat pc < length prog then
        if cur_pc \<ge> remain_cu then
          BPF_EFlag
        else
          case bpf_find_instr (unat pc) prog of
            None \<Rightarrow> BPF_Err |
            Some ins \<Rightarrow> 
              let remain_cu' = case ins of
                BPF_JA ofs \<Rightarrow>
                  let t_pc :: u64 = cur_pc + scast ofs + 1 in
                  emit_validate_and_profile_instruction_count t_pc cur_pc remain_cu |
                BPF_JUMP cond bpf_ireg snd_op ofs \<Rightarrow>
                  let t_pc = cur_pc + scast ofs + 1 in 
                  emit_validate_and_profile_instruction_count t_pc cur_pc remain_cu |
                BPF_LD_IMM dst imm1 imm2 \<Rightarrow>
                  emit_validate_and_profile_instruction_count (cur_pc+2) cur_pc remain_cu |
                BPF_CALL_IMM src imm \<Rightarrow> (
                  case get_function_registry (ucast imm) of
                    None \<Rightarrow> None |
                    Some t_pc \<Rightarrow> emit_validate_and_profile_instruction_count t_pc cur_pc remain_cu) |
                BPF_CALL_REG src imm \<Rightarrow>
                  let v = case sv of
                  V1 \<Rightarrow> Option.the (u4_to_bpf_ireg (scast imm)) |
                  V2 \<Rightarrow> src in 
                  emit_validate_and_profile_instruction_count (rs v) cur_pc remain_cu |
                BPF_EXIT \<Rightarrow> emit_validate_and_profile_instruction_count 0 cur_pc remain_cu |
                _ \<Rightarrow> Some(l_pc,remain_cu) in 
            if remain_cu' = None then
              BPF_EFlag
            else
              let meter' = (snd (Option.the remain_cu')) in
              let l_pc' = fst (Option.the remain_cu') in
            bpf_interp2 fuel l_pc' remain_cu prog (step2 pc ins rs m ss sv cur_pc remain_cu)
      else BPF_EFlag))"  



*)




(*
fun bpf_interp2 :: "nat \<Rightarrow> last_pc \<Rightarrow> bpf_bin \<Rightarrow> bpf_state \<Rightarrow> bpf_state" where
"bpf_interp2 0 _ _ _ = BPF_EFlag" | 
"bpf_interp2 (Suc fuel) l_pc prog st = (
  case st of
  BPF_EFlag \<Rightarrow> BPF_EFlag |
  BPF_Err \<Rightarrow> BPF_Err |
  BPF_Success v \<Rightarrow> BPF_Success v |
  BPF_OK pc rs m ss sv cur_pc remain_cu \<Rightarrow> (
    if unat pc < length prog then
      if (instruction_meter_checkpoint_distance + l_pc \<le> cur_pc) \<and> cur_pc + 1 > remain_cu then BPF_EFlag
      else
        let l_pc' = if instruction_meter_checkpoint_distance + l_pc \<le> cur_pc then cur_pc else l_pc in 
          case bpf_find_instr (unat pc) prog of
            None \<Rightarrow> BPF_Err |
            Some ins \<Rightarrow> 
              let n' = case ins of
                BPF_JA ofs \<Rightarrow>
                  let t_pc :: u64 = cur_pc + scast ofs + 1 in
                  emit_validate_and_profile_instruction_count t_pc cur_pc remain_cu |
                BPF_JUMP cond bpf_ireg snd_op ofs \<Rightarrow>
                  let t_pc = cur_pc + scast ofs + 1 in 
                  emit_validate_and_profile_instruction_count t_pc cur_pc remain_cu |
                BPF_LD_IMM dst imm1 imm2 \<Rightarrow>
                  emit_validate_and_profile_instruction_count (cur_pc+2) cur_pc remain_cu |
                BPF_CALL_IMM src imm \<Rightarrow> (
                  case get_function_registry (ucast imm) of
                    None \<Rightarrow> None |
                    Some t_pc \<Rightarrow> emit_validate_and_profile_instruction_count t_pc cur_pc remain_cu) |
                BPF_CALL_REG src imm \<Rightarrow>
                  let v = case sv of
                  V1 \<Rightarrow> Option.the (u4_to_bpf_ireg (scast imm)) |
                  V2 \<Rightarrow> src in 
                  emit_validate_and_profile_instruction_count (rs v) cur_pc remain_cu |
                BPF_EXIT \<Rightarrow> emit_validate_and_profile_instruction_count 0 cur_pc remain_cu |
                _ \<Rightarrow> Some(l_pc',remain_cu) in 
            if n' = None then
              BPF_EFlag
            else
              let remain_cu' = (snd (Option.the n')) in
              let l_pc' = fst (Option.the n') in
            bpf_interp2 fuel l_pc' prog (step2 pc ins rs m ss sv cur_pc remain_cu')
    else BPF_EFlag))"  

*)
end
