section \<open> The Safety proof of the Interpreter in Solana rBPF \<close>

theory VerifierSafety
imports
  Main
  rBPFCommType rBPFSyntax vm_state vm Mem
  ebpf rBPFDecoder BitsOpMore2 BitsOpMore3 BitsOpMore4
  verifier Interpreter
begin

declare if_split_asm [split]

lemma verifier_step_safe: "verify_one ins l pc len sv fr reject_callx_r10 \<Longrightarrow>
  step (of_nat pc) ins rs m ss sv fm enable_stack_frame_gaps program_vm_addr (cur_cu+1) remain_cu \<noteq> BPF_Err"
  apply (unfold verify_one_def)

  apply (cases ins; simp)
  subgoal for x21 x22 x23 x24
    apply (cases "eval_load x21 x22 x23 x24 rs m"; simp)
    done

  subgoal for x31 x32 x33 x34
    apply (cases "eval_store x31 x32 x33 x34 rs m"; simp)
    done

  subgoal for x41
    apply (cases sv; simp)
    apply (unfold eval_add64_imm_R10_def Let_def; simp)
    done

  subgoal for x51 x52 x53
    apply (cases x51; cases sv; cases x53; simp add: eval_alu32_def eval_alu32_aux1_def
        eval_alu32_aux2_def eval_alu32_aux3_def check_imm_nonzero_def Let_def)
    subgoal for x1
      by (metis cast_lemma4 scast_0 ucast_id)

    subgoal for x1
      by (metis cast_lemma4 scast_0 ucast_id)

    done

  subgoal for x51 x52 x53
    apply (cases x51; cases sv; cases x53; simp add: eval_alu32_def eval_alu32_aux1_def
        eval_alu32_aux2_def eval_alu32_aux3_def check_imm_nonzero_def Let_def)
    done

  subgoal for x6
    apply (unfold eval_neg32_def, simp)
    done

  subgoal for x71 x72
    apply (simp add: eval_le_def Let_def)

    using u64_of_u8_list_same u32_of_u8_list_same u16_of_u8_list_same
    by (smt (verit) bpf_state.distinct(5) option.simps(5) option2.simps(9))

  subgoal for x81 x82
    apply (simp add: eval_be_def Let_def)
    apply (cases sv; simp)

    apply (cases "u64_of_u8_list (rev (u8_list_of_u64 (eval_reg x81 rs)))"; 
           cases "u32_of_u8_list (rev (u8_list_of_u32 (ucast (eval_reg x81 rs))))";
           cases "u16_of_u8_list (rev (u8_list_of_u16 (ucast (eval_reg x81 rs))))"; simp)
    done

  subgoal for x91 x92 x93
    apply (cases x91; cases x93; simp add: check_imm_nonzero_def eval_alu64_def eval_alu64_aux1_def
        eval_alu64_aux2_def eval_alu64_aux3_def Let_def)

    subgoal
      by (metis cast_lemma4 cast_lemma4 scast_0 ucast_id) 
    subgoal
      by (metis cast_lemma4 cast_lemma4 scast_0 ucast_id) 
    done

  subgoal for x91 x92 x93
    apply (cases x91; cases sv; simp add: eval_alu64_def eval_alu64_aux1_def
        eval_alu64_aux2_def eval_alu64_aux3_def Let_def)
    apply (cases x93; simp)
    done

  subgoal for x10
    apply (simp add: eval_neg64_def)
    done

  subgoal for x111 x112
    apply (simp add: eval_hor64_def)
    done

  subgoal for x121 x122 x123
    apply (cases sv; cases x121; cases x123; simp add: check_imm_nonzero_def eval_pqr32_def
        eval_pqr32_aux1_def eval_pqr32_aux2_def Let_def)
    subgoal for x1
      by (metis cast_lemma4 scast_0 ucast_id)
    subgoal for x1
      by (metis cast_lemma4 scast_0 ucast_id)
    done

  subgoal for x131 x132 x133
    apply (cases x131; cases sv; cases x133; simp add: check_imm_nonzero_def eval_pqr64_def
        eval_pqr64_aux1_def eval_pqr64_aux2_def Let_def)
    subgoal
      by (metis cast_lemma4 cast_lemma4 scast_0 ucast_id) 
    subgoal
      by (metis cast_lemma4 cast_lemma4 scast_0 ucast_id) 
    subgoal
      by (metis cast_lemma4 cast_lemma4 scast_0 ucast_id) 
    subgoal
      by (metis cast_lemma4 cast_lemma4 scast_0 ucast_id) 
    done

  subgoal for x141 x142 x143
    apply (cases x141; simp add: eval_pqr64_2_def)
    done

  subgoal for x171 x172
    apply (cases "eval_call_reg x171 x172 rs ss (case sv of V1 \<Rightarrow> True | V2 \<Rightarrow> False)
      (word_of_nat pc) fm enable_stack_frame_gaps program_vm_addr"; simp)
    subgoal for a
      apply (cases a; simp)
      done
    done

  subgoal for x171 x172
    apply (cases "eval_call_reg x171 x172 rs ss True (word_of_nat pc)
  fm enable_stack_frame_gaps program_vm_addr"; simp)
    subgoal for a
      apply (cases a; simp)
      done
    done

  subgoal for x181 x182
    apply (cases "fr (ucast x182)"; simp)
    subgoal for a
      apply (cases "eval_call_imm (word_of_nat pc) x181 x182 rs ss
        (case sv of V1 \<Rightarrow> True | V2 \<Rightarrow> False) fm enable_stack_frame_gaps"; simp)
      subgoal for aa
        apply (cases aa; simp)
        done
      done
    done

  subgoal for x181 x182
    apply (cases "eval_call_imm (word_of_nat pc) x181 x182 rs ss
      (case sv of V1 \<Rightarrow> True | V2 \<Rightarrow> False) fm enable_stack_frame_gaps"; simp)
    subgoal for a
      apply (cases a; simp)
      done
    done

  subgoal
    apply (cases "eval_exit rs ss (case sv of V1 \<Rightarrow> True | V2 \<Rightarrow> False)"; simp)
    done
  done

declare if_split_asm [split del]
end