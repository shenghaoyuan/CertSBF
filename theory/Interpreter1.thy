section \<open> Interpreter of Solana rBPF \<close>

theory Interpreter1
imports
  Main
  rBPFCommType rBPFSyntax vm_state vm Mem
  ebpf rBPFDecoder Interpreter
begin

subsubsection  \<open> Interpreter State \<close>



(*
record rbpf_state =
registers :: reg_map
memory_mapping :: mem
stack :: stack_state *)

datatype bpf_state_ty = BPF_OK1 | BPF_Success1 | BPF_EFlag1 | BPF_Err1 | BPF_CU1

datatype bpf_state1 =
  BPF_st bpf_state_ty u64 u64 reg_map mem stack_state SBPFV u64 u64
                                                     
fun bad_bpf_state1 :: "bpf_state_ty => bpf_state1" where
"bad_bpf_state1 ty = (
  BPF_st ty 0 0 (\<lambda> _. 0) (\<lambda> _. None) default_stack_state V1 0 0
)"

definition step1 :: "u64 \<Rightarrow> bpf_instruction \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> stack_state \<Rightarrow> SBPFV \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> bpf_state1" where
"step1 pc ins rs m ss sv cur_cu remain_cu = ( let is_v1 = (case sv of V1 \<Rightarrow> True | _ \<Rightarrow> False) in
  case ins of
  BPF_ALU bop d sop \<Rightarrow> (
    case eval_alu32 bop d sop rs is_v1 of
    NOK \<Rightarrow> bad_bpf_state1 BPF_Err1 |
    OKN \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    OKS rs' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs' m ss sv (cur_cu+1) remain_cu ) |

  BPF_ALU64 bop d sop \<Rightarrow> (
    case eval_alu64 bop d sop rs is_v1 of
    NOK \<Rightarrow> bad_bpf_state1 BPF_Err1 |
    OKN \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    OKS rs' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs' m ss sv (cur_cu+1) remain_cu ) |

  BPF_ADD_STK i \<Rightarrow> (
    case eval_add64_imm_R10 i ss is_v1 of
    None \<Rightarrow> bad_bpf_state1 BPF_Err1 |
    Some ss' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs m ss' sv (cur_cu+1) remain_cu ) |

  BPF_LE dst imm \<Rightarrow> (
    case eval_le dst imm rs is_v1 of
    NOK \<Rightarrow> bad_bpf_state1 BPF_Err1 |
    OKN \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    OKS rs' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs' m ss sv (cur_cu+1) remain_cu ) |

  BPF_BE dst imm \<Rightarrow> (
    case eval_be dst imm rs is_v1 of
    NOK \<Rightarrow> bad_bpf_state1 BPF_Err1 |
    OKN \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    OKS rs' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs' m ss sv (cur_cu+1) remain_cu ) |

  BPF_NEG32_REG dst \<Rightarrow> (
    case eval_neg32 dst rs is_v1 of
    NOK \<Rightarrow> bad_bpf_state1 BPF_Err1 |
    OKN \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    OKS rs' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs' m ss sv (cur_cu+1) remain_cu ) |

  BPF_NEG64_REG dst \<Rightarrow> (
    case eval_neg64 dst rs is_v1 of
    NOK \<Rightarrow> bad_bpf_state1 BPF_Err1 |
    OKN \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    OKS rs' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs' m ss sv (cur_cu+1) remain_cu ) |

  BPF_LDX chk dst sop off \<Rightarrow> (
    case eval_load chk dst sop off rs m of
    None \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    Some rs' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs' m ss sv (cur_cu+1) remain_cu ) |

  BPF_ST chk dst sop off \<Rightarrow> (
    case eval_store chk dst sop off rs m of
    None \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    Some m' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs m' ss sv (cur_cu+1) remain_cu ) |

  BPF_LD_IMM dst imm1 imm2  \<Rightarrow> (
    case eval_load_imm dst imm1 imm2 rs m of
    None \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    Some rs' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs' m ss sv (cur_cu+1) remain_cu ) |

  BPF_PQR pop dst sop \<Rightarrow> (
    case eval_pqr32 pop dst sop rs is_v1 of
    NOK \<Rightarrow> bad_bpf_state1 BPF_Err1 |
    OKN \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    OKS rs' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs' m ss sv (cur_cu+1) remain_cu ) |

  BPF_PQR64 pop dst sop \<Rightarrow> (
    case eval_pqr64 pop dst sop rs is_v1 of
    NOK \<Rightarrow> bad_bpf_state1 BPF_Err1 |
    OKN \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    OKS rs' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs' m ss sv (cur_cu+1) remain_cu ) |

  BPF_PQR2 pop dst sop \<Rightarrow> (
    case eval_pqr64_2 pop dst sop rs is_v1 of
    NOK \<Rightarrow> bad_bpf_state1 BPF_Err1 |
    OKN \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    OKS rs' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs' m ss sv (cur_cu+1) remain_cu ) |

  BPF_HOR64_IMM dst imm \<Rightarrow> (
    case eval_hor64 dst imm rs is_v1 of
    NOK \<Rightarrow> bad_bpf_state1 BPF_Err1 |
    OKN \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    OKS rs' \<Rightarrow> BPF_st BPF_OK1 (pc+1) (pc+1) rs' m ss sv (cur_cu+1) remain_cu ) |

  BPF_JA off  \<Rightarrow>
    BPF_st BPF_OK1 (pc+1) (pc + scast off + 1) rs m ss sv (cur_cu+1) remain_cu  |

  BPF_JUMP cond bpf_ireg snd_op off  \<Rightarrow> (
    if eval_jmp cond bpf_ireg snd_op rs  then
      BPF_st BPF_OK1 (pc+1) (pc + scast off + 1) rs m ss sv (cur_cu+1) remain_cu 
    else
      BPF_st BPF_OK1 (pc+1) (pc + 1) rs m ss sv (cur_cu+1) remain_cu ) |

  BPF_CALL_IMM src imm \<Rightarrow> (
    case eval_call_imm imm rs ss is_v1  of
    None \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    Some (pc, rs', ss') \<Rightarrow> BPF_st BPF_OK1 (pc+1) pc rs' m ss' sv (cur_cu+1) remain_cu ) |

  BPF_CALL_REG src imm \<Rightarrow> (
    case eval_call_reg src imm rs ss is_v1 pc of
    None \<Rightarrow> bad_bpf_state1 BPF_EFlag1 |
    Some (pc', rs', ss') \<Rightarrow> BPF_st BPF_OK1 (pc+1) pc' rs' m ss' sv (cur_cu+1) remain_cu ) |
  BPF_EXIT \<Rightarrow> (
    if call_depth ss = 0 then
      if cur_cu >  remain_cu then
        bad_bpf_state1 BPF_EFlag1
      else
        BPF_st BPF_Success1 0 pc rs m ss sv cur_cu remain_cu
    else (
      let (pc', rs', ss') = eval_exit rs ss is_v1 in
        BPF_st BPF_OK1 (pc+1) pc' rs' m ss' sv (cur_cu+1) remain_cu ))
)"

fun bpf_interp1 :: "nat \<Rightarrow> bpf_bin \<Rightarrow> bpf_state1 \<Rightarrow> bpf_state1" where
"bpf_interp1 0 _ _ = bad_bpf_state1 BPF_EFlag1 " | 
"bpf_interp1 (Suc n) prog st  = (
  case st of
  BPF_st ty lpc pc rs m ss sv cur_cu remain_cu \<Rightarrow> (
    case ty of
    BPF_OK1 \<Rightarrow> (
    if INSN_SIZE*unat pc < length prog then
      if cur_cu \<ge> remain_cu then
        bad_bpf_state1 BPF_CU1
      else
        case bpf_find_instr (unat pc) prog of
        None \<Rightarrow> bad_bpf_state1 BPF_Err1 |
        Some ins \<Rightarrow> bpf_interp1 n prog (step1 pc ins rs m ss sv cur_cu remain_cu) 
    else bad_bpf_state1 BPF_Err1) |
    _ \<Rightarrow> st )
)"

definition refine_bpf_state1 :: "bpf_state1 \<Rightarrow> bpf_state" where
"refine_bpf_state1 st = (
  case st of
  BPF_st ty lpc pc rs m ss sv cur_cu remain_cu \<Rightarrow> (
    case ty of
    BPF_OK1 \<Rightarrow> BPF_OK pc rs m ss sv cur_cu remain_cu |
    BPF_Err1 \<Rightarrow> BPF_Err |
    BPF_Success1 \<Rightarrow> BPF_Success (rs BR0) |
    BPF_CU1 \<Rightarrow> BPF_CU |
    BPF_EFlag1 \<Rightarrow> BPF_EFlag
))"

lemma bpf_step1_equiv:
" st1 = step1 pc ins rs m ss sv cur_cu remain_cu \<Longrightarrow>
  st = step pc ins rs m ss sv cur_cu remain_cu \<Longrightarrow>
  st = (refine_bpf_state1 st1)"
  apply (cases ins; simp add: step1_def step_def refine_bpf_state1_def)
  subgoal for x11 x12 x13
    apply (cases "eval_load_imm x11 x12 x13 rs m"; simp)
    done
  subgoal for x21 x22 x23 x24
    apply (cases "eval_load x21 x22 x23 x24 rs m"; simp)
    done
  subgoal for x21 x22 x23 x24
    apply (cases "eval_store x21 x22 x23 x24 rs m"; simp)
    done
  subgoal for x21
    apply (cases "eval_add64_imm_R10 x21 ss (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False)"; simp)
    done
  subgoal for x21 x22 x23
    apply (cases "eval_alu32 x21 x22 x23 rs (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False)"; simp)
    done
  subgoal for x21
    apply (cases "eval_neg32 x21 rs (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False)"; simp)
    done
  subgoal for x21 x22
    apply (cases "eval_le x21 x22 rs (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False)"; simp)
    done
  subgoal for x21 x22
    apply (cases "eval_be x21 x22 rs (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False)"; simp)
    done
  subgoal for x21 x22 x23
    apply (cases "eval_alu64 x21 x22 x23 rs (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False)"; simp)
    done
  subgoal for x21
    apply (cases "eval_neg64 x21 rs (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False)"; simp)
    done
  subgoal for x21 x22
    apply (cases "eval_hor64 x21 x22 rs (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False)"; simp)
    done
  subgoal for x21 x22 x23
    apply (cases "eval_pqr32 x21 x22 x23 rs (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False)"; simp)
    done
  subgoal for x21 x22 x23
    apply (cases "eval_pqr64 x21 x22 x23 rs (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False)"; simp)
    done
  subgoal for x21 x22 x23
    apply (cases "eval_pqr64_2 x21 x22 x23 rs (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False)"; simp)
    done
  subgoal for x21 x22
    apply (cases "eval_call_reg x21 x22 rs ss (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False) pc"; simp)
    subgoal for a 
      apply (cases a; simp)
      done
    done
  subgoal for x21 x22
    apply (cases "eval_call_imm x22 rs ss (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False)"; simp)
    subgoal for a
      apply (cases a; simp)
      done
    done
  subgoal
    apply (cases "stack_state.call_depth ss = 0"; simp)
    apply (cases "eval_exit rs ss (case sv of V1 \<Rightarrow> enable_instruction_meter | V2 \<Rightarrow> False)"; simp)
    done
  done


theorem bpf_interp1_equiv:
" st1 = bpf_interp1 n l st0 \<Longrightarrow>
  st = bpf_interp n l (refine_bpf_state1 st0) \<Longrightarrow>
  st = (refine_bpf_state1 st1)"
  apply (induction n arbitrary: l st0 st1 st, simp add: refine_bpf_state1_def)
  subgoal for k l st0 st1 st
    apply simp
    apply (cases st0)
    subgoal for x1 x2 x3 x4 x5 x6 x7 x8 x9
      apply (simp add: refine_bpf_state1_def)
      apply (cases x1; simp)
      apply (cases "INSN_SIZE * unat x3 < length l"; simp)
      apply (cases "x9 \<le> x8"; simp)
      apply (cases "bpf_find_instr (unat x3) l"; simp)
      subgoal for a
        apply (subgoal_tac "step x3 a x4 x5 x6 x7 x8 x9 = (refine_bpf_state1 (step1 x3 a x4 x5 x6 x7 x8 x9))")
         prefer 2
        subgoal
          using bpf_step1_equiv
          apply simp
          done
        apply simp
        apply (cases "step1 x3 a x4 x5 x6 x7 x8 x9"; simp add: refine_bpf_state1_def)
        done
      done
    done
  done

end