section \<open> Interpreter of Solana rBPF \<close>

theory Interpreter2
imports
  Main
  rBPFCommType rBPFSyntax vm_state vm Mem
  ebpf rBPFDecoder Interpreter
begin

subsubsection  \<open> Interpreter State \<close>

type_synonym target_pc ="usize"
type_synonym pc = "usize"
type_synonym insn_meter = "usize"
type_synonym last_pc = "usize"

definition emit_validate_instruction_count::"pc \<Rightarrow> insn_meter \<Rightarrow> last_pc option" where
"emit_validate_instruction_count pc im = (if pc+1 > im then Some pc else None)"

definition emit_profile_instruction_count::"target_pc \<Rightarrow> pc \<Rightarrow> insn_meter \<Rightarrow> insn_meter" where
"emit_profile_instruction_count t_pc pc im = im + (t_pc -(pc+1))"

definition emit_validate_and_profile_instruction_count::"target_pc \<Rightarrow> pc \<Rightarrow> insn_meter \<Rightarrow> (last_pc \<times> insn_meter) option"where
"emit_validate_and_profile_instruction_count t_pc pc im = (
  case emit_validate_instruction_count pc im of
  None \<Rightarrow> None |
  Some l_pc \<Rightarrow>
    let meter = emit_profile_instruction_count t_pc pc im in 
    Some (l_pc, meter))"

definition emit_undo_profile_instruction_count::"target_pc \<Rightarrow> pc \<Rightarrow> insn_meter \<Rightarrow> insn_meter" where
"emit_undo_profile_instruction_count t_pc pc im = im + (pc+1)-t_pc"


fun step2 :: "u64 \<Rightarrow> bpf_instruction \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> stack_state \<Rightarrow> SBPFV \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> bpf_state" where
"step2 pc ins rs m ss sv cur_cu remain_cu = ( let is_v1 = (case sv of V1 \<Rightarrow> True | _ \<Rightarrow> False) in
  case ins of
  BPF_ALU bop d sop \<Rightarrow> (
    case eval_alu32 bop d sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu remain_cu ) |

  BPF_ALU64 bop d sop \<Rightarrow> (
    case eval_alu64 bop d sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu remain_cu ) |

  BPF_ADD_STK i \<Rightarrow> (
    case eval_add64_imm_R10 i ss is_v1 of
    None \<Rightarrow> BPF_Err |
    Some ss' \<Rightarrow> BPF_OK (pc+1) rs m ss' sv cur_cu remain_cu ) |

  BPF_LE dst imm \<Rightarrow> (
    case eval_le dst imm rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu remain_cu ) |

  BPF_BE dst imm \<Rightarrow> (
    case eval_be dst imm rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu remain_cu ) |

  BPF_NEG32_REG dst \<Rightarrow> (
    case eval_neg32 dst rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu remain_cu ) |

  BPF_NEG64_REG dst \<Rightarrow> (
    case eval_neg64 dst rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu remain_cu ) |

  BPF_LDX chk dst sop off \<Rightarrow> (
    case eval_load chk dst sop off rs m of
    None \<Rightarrow> BPF_EFlag |
    Some rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu remain_cu ) |

  BPF_ST chk dst sop off \<Rightarrow> (
    case eval_store chk dst sop off rs m of
    None \<Rightarrow> BPF_EFlag |
    Some m' \<Rightarrow> BPF_OK (pc+1) rs m' ss sv cur_cu remain_cu ) |

  BPF_LD_IMM dst imm1 imm2  \<Rightarrow> (
    case eval_load_imm dst imm1 imm2 rs m of
    None \<Rightarrow> BPF_EFlag |
    Some rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu remain_cu ) |

  BPF_PQR pop dst sop \<Rightarrow> (
    case eval_pqr32 pop dst sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu remain_cu ) |

  BPF_PQR64 pop dst sop \<Rightarrow> (
    case eval_pqr64 pop dst sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu remain_cu ) |

  BPF_PQR2 pop dst sop \<Rightarrow> (
    case eval_pqr64_2 pop dst sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu remain_cu ) |

  BPF_HOR64_IMM dst imm \<Rightarrow> (
    case eval_hor64 dst imm rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (pc+1) rs' m ss sv cur_cu remain_cu ) |

  BPF_JA off  \<Rightarrow>
    BPF_OK (pc + scast off + 1) rs m ss sv cur_cu remain_cu  |

  BPF_JUMP cond bpf_ireg snd_op off  \<Rightarrow> (
    if eval_jmp cond bpf_ireg snd_op rs then
      BPF_OK (pc + scast off + 1) rs m ss sv cur_cu remain_cu 
    else
      let t_pc = (pc + scast off + 1); remain_cu' = emit_undo_profile_instruction_count t_pc pc remain_cu in
      BPF_OK (pc + 1) rs m ss sv cur_cu remain_cu' ) |

  BPF_CALL_IMM src imm \<Rightarrow> (
    case eval_call_imm imm rs ss is_v1  of
    None \<Rightarrow> BPF_EFlag |
    Some (pc, rs', ss') \<Rightarrow> let remain_cu' = emit_undo_profile_instruction_count 0 pc remain_cu in
    BPF_OK pc rs' m ss' sv cur_cu remain_cu' ) |

  BPF_CALL_REG src imm \<Rightarrow> (
    case eval_call_reg src imm rs ss is_v1 pc of
    None \<Rightarrow> BPF_EFlag |
    Some (pc', rs', ss') \<Rightarrow> let remain_cu' = emit_undo_profile_instruction_count 0 pc remain_cu in
    BPF_OK pc' rs' m ss' sv cur_cu remain_cu' ) |
  BPF_EXIT \<Rightarrow> (
    if call_depth ss = 0 then
        BPF_Success (rs BR1)
    else (
      let (pc', rs', ss') = eval_exit rs ss is_v1 in
        BPF_OK pc' rs' m ss' sv cur_cu remain_cu ))
)"

fun bpf_interp2 :: "nat \<Rightarrow> last_pc \<Rightarrow> bpf_bin \<Rightarrow> bpf_state \<Rightarrow> bpf_state" where
"bpf_interp2 0 _ _ _ = BPF_EFlag" | 
"bpf_interp2 (Suc fuel) l_pc prog st = (
  case st of
  BPF_EFlag \<Rightarrow> BPF_EFlag |
  BPF_Err \<Rightarrow> BPF_Err |
  BPF_CU \<Rightarrow> BPF_CU |
  BPF_Success v \<Rightarrow> BPF_Success v |
  BPF_OK pc rs m ss sv cur_pc remain_cu \<Rightarrow> (
    if INSN_SIZE*unat pc < length prog then
      if (instruction_meter_checkpoint_distance + l_pc \<le> pc) \<and> pc + 1 > remain_cu then BPF_CU
      else
        let l_pc' = if instruction_meter_checkpoint_distance + l_pc \<le> pc then pc else l_pc in 
          case bpf_find_instr (unat pc) prog of
            None \<Rightarrow> BPF_Err |
            Some ins \<Rightarrow> 
              let n' = case ins of
                BPF_JA ofs \<Rightarrow>
                  let t_pc :: u64 = pc + scast ofs + 1 in
                  emit_validate_and_profile_instruction_count t_pc pc remain_cu |
                BPF_JUMP cond bpf_ireg snd_op ofs \<Rightarrow>
                  let t_pc = pc + scast ofs + 1 in 
                  emit_validate_and_profile_instruction_count t_pc pc remain_cu |
                BPF_LD_IMM dst imm1 imm2 \<Rightarrow>
                  emit_validate_and_profile_instruction_count (pc+2) pc remain_cu |
                BPF_CALL_IMM src imm \<Rightarrow> (
                  case get_function_registry (ucast imm) of
                    None \<Rightarrow> None |
                    Some t_pc \<Rightarrow> emit_validate_and_profile_instruction_count t_pc pc remain_cu) |
                BPF_CALL_REG src imm \<Rightarrow>
                  let v = case sv of
                  V1 \<Rightarrow> Option.the (u4_to_bpf_ireg (scast imm)) |
                  V2 \<Rightarrow> src in 
                  emit_validate_and_profile_instruction_count (rs v) pc remain_cu |
                BPF_EXIT \<Rightarrow> emit_validate_and_profile_instruction_count 0 pc remain_cu |
                _ \<Rightarrow> Some(l_pc',remain_cu) in 
            if n' = None then
              BPF_CU
            else
              let remain_cu' = (snd (Option.the n')) in
              let l_pc' = fst (Option.the n') in
            bpf_interp2 fuel l_pc' prog (step2 pc ins rs m ss sv pc remain_cu')
    else BPF_EFlag))"  


end