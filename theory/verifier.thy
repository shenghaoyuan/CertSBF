section \<open> Verifier of Solana rBPF \<close>

theory verifier
imports
  Main
  rBPFCommType rBPFSyntax
  ebpf rustCommType vm
begin

datatype VerifierError =
    ProgramLengthNotMultiple
  | NoProgram
  | DivisionByZero (* usize *)
  | UnsupportedLEBEArgument (*usize *)
  | LDDWCannotBeLast
  | IncompleteLDDW (*usize *)
  | InfiniteLoop (*usize *)
  | JumpOutOfCode (* usize usize *)
  | JumpToMiddleOfLDDW (* usize usize *)
  | InvalidSourceRegister (*usize *)
  | CannotWriteR10 (*usize *)
  | InvalidDestinationRegister (*usize *)
  | UnknownOpCode (* u8 usize *)
  | ShiftWithOverflow  (* u64 u64 usize *)
  | InvalidRegister (*usize *)
  | InvalidFunction (*usize *)

definition check_prog_len :: "u8 list \<Rightarrow> (unit, VerifierError) Result" where
"check_prog_len prog = (
  if (length prog) mod INSN_SIZE \<noteq> 0 then
    Err ProgramLengthNotMultiple
  else if length prog = 0 then
    Err NoProgram
  else
    Ok ()
)"

definition check_imm_nonzero :: "snd_op \<Rightarrow> (bool, VerifierError) Result" where
" check_imm_nonzero sop = (
    case sop of
    SOImm i \<Rightarrow> if i = 0 then Err DivisionByZero else Ok False |
    SOReg _ \<Rightarrow> Ok False
)"

definition check_jmp_offset :: "off_ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (bool, VerifierError) Result" where
" check_jmp_offset o1 insn_ptr len = (
  let (dst_ptr::i64) = (of_nat insn_ptr) + ((scast o1)::i64) + 1 in
    if 0 \<le> dst_ptr \<and> dst_ptr < (of_nat len) then Ok False
    else Err JumpOutOfCode
)"

definition verify_one :: "bpf_instruction \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> SBPFV \<Rightarrow>
 func_map \<Rightarrow> Config \<Rightarrow> (bool, VerifierError) Result" where
"verify_one insn len insn_ptr sbpf_version fr conf = (
  case insn of
  BPF_LD_IMM  dst i1 i2    \<Rightarrow> (
    if sbpf_version \<noteq> V1 then
      Err UnknownOpCode
    else if (insn_ptr + 1) \<ge> len then
      Err LDDWCannotBeLast
    else
      Ok False) |

  BPF_LDX _ _ _ _ \<Rightarrow> Ok False |

  BPF_ST  mc  dst sop off  \<Rightarrow> Ok True |

  BPF_ALU bop dst sop \<Rightarrow> (
    case bop of
    BPF_MUL \<Rightarrow> if sbpf_version = V1 then Ok False else Err UnknownOpCode |

    BPF_DIV \<Rightarrow> if sbpf_version = V1 then check_imm_nonzero sop
               else Err UnknownOpCode |
    BPF_MOD \<Rightarrow> if sbpf_version = V1 then check_imm_nonzero sop
               else Err UnknownOpCode |

    BPF_LSH \<Rightarrow> (
      case sop of
      SOImm i \<Rightarrow> if 0 \<le> i \<and> i < 32 then Ok False else Err ShiftWithOverflow |
      SOReg _ \<Rightarrow> Ok False) |
    BPF_RSH \<Rightarrow>  (
      case sop of
      SOImm i \<Rightarrow> if 0 \<le> i \<and> i < 32 then Ok False else Err ShiftWithOverflow |
      SOReg _ \<Rightarrow> Ok False) |
    BPF_ARSH \<Rightarrow> (
      case sop of
      SOImm i \<Rightarrow> if 0 \<le> i \<and> i < 32 then Ok False else Err ShiftWithOverflow |
      SOReg _ \<Rightarrow> Ok False)
  ) |

  BPF_NEG32_REG _ \<Rightarrow> if sbpf_version = V1 then Ok False else Err UnknownOpCode |

  BPF_LE dst i \<Rightarrow>
    if sbpf_version = V1 then
      if i = 16 \<or> i = 32 \<or> i = 64 then Ok False
      else Err UnsupportedLEBEArgument
    else Err UnknownOpCode |

  BPF_BE dst i \<Rightarrow> if i = 16 \<or> i = 32 \<or> i = 64 then Ok False
                  else Err UnsupportedLEBEArgument |

  BPF_ALU64 bop dst sop \<Rightarrow> (
    case bop of
    BPF_MUL \<Rightarrow> if sbpf_version = V1 then Ok False else Err UnknownOpCode |

    BPF_DIV \<Rightarrow> if sbpf_version = V1 then check_imm_nonzero sop
               else Err UnknownOpCode |
    BPF_MOD \<Rightarrow> if sbpf_version = V1 then check_imm_nonzero sop
               else Err UnknownOpCode |

    BPF_LSH \<Rightarrow> (
      case sop of
      SOImm i \<Rightarrow> if 0 \<le> i \<and> i < 64 then Ok False else Err ShiftWithOverflow |
      SOReg _ \<Rightarrow> Ok False) |
    BPF_RSH \<Rightarrow>  (
      case sop of
      SOImm i \<Rightarrow> if 0 \<le> i \<and> i < 64 then Ok False else Err ShiftWithOverflow |
      SOReg _ \<Rightarrow> Ok False) |
    BPF_ARSH \<Rightarrow> (
      case sop of
      SOImm i \<Rightarrow> if 0 \<le> i \<and> i < 64 then Ok False else Err ShiftWithOverflow |
      SOReg _ \<Rightarrow> Ok False)
  ) |

  BPF_NEG64_REG _ \<Rightarrow> if sbpf_version = V1 then Ok False else Err UnknownOpCode |

  BPF_HOR64_IMM _ _ \<Rightarrow> if sbpf_version \<noteq> V1 then Ok False else Err UnknownOpCode |

  BPF_PQR     pop dst sop \<Rightarrow> if sbpf_version = V1 then Err UnknownOpCode else (
    case pop of
    BPF_UDIV \<Rightarrow> check_imm_nonzero sop |
    BPF_UREM \<Rightarrow> check_imm_nonzero sop |
    BPF_SDIV \<Rightarrow> check_imm_nonzero sop |
    BPF_SREM \<Rightarrow> check_imm_nonzero sop |
    _ \<Rightarrow> Ok False
  ) |

  BPF_PQR64   pop dst sop \<Rightarrow> if sbpf_version = V1 then Err UnknownOpCode else (
    case pop of
    BPF_UDIV \<Rightarrow> check_imm_nonzero sop |
    BPF_UREM \<Rightarrow> check_imm_nonzero sop |
    BPF_SDIV \<Rightarrow> check_imm_nonzero sop |
    BPF_SREM \<Rightarrow> check_imm_nonzero sop |
    _ \<Rightarrow> Ok False
  ) |

  BPF_PQR2 pop2 dst sop \<Rightarrow> if sbpf_version = V1 then Err UnknownOpCode else Ok False |

  BPF_JA off \<Rightarrow> check_jmp_offset off insn_ptr len |
  BPF_JUMP cop dst sop off \<Rightarrow> check_jmp_offset off insn_ptr len |
  BPF_CALL_IMM src i1 \<Rightarrow> (
    if sbpf_version \<noteq> V1 \<and> src \<noteq> BR0 then (
      case fr (ucast i1) of
      None \<Rightarrow> Err InvalidFunction |
      Some _ \<Rightarrow> Ok False
      )
    else Ok False) |

  BPF_CALL_REG src i1 \<Rightarrow> (
    let (reg::i64) = if sbpf_version \<noteq> V1 then ucast (bpf_ireg2u4 src)
                     else (scast i1) in
      if reg < 0 \<or> 10 < reg \<or> (reg = 10 \<and> (reject_callx_r10 conf)) then
        Err InvalidRegister
      else Ok False
  ) |

  BPF_EXIT \<Rightarrow> Ok False
)"

end