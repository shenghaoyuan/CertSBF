section \<open> Verifier of Solana rBPF \<close>

theory verifier
imports
  Main
  rBPFCommType rBPFSyntax rBPFDecoder
  ebpf rustCommType vm
begin

(*
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
  | InvalidFunction (*usize *) *)

definition check_prog_len :: "u8 list \<Rightarrow> bool" where
"check_prog_len prog = (
  if (length prog) mod INSN_SIZE \<noteq> 0 then
    False
  else if length prog = 0 then
    False
  else
    True
)"

definition check_imm_nonzero :: "snd_op \<Rightarrow> bool" where
" check_imm_nonzero sop = (
    case sop of
    SOImm i \<Rightarrow> if i = 0 then False else True |
    SOReg _ \<Rightarrow> True
)"

definition check_jmp_offset :: "off_ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
" check_jmp_offset o1 insn_ptr len = (
  let (dst_ptr::i64) = (of_nat insn_ptr) + ((scast o1)::i64) + 1 in
    if 0 \<le> dst_ptr \<and> dst_ptr < (of_nat len) then True
    else False
)"


definition check_load_dw :: "u8 list \<Rightarrow> nat \<Rightarrow> bool" where
"check_load_dw l insn_ptr = (
  if (insn_ptr+1)* INSN_SIZE \<ge> length l then
    False
  else
    l!((insn_ptr+1)* INSN_SIZE) = 0
)"

definition verify_one :: "bpf_instruction \<Rightarrow> u8 list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> SBPFV \<Rightarrow>
 func_map \<Rightarrow> Config \<Rightarrow> bool" where
"verify_one insn l len insn_ptr sbpf_version fr conf = (
  case insn of
  BPF_LD_IMM  dst i1 i2    \<Rightarrow> (
    if sbpf_version = V1 then
      check_load_dw l insn_ptr
    else
      False) |

  BPF_LDX _ _ _ _ \<Rightarrow> True |

  BPF_ST  _ _ _ _  \<Rightarrow> True |

  BPF_ALU bop dst sop \<Rightarrow> (
    case bop of
    BPF_MUL \<Rightarrow> if sbpf_version = V1 then True else False |

    BPF_DIV \<Rightarrow> if sbpf_version = V1 then check_imm_nonzero sop
               else False |
    BPF_MOD \<Rightarrow> if sbpf_version = V1 then check_imm_nonzero sop
               else False |

    BPF_LSH \<Rightarrow> (
      case sop of
      SOImm i \<Rightarrow> if 0 \<le> i \<and> i < 32 then True else False |
      SOReg _ \<Rightarrow> True) |
    BPF_RSH \<Rightarrow>  (
      case sop of
      SOImm i \<Rightarrow> if 0 \<le> i \<and> i < 32 then True else False |
      SOReg _ \<Rightarrow> True) |
    BPF_ARSH \<Rightarrow> (
      case sop of
      SOImm i \<Rightarrow> if 0 \<le> i \<and> i < 32 then True else False |
      SOReg _ \<Rightarrow> True)
  ) |

  BPF_NEG32_REG _ \<Rightarrow> if sbpf_version = V1 then True else False |

  BPF_LE dst i \<Rightarrow>
    if sbpf_version = V1 then
      if i = 16 \<or> i = 32 \<or> i = 64 then True
      else False
    else False |

  BPF_BE dst i \<Rightarrow> if i = 16 \<or> i = 32 \<or> i = 64 then True
                  else False |

  BPF_ALU64 bop dst sop \<Rightarrow> (
    case bop of
    BPF_MUL \<Rightarrow> if sbpf_version = V1 then True else False |

    BPF_DIV \<Rightarrow> if sbpf_version = V1 then check_imm_nonzero sop
               else False |
    BPF_MOD \<Rightarrow> if sbpf_version = V1 then check_imm_nonzero sop
               else False |

    BPF_LSH \<Rightarrow> (
      case sop of
      SOImm i \<Rightarrow> if 0 \<le> i \<and> i < 64 then True else False |
      SOReg _ \<Rightarrow> True) |
    BPF_RSH \<Rightarrow>  (
      case sop of
      SOImm i \<Rightarrow> if 0 \<le> i \<and> i < 64 then True else False |
      SOReg _ \<Rightarrow> True) |
    BPF_ARSH \<Rightarrow> (
      case sop of
      SOImm i \<Rightarrow> if 0 \<le> i \<and> i < 64 then True else False |
      SOReg _ \<Rightarrow> True)
  ) |

  BPF_NEG64_REG _ \<Rightarrow> if sbpf_version = V1 then True else False |

  BPF_HOR64_IMM _ _ \<Rightarrow> if sbpf_version \<noteq> V1 then True else False |

  BPF_PQR     pop dst sop \<Rightarrow> if sbpf_version = V1 then False else (
    case pop of
    BPF_UDIV \<Rightarrow> check_imm_nonzero sop |
    BPF_UREM \<Rightarrow> check_imm_nonzero sop |
    BPF_SDIV \<Rightarrow> check_imm_nonzero sop |
    BPF_SREM \<Rightarrow> check_imm_nonzero sop |
    _ \<Rightarrow> True
  ) |

  BPF_PQR64   pop dst sop \<Rightarrow> if sbpf_version = V1 then False else (
    case pop of
    BPF_UDIV \<Rightarrow> check_imm_nonzero sop |
    BPF_UREM \<Rightarrow> check_imm_nonzero sop |
    BPF_SDIV \<Rightarrow> check_imm_nonzero sop |
    BPF_SREM \<Rightarrow> check_imm_nonzero sop |
    _ \<Rightarrow> True
  ) |

  BPF_PQR2 pop2 dst sop \<Rightarrow> if sbpf_version = V1 then False else True |

  BPF_JA off \<Rightarrow> check_jmp_offset off insn_ptr len |
  BPF_JUMP cop dst sop off \<Rightarrow> check_jmp_offset off insn_ptr len |
  BPF_CALL_IMM src i1 \<Rightarrow> (
    if sbpf_version \<noteq> V1 \<and> src \<noteq> BR0 then (
      case fr (ucast i1) of
      None \<Rightarrow> False |
      Some _ \<Rightarrow> True
      )
    else True) |

  BPF_CALL_REG src i1 \<Rightarrow> (
    let (reg::i64) = if sbpf_version \<noteq> V1 then ucast (bpf_ireg2u4 src)
                     else (scast i1) in
      if reg < 0 \<or> 10 < reg \<or> (reg = 10 \<and> (reject_callx_r10 conf)) then
        False
      else True
  ) |

  BPF_EXIT \<Rightarrow> True
)"

definition is_store :: "bpf_instruction \<Rightarrow> bool" where
"is_store ins = (
  case ins of
  BPF_ST _ _ _ _ \<Rightarrow> True |
  _ \<Rightarrow> False
)"

definition is_lddw_imm :: "bpf_instruction \<Rightarrow> bool" where
"is_lddw_imm ins = (
  case ins of
  BPF_LD_IMM _ _ _ \<Rightarrow> True |
  _ \<Rightarrow> False
)"

definition check_registers :: "u8 list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> SBPFV \<Rightarrow> bool" where
"check_registers l store pc sbpf_version = (
  let op = l!(pc*INSN_SIZE) in
  let reg = l!(pc*INSN_SIZE + 1) in
  let dst = unsigned_bitfield_extract_u8 0 4 reg in
  let src = unsigned_bitfield_extract_u8 4 4 reg in
    if src > 10 then
      False
    else
      if (0 \<le> dst \<and> dst \<le> 9) \<or> (dst = 10 \<and> store = True) then
        True
      else
        if dst = 11 \<and> sbpf_version \<noteq> V1 \<and> op = 0x07 then
          True
        else
          False
)"

fun verifier :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> u8 list \<Rightarrow> SBPFV \<Rightarrow>
 func_map \<Rightarrow> Config \<Rightarrow> bool" where
"verifier fuel pc len l sbpf_version fr conf = (
  case fuel of
  0 \<Rightarrow> False |
  Suc n \<Rightarrow> (
    case bpf_find_instr pc l of
    None \<Rightarrow> False |
    Some ins \<Rightarrow>
      if verify_one ins l pc len sbpf_version fr conf then
        if check_registers l (is_store ins) pc sbpf_version then
          verifier n (if is_lddw_imm ins then pc + 2 else pc + 1)
            len l sbpf_version fr conf
        else
          False
      else
        False
    )
)"

end