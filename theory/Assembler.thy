theory Assembler
imports
  Main (*
  "HOL.Bit_Operations" "HOL-Library.Word" *)
  rBPFCommType rBPFSyntax
begin

definition insn :: "u8 \<Rightarrow> i64 \<Rightarrow> i64 \<Rightarrow> i64 \<Rightarrow> i64 \<Rightarrow> ebpf_binary option" where
"insn opc dst src off imm = 
  ( if dst <s 0 \<or> 10 <s dst then None else
    if src <s 0 \<or> 10 <s src then None else
    if off <s (-32768) \<or> 32767 <s off then None else
    if imm <s (-2147483648) \<or> 2147483647 <s imm then None else
      Some \<lparr> bpf_opc = opc,
            bpf_dst = (ucast dst),
            bpf_src = (ucast src),
            bpf_off = (scast off),
            bpf_imm = (scast imm) \<rparr> )"

fun ldx_chunk2opcode :: "chunk \<Rightarrow> u8" where
"ldx_chunk2opcode Byte = 0x71" |
"ldx_chunk2opcode HalfWord = 0x69" |
"ldx_chunk2opcode SWord = 0x61" |
"ldx_chunk2opcode DWord = 0x79"

fun st_chunk2opcode :: "chunk \<Rightarrow> snd_op \<Rightarrow> u8" where
"st_chunk2opcode Byte (SOImm _) = 0x72" |
"st_chunk2opcode Byte (SOReg _) = 0x73" |
"st_chunk2opcode HalfWord (SOImm _) = 0x6a" |
"st_chunk2opcode HalfWord (SOReg _) = 0x6b" |
"st_chunk2opcode SWord (SOImm _) = 0x62" |
"st_chunk2opcode SWord (SOReg _) = 0x63" |
"st_chunk2opcode DWord (SOImm _) = 0x7a" |
"st_chunk2opcode DWord (SOReg _) = 0x7b"

fun alu2opcode :: "binop \<Rightarrow> snd_op \<Rightarrow> u8" where
"alu2opcode BPF_ADD (SOImm _) = 0x04" |
"alu2opcode BPF_ADD (SOReg _) = 0x0c" |
"alu2opcode BPF_SUB (SOImm _) = 0x14" |
"alu2opcode BPF_SUB (SOReg _) = 0x1c" |
"alu2opcode BPF_MUL (SOImm _) = 0x24" |
"alu2opcode BPF_MUL (SOReg _) = 0x2c" |
"alu2opcode BPF_DIV (SOImm _) = 0x34" |
"alu2opcode BPF_DIV (SOReg _) = 0x3c" |
"alu2opcode BPF_OR  (SOImm _) = 0x44" |
"alu2opcode BPF_OR  (SOReg _) = 0x4c" |
"alu2opcode BPF_AND (SOImm _) = 0x54" |
"alu2opcode BPF_AND (SOReg _) = 0x5c" |
"alu2opcode BPF_LSH (SOImm _) = 0x64" |
"alu2opcode BPF_LSH (SOReg _) = 0x6c" |
"alu2opcode BPF_RSH (SOImm _) = 0x74" |
"alu2opcode BPF_RSH (SOReg _) = 0x7c" |
"alu2opcode BPF_MOD (SOImm _) = 0x94" |
"alu2opcode BPF_MOD (SOReg _) = 0x9c" |
"alu2opcode BPF_XOR (SOImm _) = 0xa4" |
"alu2opcode BPF_XOR (SOReg _) = 0xac" |
"alu2opcode BPF_MOV (SOImm _) = 0xb4" |
"alu2opcode BPF_MOV (SOReg _) = 0xbc" |
"alu2opcode BPF_ARSH (SOImm _) = 0xc4" |
"alu2opcode BPF_ARSH (SOReg _) = 0xcc"

fun alu642opcode :: "binop \<Rightarrow> snd_op \<Rightarrow> u8" where
"alu642opcode BPF_ADD (SOImm _) = 0x07" |
"alu642opcode BPF_ADD (SOReg _) = 0x0f" |
"alu642opcode BPF_SUB (SOImm _) = 0x17" |
"alu642opcode BPF_SUB (SOReg _) = 0x1f" |
"alu642opcode BPF_MUL (SOImm _) = 0x27" |
"alu642opcode BPF_MUL (SOReg _) = 0x2f" |
"alu642opcode BPF_DIV (SOImm _) = 0x37" |
"alu642opcode BPF_DIV (SOReg _) = 0x3f" |
"alu642opcode BPF_OR  (SOImm _) = 0x47" |
"alu642opcode BPF_OR  (SOReg _) = 0x4f" |
"alu642opcode BPF_AND (SOImm _) = 0x57" |
"alu642opcode BPF_AND (SOReg _) = 0x5f" |
"alu642opcode BPF_LSH (SOImm _) = 0x67" |
"alu642opcode BPF_LSH (SOReg _) = 0x6f" |
"alu642opcode BPF_RSH (SOImm _) = 0x77" |
"alu642opcode BPF_RSH (SOReg _) = 0x7f" |
"alu642opcode BPF_MOD (SOImm _) = 0x97" |
"alu642opcode BPF_MOD (SOReg _) = 0x9f" |
"alu642opcode BPF_XOR (SOImm _) = 0xa7" |
"alu642opcode BPF_XOR (SOReg _) = 0xaf" |
"alu642opcode BPF_MOV (SOImm _) = 0xb7" |
"alu642opcode BPF_MOV (SOReg _) = 0xbf" |
"alu642opcode BPF_ARSH (SOImm _) = 0xc7" |
"alu642opcode BPF_ARSH (SOReg _) = 0xcf"

fun snd_op2i64 :: "snd_op \<Rightarrow> i64" where
"snd_op2i64 (SOReg ir) = (bpf_ireg2i64 ir)" |
"snd_op2i64 (SOImm im) = (scast im)"

fun pqr2opcode :: "pqrop \<Rightarrow> snd_op \<Rightarrow> u8" where
"pqr2opcode BPF_LMUL (SOImm _) = 0x86" |
"pqr2opcode BPF_LMUL (SOReg _) = 0x8e" |
"pqr2opcode BPF_UDIV (SOImm _) = 0x46" |
"pqr2opcode BPF_UDIV (SOReg _) = 0x4e" |
"pqr2opcode BPF_UREM (SOImm _) = 0x66" |
"pqr2opcode BPF_UREM (SOReg _) = 0x6e" |
"pqr2opcode BPF_SDIV (SOImm _) = 0xc6" |
"pqr2opcode BPF_SDIV (SOReg _) = 0xce" |
"pqr2opcode BPF_SREM (SOImm _) = 0xe6" |
"pqr2opcode BPF_SREM (SOReg _) = 0xee"

fun pqr642opcode :: "pqrop \<Rightarrow> snd_op \<Rightarrow> u8" where
"pqr642opcode BPF_LMUL (SOImm _) = 0x96" |
"pqr642opcode BPF_LMUL (SOReg _) = 0x9e" |
"pqr642opcode BPF_UDIV (SOImm _) = 0x56" |
"pqr642opcode BPF_UDIV (SOReg _) = 0x5e" |
"pqr642opcode BPF_UREM (SOImm _) = 0x76" |
"pqr642opcode BPF_UREM (SOReg _) = 0x7e" |
"pqr642opcode BPF_SDIV (SOImm _) = 0xd6" |
"pqr642opcode BPF_SDIV (SOReg _) = 0xde" |
"pqr642opcode BPF_SREM (SOImm _) = 0xf6" |
"pqr642opcode BPF_SREM (SOReg _) = 0xfe"

fun pqr22opcode :: "pqrop2 \<Rightarrow> snd_op \<Rightarrow> u8" where
"pqr22opcode BPF_UHMUL (SOImm _) = 0x36" |
"pqr22opcode BPF_UHMUL (SOReg _) = 0x3e" |
"pqr22opcode BPF_SHMUL (SOImm _) = 0xb6" |
"pqr22opcode BPF_SHMUL (SOReg _) = 0xbe"


fun condition2opcode :: "condition \<Rightarrow> snd_op \<Rightarrow> u8" where
"condition2opcode Eq  (SOImm _) = 0x15" |
"condition2opcode Eq  (SOReg _) = 0x1d" |
"condition2opcode Gt  (SOImm _) = 0x25" |
"condition2opcode Gt  (SOReg _) = 0x2d" |
"condition2opcode Ge  (SOImm _) = 0x35" |
"condition2opcode Ge  (SOReg _) = 0x3d" |
"condition2opcode Lt  (SOImm _) = 0xa5" |
"condition2opcode Lt  (SOReg _) = 0xad" |
"condition2opcode Le  (SOImm _) = 0xb5" |
"condition2opcode Le  (SOReg _) = 0xbd" |
"condition2opcode SEt (SOImm _) = 0x45" |
"condition2opcode SEt (SOReg _) = 0x4d" |
"condition2opcode Ne  (SOImm _) = 0x55" |
"condition2opcode Ne  (SOReg _) = 0x5d" |
"condition2opcode SGt (SOImm _) = 0x65" |
"condition2opcode SGt (SOReg _) = 0x6d" |
"condition2opcode SGe (SOImm _) = 0x75" |
"condition2opcode SGe (SOReg _) = 0x7d" |
"condition2opcode SLt (SOImm _) = 0xc5" |
"condition2opcode SLt (SOReg _) = 0xcd" |
"condition2opcode SLe (SOImm _) = 0xd5" |
"condition2opcode SLe (SOReg _) = 0xdd"

fun assemble_one_instruction :: "bpf_instruction \<Rightarrow> ebpf_binary option" where
"assemble_one_instruction (BPF_LD_IMM dst i1 i2) =
  insn 0x18 (bpf_ireg2i64 dst) 0 0 (scast i1)" |
"assemble_one_instruction (BPF_LDX ck dst src off) =
  insn (ldx_chunk2opcode ck) (bpf_ireg2i64 dst) (bpf_ireg2i64 src) (scast off) 0" |
"assemble_one_instruction (BPF_ST ck dst src off) =
  insn (st_chunk2opcode ck src) (bpf_ireg2i64 dst) (snd_op2i64 src) (scast off) 0" |
  
"assemble_one_instruction (BPF_NEG32_REG dst) =
  insn 0x84 (bpf_ireg2i64 dst) 0 0 0" |
"assemble_one_instruction (BPF_NEG64_REG dst) =
  insn 0x87 (bpf_ireg2i64 dst) 0 0 0" |
  
"assemble_one_instruction (BPF_ALU bop dst src) =
  insn (alu2opcode bop src) (bpf_ireg2i64 dst) (snd_op2i64 src) 0 0" |
"assemble_one_instruction (BPF_LE dst imm) =
  insn 0xd4 (bpf_ireg2i64 dst) 0 0 (scast imm)" |
"assemble_one_instruction (BPF_BE dst imm) =
  insn 0xdc (bpf_ireg2i64 dst) 0 0 (scast imm)" |
  
"assemble_one_instruction (BPF_ALU64 bop dst src) =
  insn (alu642opcode bop src) (bpf_ireg2i64 dst) (snd_op2i64 src) 0 0" |
"assemble_one_instruction (BPF_HOR64_IMM dst imm) =
  insn 0xf7 (bpf_ireg2i64 dst) 0 0 (scast imm)" |
  
"assemble_one_instruction (BPF_PQR pop dst src) =
  insn (pqr2opcode pop src) (bpf_ireg2i64 dst) (snd_op2i64 src) 0 0" |
"assemble_one_instruction (BPF_PQR64 pop dst src) =
  insn (pqr642opcode pop src) (bpf_ireg2i64 dst) (snd_op2i64 src) 0 0" |
"assemble_one_instruction (BPF_PQR2 pop dst src) =
  insn (pqr22opcode pop src) (bpf_ireg2i64 dst) (snd_op2i64 src) 0 0" |
  
"assemble_one_instruction (BPF_JA off) =
  insn 0x5 0 0 (scast off) 0" |
"assemble_one_instruction (BPF_JUMP cop dst src off) =
  insn (condition2opcode cop src) (bpf_ireg2i64 dst) (snd_op2i64 src) (scast off) 0" |
  
"assemble_one_instruction (BPF_CALL_REG src imm) =
  insn 0x8d 0 (bpf_ireg2i64 src) 0 (scast imm)" |
"assemble_one_instruction (BPF_CALL_IMM src imm) =
  insn 0x85 0 (bpf_ireg2i64 src) 0 (scast imm)" |
  
"assemble_one_instruction BPF_EXIT = insn 0x95 0 0 0 0"


  (*
definition st_chunk2opcode :: "chunk \<Rightarrow> snd_op \<Rightarrow> u8" where
"st_chunk2opcode ck sop = (
  case ck of
  Byte \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x72 |
    (SOReg _) \<Rightarrow> 0x73) |
  HalfWord \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x6a |
    (SOReg _) \<Rightarrow> 0x6b) |
  SWord \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x62 |
    (SOReg _) \<Rightarrow> 0x63) |
  DWord \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x7a |
    (SOReg _) \<Rightarrow> 0x7b))"

definition alu2opcode :: "binop \<Rightarrow> snd_op \<Rightarrow> u8" where
"alu2opcode bop sop = (
  case bop of 
  BPF_ADD \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x04 |
    (SOReg _) \<Rightarrow> 0x0c) |
  BPF_SUB \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x14 |
    (SOReg _) \<Rightarrow> 0x1c) |
  BPF_MUL \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x24 |
    (SOReg _) \<Rightarrow> 0x2c) |
  BPF_DIV \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x34 |
    (SOReg _) \<Rightarrow> 0x3c) |
  BPF_OR \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x44 |
    (SOReg _) \<Rightarrow> 0x4c) |
  BPF_AND \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x54 |
    (SOReg _) \<Rightarrow> 0x5c) |
  BPF_LSH \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x64 |
    (SOReg _) \<Rightarrow> 0x6c) |
  BPF_RSH \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x74 |
    (SOReg _) \<Rightarrow> 0x7c) |
  BPF_MOD \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x94 |
    (SOReg _) \<Rightarrow> 0x9c) |
  BPF_XOR \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0xa4 |
    (SOReg _) \<Rightarrow> 0xac) |
  BPF_MOV \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0xb4 |
    (SOReg _) \<Rightarrow> 0xbc) |
  BPF_ARSH \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0xc4 |
    (SOReg _) \<Rightarrow> 0xcc)
 )"

definition alu642opcode :: "binop \<Rightarrow> snd_op \<Rightarrow> u8" where
"alu642opcode bop sop = (
  case bop of 
  BPF_ADD \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x07 |
    (SOReg _) \<Rightarrow> 0x0f) |
  BPF_SUB \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x17 |
    (SOReg _) \<Rightarrow> 0x1f) |
  BPF_MUL \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x27 |
    (SOReg _) \<Rightarrow> 0x2f) |
  BPF_DIV \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x37 |
    (SOReg _) \<Rightarrow> 0x3f) |
  BPF_OR \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x47 |
    (SOReg _) \<Rightarrow> 0x4f) |
  BPF_AND \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x57 |
    (SOReg _) \<Rightarrow> 0x5f) |
  BPF_LSH \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x67 |
    (SOReg _) \<Rightarrow> 0x6f) |
  BPF_RSH \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x77 |
    (SOReg _) \<Rightarrow> 0x7f) |
  BPF_MOD \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0x97 |
    (SOReg _) \<Rightarrow> 0x9f) |
  BPF_XOR \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0xa7 |
    (SOReg _) \<Rightarrow> 0xaf) |
  BPF_MOV \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0xb7 |
    (SOReg _) \<Rightarrow> 0xbf) |
  BPF_ARSH \<Rightarrow> (
    case sop of 
    (SOImm _) \<Rightarrow> 0xc7 |
    (SOReg _) \<Rightarrow> 0xcf)
 )"


definition snd_op2i64 :: "snd_op \<Rightarrow> i64" where
"snd_op2i64 sop = (
 case sop of
 SOReg ir \<Rightarrow> bpf_ireg2i64 ir |
 SOImm im \<Rightarrow> scast im)"

definition pqr2opcode :: "pqrop \<Rightarrow> snd_op \<Rightarrow> u8" where
"pqr2opcode pop sop = (
  case pop of
  BPF_LMUL \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x86 |
    SOReg _ \<Rightarrow> 0x8e) |
  BPF_UDIV  \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x46 |
    SOReg _ \<Rightarrow> 0x4e) |
  BPF_UREM  \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x66 |
    SOReg _ \<Rightarrow> 0x6e) |
  BPF_SDIV  \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0xc6 |
    SOReg _ \<Rightarrow> 0xce) |
  BPF_SREM  \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0xe6 |
    SOReg _ \<Rightarrow> 0xee))"

definition pqr642opcode :: "pqrop \<Rightarrow> snd_op \<Rightarrow> u8" where
"pqr642opcode pop sop = (
  case pop of
  BPF_LMUL \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x96 |
    SOReg _ \<Rightarrow> 0x9e) |
  BPF_UDIV \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x56 |
    SOReg _ \<Rightarrow> 0x5e) |
  BPF_UREM \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x76 |
    SOReg _ \<Rightarrow> 0x7e) |
  BPF_SDIV \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0xd6 |
    SOReg _ \<Rightarrow> 0xde) |
  BPF_SREM \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0xf6 |
    SOReg _ \<Rightarrow> 0xfe))"

definition pqr22opcode :: "pqrop2 \<Rightarrow> snd_op \<Rightarrow> u8" where
"pqr22opcode pop sop = (
  case pop of
  BPF_UHMUL \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x36 |
    SOReg _ \<Rightarrow> 0x3e) |
  BPF_SHMUL \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0xb6 |
    SOReg _ \<Rightarrow> 0xbe))"


definition condition2opcode :: "condition \<Rightarrow> snd_op \<Rightarrow> u8" where
"condition2opcode cop sop = (
  case cop of
  Eq \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x15 |
    SOReg _ \<Rightarrow> 0x1d) |
  Gt \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x25 |
    SOReg _ \<Rightarrow> 0x2d) |
  Ge \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x35 |
    SOReg _ \<Rightarrow> 0x3d) |
  Lt \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0xa5 |
    SOReg _ \<Rightarrow> 0xad) |
  Le \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0xb5 |
    SOReg _ \<Rightarrow> 0xbd) |
  SEt \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x45 |
    SOReg _ \<Rightarrow> 0x4d) |
  Ne \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x55 |
    SOReg _ \<Rightarrow> 0x5d) |
  SGt \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x65 |
    SOReg _ \<Rightarrow> 0x6d) |
  SGe \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0x75 |
    SOReg _ \<Rightarrow> 0x7d) |
  SLt \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0xc5 |
    SOReg _ \<Rightarrow> 0xcd) |
  SLe \<Rightarrow> (
    case sop of
    SOImm _ \<Rightarrow> 0xd5 |
    SOReg _ \<Rightarrow> 0xdd))"
 
definition assemble_one_instruction :: "bpf_instruction \<Rightarrow> ebpf_binary option" where
"assemble_one_instruction ins = (
  case ins of
  BPF_LD_IMM dst i1 i2 \<Rightarrow>
    insn 0x18 (bpf_ireg2i64 dst) 0 0 (scast i1) |
  BPF_LDX ck dst src off \<Rightarrow>
    insn (ldx_chunk2opcode ck) (bpf_ireg2i64 dst) (bpf_ireg2i64 src) (scast off) 0 |
  BPF_ST ck dst src off \<Rightarrow>
    insn (st_chunk2opcode ck src) (bpf_ireg2i64 dst) (snd_op2i64 src) (scast off) 0 |
  
  BPF_NEG32_REG dst \<Rightarrow>
    insn 0x84 (bpf_ireg2i64 dst) 0 0 0 |
  BPF_NEG64_REG dst \<Rightarrow>
    insn 0x87 (bpf_ireg2i64 dst) 0 0 0 |
  
  BPF_ALU bop dst src \<Rightarrow>
    insn (alu2opcode bop src) (bpf_ireg2i64 dst) (snd_op2i64 src) 0 0 |
  BPF_LE dst imm \<Rightarrow>
    insn 0xd4 (bpf_ireg2i64 dst) 0 0 (scast imm) |
  BPF_BE dst imm \<Rightarrow>
    insn 0xdc (bpf_ireg2i64 dst) 0 0 (scast imm) |
  
  BPF_ALU64 bop dst src \<Rightarrow>
    insn (alu642opcode bop src) (bpf_ireg2i64 dst) (snd_op2i64 src) 0 0 |
  BPF_HOR64_IMM dst imm \<Rightarrow>
    insn 0xf7 (bpf_ireg2i64 dst) 0 0 (scast imm) |
  
  BPF_PQR pop dst src \<Rightarrow>
    insn (pqr2opcode pop src) (bpf_ireg2i64 dst) (snd_op2i64 src) 0 0 |
  BPF_PQR64 pop dst src \<Rightarrow>
    insn (pqr642opcode pop src) (bpf_ireg2i64 dst) (snd_op2i64 src) 0 0 |
  BPF_PQR2 pop dst src \<Rightarrow>
    insn (pqr22opcode pop src) (bpf_ireg2i64 dst) (snd_op2i64 src) 0 0 |
  
  BPF_JA off \<Rightarrow>
    insn 0x5 0 0 (scast off) 0 |
  BPF_JUMP cop dst src off \<Rightarrow>
    insn (condition2opcode cop src) (bpf_ireg2i64 dst) (snd_op2i64 src) (scast off) 0 |
  
  BPF_CALL_REG src imm \<Rightarrow>
    insn 0x8d 0 (bpf_ireg2i64 src) 0 (scast imm) |
  BPF_CALL_IMM src imm \<Rightarrow>
    insn 0x85 0 (bpf_ireg2i64 src) 0 (scast imm) |
  
  BPF_EXIT \<Rightarrow> insn 0x95 0 0 0 0)" *)

fun assemble :: "ebpf_asm \<Rightarrow> ebpf_bin option" where
"assemble [] = Some []" |
"assemble (h#t) = (
  case (assemble_one_instruction h) of
  None \<Rightarrow> None |
  Some h_i \<Rightarrow> (
    case (assemble t) of
    None \<Rightarrow> None |
    Some tl_i \<Rightarrow> (
      case h of
      BPF_LD_IMM dst i1 i2 \<Rightarrow> (
        case (insn 0 0 0 0 (scast i2)) of
        None \<Rightarrow> None |
        Some h_i2 \<Rightarrow> Some (h_i#h_i2#tl_i))|
       _ \<Rightarrow> Some (h_i#tl_i) )) )"

end