section \<open> Solana rBPF assembler formalization \<close>

theory Assembler
imports
  Main
  rBPFCommType rBPFSyntax
begin

subsection \<open> basic instruction check \<close>
definition insn :: "u8 \<Rightarrow> u4 \<Rightarrow> u4 \<Rightarrow> i16 \<Rightarrow> i32 \<Rightarrow> ebpf_binary option" where
"insn opc dst src off imm = 
  ( if 10 < dst \<or> 10 < src then None else
      Some \<lparr> bpf_opc = opc,
            bpf_dst = (ucast dst),
            bpf_src = (ucast src),
            bpf_off = (scast off),
            bpf_imm = (scast imm) \<rparr> )"

subsection \<open> get instruction opcode \<close>
fun ldx_chunk2opcode :: "chunk \<Rightarrow> u8" where
"ldx_chunk2opcode Byte = 0x71" |
"ldx_chunk2opcode HalfWord = 0x69" |
"ldx_chunk2opcode SWord = 0x61" |
"ldx_chunk2opcode DWord = 0x79"

fun st_chunk2opcode_imm :: "chunk \<Rightarrow> u8" where
"st_chunk2opcode_imm Byte = 0x72" |
"st_chunk2opcode_imm HalfWord  = 0x6a" |
"st_chunk2opcode_imm SWord = 0x62" |
"st_chunk2opcode_imm DWord  = 0x7a"

fun st_chunk2opcode_reg :: "chunk \<Rightarrow> u8" where
"st_chunk2opcode_reg Byte = 0x73" |
"st_chunk2opcode_reg HalfWord  = 0x6b" |
"st_chunk2opcode_reg SWord = 0x63" |
"st_chunk2opcode_reg DWord = 0x7b"

fun alu2opcode_imm :: "binop \<Rightarrow> u8" where
"alu2opcode_imm BPF_ADD  = 0x04" |
"alu2opcode_imm BPF_SUB  = 0x14" |
"alu2opcode_imm BPF_MUL  = 0x24" |
"alu2opcode_imm BPF_DIV  = 0x34" |
"alu2opcode_imm BPF_OR   = 0x44" |
"alu2opcode_imm BPF_AND  = 0x54" |
"alu2opcode_imm BPF_LSH  = 0x64" |
"alu2opcode_imm BPF_RSH  = 0x74" |
"alu2opcode_imm BPF_MOD  = 0x94" |
"alu2opcode_imm BPF_XOR  = 0xa4" |
"alu2opcode_imm BPF_MOV  = 0xb4" |
"alu2opcode_imm BPF_ARSH  = 0xc4"


fun alu2opcode_reg :: "binop \<Rightarrow> u8" where
"alu2opcode_reg BPF_ADD  = 0x0c" |
"alu2opcode_reg BPF_SUB  = 0x1c" |
"alu2opcode_reg BPF_MUL  = 0x2c" |
"alu2opcode_reg BPF_DIV  = 0x3c" |
"alu2opcode_reg BPF_OR   = 0x4c" |
"alu2opcode_reg BPF_AND  = 0x5c" |
"alu2opcode_reg BPF_LSH  = 0x6c" |
"alu2opcode_reg BPF_RSH  = 0x7c" |
"alu2opcode_reg BPF_MOD  = 0x9c" |
"alu2opcode_reg BPF_XOR  = 0xac" |
"alu2opcode_reg BPF_MOV  = 0xbc" |
"alu2opcode_reg BPF_ARSH = 0xcc"


fun alu642opcode_imm :: "binop \<Rightarrow> u8" where
"alu642opcode_imm BPF_ADD  = 0x07" |
"alu642opcode_imm BPF_SUB  = 0x17" |
"alu642opcode_imm BPF_MUL  = 0x27" |
"alu642opcode_imm BPF_DIV  = 0x37" |
"alu642opcode_imm BPF_OR   = 0x47" |
"alu642opcode_imm BPF_AND  = 0x57" |
"alu642opcode_imm BPF_LSH  = 0x67" |
"alu642opcode_imm BPF_RSH  = 0x77" |
"alu642opcode_imm BPF_MOD  = 0x97" |
"alu642opcode_imm BPF_XOR  = 0xa7" |
"alu642opcode_imm BPF_MOV  = 0xb7" |
"alu642opcode_imm BPF_ARSH  = 0xc7"


fun alu642opcode_reg :: "binop \<Rightarrow> u8" where
"alu642opcode_reg BPF_ADD  = 0x0f" |
"alu642opcode_reg BPF_SUB  = 0x1f" |
"alu642opcode_reg BPF_MUL  = 0x2f" |
"alu642opcode_reg BPF_DIV  = 0x3f" |
"alu642opcode_reg BPF_OR   = 0x4f" |
"alu642opcode_reg BPF_AND  = 0x5f" |
"alu642opcode_reg BPF_LSH  = 0x6f" |
"alu642opcode_reg BPF_RSH  = 0x7f" |
"alu642opcode_reg BPF_MOD  = 0x9f" |
"alu642opcode_reg BPF_XOR  = 0xaf" |
"alu642opcode_reg BPF_MOV  = 0xbf" |
"alu642opcode_reg BPF_ARSH = 0xcf"

fun pqr2opcode_imm :: "pqrop \<Rightarrow> u8" where
"pqr2opcode_imm BPF_LMUL  = 0x86" |
"pqr2opcode_imm BPF_UDIV  = 0x46" |
"pqr2opcode_imm BPF_UREM  = 0x66" |
"pqr2opcode_imm BPF_SDIV  = 0xc6" |
"pqr2opcode_imm BPF_SREM  = 0xe6"

fun pqr2opcode_reg :: "pqrop \<Rightarrow> u8" where
"pqr2opcode_reg BPF_LMUL  = 0x8e" |
"pqr2opcode_reg BPF_UDIV  = 0x4e" |
"pqr2opcode_reg BPF_UREM  = 0x6e" |
"pqr2opcode_reg BPF_SDIV  = 0xce" |
"pqr2opcode_reg BPF_SREM  = 0xee"

fun pqr642opcode_imm :: "pqrop \<Rightarrow> u8" where
"pqr642opcode_imm BPF_LMUL  = 0x96" |
"pqr642opcode_imm BPF_UDIV  = 0x56" |
"pqr642opcode_imm BPF_UREM  = 0x76" |
"pqr642opcode_imm BPF_SDIV  = 0xd6" |
"pqr642opcode_imm BPF_SREM  = 0xf6"

fun pqr642opcode_reg :: "pqrop \<Rightarrow> u8" where
"pqr642opcode_reg BPF_LMUL  = 0x9e" |
"pqr642opcode_reg BPF_UDIV  = 0x5e" |
"pqr642opcode_reg BPF_UREM  = 0x7e" |
"pqr642opcode_reg BPF_SDIV  = 0xde" |
"pqr642opcode_reg BPF_SREM  = 0xfe"

fun pqr22opcode_imm :: "pqrop2 \<Rightarrow> u8" where
"pqr22opcode_imm BPF_UHMUL  = 0x36" |
"pqr22opcode_imm BPF_SHMUL  = 0xb6"

fun pqr22opcode_reg :: "pqrop2 \<Rightarrow> u8" where
"pqr22opcode_reg BPF_UHMUL  = 0x3e" |
"pqr22opcode_reg BPF_SHMUL  = 0xbe"


fun condition2opcode_imm :: "condition \<Rightarrow> u8" where
"condition2opcode_imm Eq   = 0x15" |
"condition2opcode_imm Gt   = 0x25" |
"condition2opcode_imm Ge   = 0x35" |
"condition2opcode_imm Lt   = 0xa5" |
"condition2opcode_imm Le   = 0xb5" |
"condition2opcode_imm SEt  = 0x45" |
"condition2opcode_imm Ne   = 0x55" |
"condition2opcode_imm SGt  = 0x65" |
"condition2opcode_imm SGe  = 0x75" |
"condition2opcode_imm SLt  = 0xc5" |
"condition2opcode_imm SLe  = 0xd5"

fun condition2opcode_reg :: "condition \<Rightarrow> u8" where
"condition2opcode_reg Eq   = 0x1d" |
"condition2opcode_reg Gt   = 0x2d" |
"condition2opcode_reg Ge   = 0x3d" |
"condition2opcode_reg Lt   = 0xad" |
"condition2opcode_reg Le   = 0xbd" |
"condition2opcode_reg SEt  = 0x4d" |
"condition2opcode_reg Ne   = 0x5d" |
"condition2opcode_reg SGt  = 0x6d" |
"condition2opcode_reg SGe  = 0x7d" |
"condition2opcode_reg SLt  = 0xcd" |
"condition2opcode_reg SLe  = 0xdd"

subsection \<open> assemble one instruction \<close>


text \<open> LD_IMM only encode the first 32-bit immediate number, the second one is encoded later  \<close>
fun assemble_one_instruction :: "bpf_instruction \<Rightarrow> ebpf_binary option" where
"assemble_one_instruction (BPF_LD_IMM dst i1 i2) =
  insn 0x18 (bpf_ireg2u4 dst) 0 0 i1" |
"assemble_one_instruction (BPF_LDX ck dst src off) =
  insn (ldx_chunk2opcode ck) (bpf_ireg2u4 dst) (bpf_ireg2u4 src) off 0" |
"assemble_one_instruction (BPF_ST ck dst (SOReg ir) off) =
  insn (st_chunk2opcode_reg ck) (bpf_ireg2u4 dst) (bpf_ireg2u4 ir) off 0" |
"assemble_one_instruction (BPF_ST ck dst (SOImm im) off) =
  insn (st_chunk2opcode_imm ck) (bpf_ireg2u4 dst) 0 off im" |
  
"assemble_one_instruction (BPF_NEG32_REG dst) =
  insn 0x84 (bpf_ireg2u4 dst) 0 0 0" |
"assemble_one_instruction (BPF_NEG64_REG dst) =
  insn 0x87 (bpf_ireg2u4 dst) 0 0 0" |
  
"assemble_one_instruction (BPF_ALU bop dst (SOReg ir)) =
  insn (alu2opcode_reg bop) (bpf_ireg2u4 dst) (bpf_ireg2u4 ir) 0 0" |
"assemble_one_instruction (BPF_ALU bop dst (SOImm im)) =
  insn (alu2opcode_imm bop) (bpf_ireg2u4 dst) 0 0 im" |
"assemble_one_instruction (BPF_LE dst imm) =
  insn 0xd4 (bpf_ireg2u4 dst) 0 0 imm" |
"assemble_one_instruction (BPF_BE dst imm) =
  insn 0xdc (bpf_ireg2u4 dst) 0 0 imm" |
  
"assemble_one_instruction (BPF_ALU64 bop dst (SOReg ir)) =
  insn (alu642opcode_reg bop) (bpf_ireg2u4 dst) (bpf_ireg2u4 ir) 0 0" |
"assemble_one_instruction (BPF_ALU64 bop dst (SOImm im)) =
  insn (alu642opcode_imm bop) (bpf_ireg2u4 dst) 0 0 im" |
"assemble_one_instruction (BPF_HOR64_IMM dst imm) =
  insn 0xf7 (bpf_ireg2u4 dst) 0 0 imm" |
  
"assemble_one_instruction (BPF_PQR pop dst (SOReg ir)) =
  insn (pqr2opcode_reg pop) (bpf_ireg2u4 dst) (bpf_ireg2u4 ir) 0 0" |
"assemble_one_instruction (BPF_PQR pop dst (SOImm im)) =
  insn (pqr2opcode_imm pop) (bpf_ireg2u4 dst) 0 0 im" |
"assemble_one_instruction (BPF_PQR64 pop dst (SOReg ir)) =
  insn (pqr642opcode_reg pop) (bpf_ireg2u4 dst) (bpf_ireg2u4 ir) 0 0" |
"assemble_one_instruction (BPF_PQR64 pop dst (SOImm im)) =
  insn (pqr642opcode_imm pop) (bpf_ireg2u4 dst) 0 0 im" |
"assemble_one_instruction (BPF_PQR2 pop dst (SOReg ir)) =
  insn (pqr22opcode_reg pop) (bpf_ireg2u4 dst) (bpf_ireg2u4 ir) 0 0" |
"assemble_one_instruction (BPF_PQR2 pop dst (SOImm im)) =
  insn (pqr22opcode_imm pop) (bpf_ireg2u4 dst) 0 0 im" |
  
"assemble_one_instruction (BPF_JA off) =
  insn 0x5 0 0 off 0" |
"assemble_one_instruction (BPF_JUMP cop dst (SOReg ir) off) =
  insn (condition2opcode_reg cop) (bpf_ireg2u4 dst) (bpf_ireg2u4 ir) off 0" |
"assemble_one_instruction (BPF_JUMP cop dst (SOImm im) off) =
  insn (condition2opcode_imm cop) (bpf_ireg2u4 dst) 0 off im" |
  
"assemble_one_instruction (BPF_CALL_REG src imm) =
  insn 0x8d 0 (bpf_ireg2u4 src) 0 imm" |
"assemble_one_instruction (BPF_CALL_IMM src imm) =
  insn 0x85 0 (bpf_ireg2u4 src) 0 imm" |
  
"assemble_one_instruction BPF_EXIT = insn 0x95 0 0 0 0"

subsection \<open> assemble a set of instructions \<close>

text \<open>after each time assemble one instruction, we check if the current
instruction is LD_IMM dst imm1 imm2, if so, we additionally encode 0 0 0 0 imm2\<close>
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
        case (insn 0 0 0 0 i2) of
        None \<Rightarrow> None |
        Some h_i2 \<Rightarrow> Some (h_i#h_i2#tl_i))|
       _ \<Rightarrow> Some (h_i#tl_i) )) )"

end