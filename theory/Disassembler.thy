theory Disassembler
imports
  Main (*
  "HOL.Bit_Operations" "HOL-Library.Word" *)
  rBPFCommType rBPFSyntax
begin

definition disassemble_lddw :: "u4 => i32 \<Rightarrow> ebpf_binary \<Rightarrow> bpf_instruction option" where
"disassemble_lddw dst imm imm_h =
  ( if (bpf_opc imm_h = 0 \<and> bpf_dst imm_h = 0 \<and> bpf_src imm_h = 0 \<and> bpf_off imm_h = 0 )
    then
      case u4_to_bpf_ireg dst of
      None \<Rightarrow> None |
      Some d \<Rightarrow> Some (BPF_LD_IMM d imm (bpf_imm imm_h))
    else None)"

    (**  \<and>
        (\<not> (imm <s (-2147483648) \<or> 2147483647 <s imm)) \<and>
        (\<not> ((bpf_imm imm_h) <s (-2147483648) \<or> 2147483647 <s (bpf_imm imm_h)))  *)

definition disassemble_one_instruction :: "ebpf_binary \<Rightarrow> bpf_instruction option" where
"disassemble_one_instruction bi = (
  case u4_to_bpf_ireg (bpf_dst bi) of
  None \<Rightarrow> None |
  Some dst \<Rightarrow> (
    case u4_to_bpf_ireg (bpf_src bi) of
    None \<Rightarrow> None |
    Some src \<Rightarrow> (
      if bpf_opc bi = 0x71 then
        Some (BPF_LDX Byte      dst src         (bpf_off bi))
      else if bpf_opc bi = 0x69 then
        Some (BPF_LDX HalfWord  dst src         (bpf_off bi))
      else if bpf_opc bi = 0x61 then
        Some (BPF_LDX SWord     dst src         (bpf_off bi))
      else if bpf_opc bi = 0x79 then
        Some (BPF_LDX DWord     dst src         (bpf_off bi))

      else if bpf_opc bi = 0x72 then
        Some (BPF_ST  Byte      dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0x6a then
        Some (BPF_ST  HalfWord  dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0x62 then
        Some (BPF_ST  SWord     dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0x7a then
        Some (BPF_ST  DWord     dst (SOImm (bpf_imm bi)) (bpf_off bi))

      else if bpf_opc bi = 0x73 then
        Some (BPF_ST  Byte      dst (SOReg src) (bpf_off bi))
      else if bpf_opc bi = 0x6b then
        Some (BPF_ST  HalfWord  dst (SOReg src) (bpf_off bi))
      else if bpf_opc bi = 0x63 then
        Some (BPF_ST  SWord     dst (SOReg src) (bpf_off bi))
      else if bpf_opc bi = 0x7b then
        Some (BPF_ST  DWord     dst (SOReg src) (bpf_off bi))

      else if bpf_opc bi = 0x04 then
        Some (BPF_ALU BPF_ADD   dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x0c then
        Some (BPF_ALU BPF_ADD   dst (SOReg src))
      else if bpf_opc bi = 0x14 then
        Some (BPF_ALU BPF_SUB   dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x1c then
        Some (BPF_ALU BPF_SUB   dst (SOReg src))
      else if bpf_opc bi = 0x24 then
        Some (BPF_ALU BPF_MUL   dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x2c then
        Some (BPF_ALU BPF_MUL   dst (SOReg src))
      else if bpf_opc bi = 0x34 then
        Some (BPF_ALU BPF_DIV   dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x3c then
        Some (BPF_ALU BPF_DIV   dst (SOReg src))
      else if bpf_opc bi = 0x44 then
        Some (BPF_ALU BPF_OR    dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x4c then
        Some (BPF_ALU BPF_OR    dst (SOReg src))
      else if bpf_opc bi = 0x54 then
        Some (BPF_ALU BPF_AND   dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x5c then
        Some (BPF_ALU BPF_AND   dst (SOReg src))
      else if bpf_opc bi = 0x64 then
        Some (BPF_ALU BPF_LSH   dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x6c then
        Some (BPF_ALU BPF_LSH   dst (SOReg src))
      else if bpf_opc bi = 0x74 then
        Some (BPF_ALU BPF_RSH   dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x7c then
        Some (BPF_ALU BPF_RSH   dst (SOReg src))

      else if bpf_opc bi = 0x84 then
        Some (BPF_NEG32_REG     dst)

      else if bpf_opc bi = 0x94 then
        Some (BPF_ALU BPF_MOD   dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x9c then
        Some (BPF_ALU BPF_MOD   dst (SOReg src))
      else if bpf_opc bi = 0xa4 then
        Some (BPF_ALU BPF_XOR   dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0xac then
        Some (BPF_ALU BPF_XOR   dst (SOReg src))
      else if bpf_opc bi = 0xb4 then
        Some (BPF_ALU BPF_MOV   dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0xbc then
        Some (BPF_ALU BPF_MOV   dst (SOReg src))
      else if bpf_opc bi = 0xc4 then
        Some (BPF_ALU BPF_ARSH  dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0xcc then
        Some (BPF_ALU BPF_ARSH  dst (SOReg src))

      else if bpf_opc bi = 0xd4 then
        Some (BPF_LE            dst (bpf_imm bi))
      else if bpf_opc bi = 0xdc then
        Some (BPF_BE            dst (bpf_imm bi))

      else if bpf_opc bi = 0x07 then
        Some (BPF_ALU64 BPF_ADD dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x0f then
        Some (BPF_ALU64 BPF_ADD dst (SOReg src))
      else if bpf_opc bi = 0x17 then
        Some (BPF_ALU64 BPF_SUB dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x1f then
        Some (BPF_ALU64 BPF_SUB dst (SOReg src))
      else if bpf_opc bi = 0x27 then
        Some (BPF_ALU64 BPF_MUL dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x2f then
        Some (BPF_ALU64 BPF_MUL dst (SOReg src))
      else if bpf_opc bi = 0x37 then
        Some (BPF_ALU64 BPF_DIV dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x3f then
        Some (BPF_ALU64 BPF_DIV dst (SOReg src))
      else if bpf_opc bi = 0x47 then
        Some (BPF_ALU64 BPF_OR  dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x4f then
        Some (BPF_ALU64 BPF_OR  dst (SOReg src))
      else if bpf_opc bi = 0x57 then
        Some (BPF_ALU64 BPF_AND dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x5f then
        Some (BPF_ALU64 BPF_AND dst (SOReg src))
      else if bpf_opc bi = 0x67 then
        Some (BPF_ALU64 BPF_LSH dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x6f then
        Some (BPF_ALU64 BPF_LSH dst (SOReg src))
      else if bpf_opc bi = 0x77 then
        Some (BPF_ALU64 BPF_RSH dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x7f then
        Some (BPF_ALU64 BPF_RSH dst (SOReg src))

      else if bpf_opc bi = 0x87 then
        Some (BPF_NEG64_REG     dst)

      else if bpf_opc bi = 0x97 then
        Some (BPF_ALU64 BPF_MOD dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x9f then
        Some (BPF_ALU64 BPF_MOD dst (SOReg src))
      else if bpf_opc bi = 0xa7 then
        Some (BPF_ALU64 BPF_XOR dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0xaf then
        Some (BPF_ALU64 BPF_XOR dst (SOReg src))
      else if bpf_opc bi = 0xb7 then
        Some (BPF_ALU64 BPF_MOV dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0xbf then
        Some (BPF_ALU64 BPF_MOV dst (SOReg src))
      else if bpf_opc bi = 0xc7 then
        Some (BPF_ALU64 BPF_ARSH  dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0xcf then
        Some (BPF_ALU64 BPF_ARSH  dst (SOReg src))

      else if bpf_opc bi = 0xf7 then
        Some (BPF_HOR64_IMM     dst (bpf_imm bi))

      else if bpf_opc bi = 0x86 then
        Some (BPF_PQR BPF_LMUL    dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x8e then
        Some (BPF_PQR BPF_LMUL    dst (SOReg src))
      else if bpf_opc bi = 0x96 then
        Some (BPF_PQR64 BPF_LMUL  dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x9e then
        Some (BPF_PQR64 BPF_LMUL  dst (SOReg src))

      else if bpf_opc bi = 0x36 then
        Some (BPF_PQR2 BPF_UHMUL  dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x3e then
        Some (BPF_PQR2 BPF_UHMUL  dst (SOReg src))
      else if bpf_opc bi = 0xb6 then
        Some (BPF_PQR2 BPF_SHMUL  dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0xbe then
        Some (BPF_PQR2 BPF_SHMUL  dst (SOReg src))

      else if bpf_opc bi = 0x46 then
        Some (BPF_PQR BPF_UDIV    dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x4e then
        Some (BPF_PQR BPF_UDIV    dst (SOReg src))
      else if bpf_opc bi = 0x56 then
        Some (BPF_PQR64 BPF_UDIV  dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x5e then
        Some (BPF_PQR64 BPF_UDIV  dst (SOReg src))

      else if bpf_opc bi = 0x66 then
        Some (BPF_PQR BPF_UREM    dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x6e then
        Some (BPF_PQR BPF_UREM    dst (SOReg src))
      else if bpf_opc bi = 0x76 then
        Some (BPF_PQR64 BPF_UREM  dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0x7e then
        Some (BPF_PQR64 BPF_UREM  dst (SOReg src))

      else if bpf_opc bi = 0xc6 then
        Some (BPF_PQR BPF_SDIV    dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0xce then
        Some (BPF_PQR BPF_SDIV    dst (SOReg src))
      else if bpf_opc bi = 0xd6 then
        Some (BPF_PQR64 BPF_SDIV  dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0xde then
        Some (BPF_PQR64 BPF_SDIV  dst (SOReg src))

      else if bpf_opc bi = 0xe6 then
        Some (BPF_PQR BPF_SREM    dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0xee then
        Some (BPF_PQR BPF_SREM    dst (SOReg src))
      else if bpf_opc bi = 0xf6 then
        Some (BPF_PQR64 BPF_SREM  dst (SOImm (bpf_imm bi)))
      else if bpf_opc bi = 0xfe then
        Some (BPF_PQR64 BPF_SREM  dst (SOReg src))

      else if bpf_opc bi = 0x05 then
        Some (BPF_JA (bpf_off bi))

      else if bpf_opc bi = 0x15 then
        Some (BPF_JUMP Eq  dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0x1d then
        Some (BPF_JUMP Eq  dst (SOReg src)          (bpf_off bi))
      else if bpf_opc bi = 0x25 then
        Some (BPF_JUMP Gt  dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0x2d then
        Some (BPF_JUMP Gt  dst (SOReg src)          (bpf_off bi))
      else if bpf_opc bi = 0x35 then
        Some (BPF_JUMP Ge  dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0x3d then
        Some (BPF_JUMP Ge  dst (SOReg src)          (bpf_off bi))
      else if bpf_opc bi = 0xa5 then
        Some (BPF_JUMP Lt  dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0xad then
        Some (BPF_JUMP Lt  dst (SOReg src)          (bpf_off bi))
      else if bpf_opc bi = 0xb5 then
        Some (BPF_JUMP Le  dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0xbd then
        Some (BPF_JUMP Le  dst (SOReg src)          (bpf_off bi))
      else if bpf_opc bi = 0x45 then
        Some (BPF_JUMP SEt dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0x4d then
        Some (BPF_JUMP SEt dst (SOReg src)          (bpf_off bi))
      else if bpf_opc bi = 0x55 then
        Some (BPF_JUMP Ne  dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0x5d then
        Some (BPF_JUMP Ne  dst (SOReg src)          (bpf_off bi))
      else if bpf_opc bi = 0x65 then
        Some (BPF_JUMP SGt dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0x6d then
        Some (BPF_JUMP SGt dst (SOReg src)          (bpf_off bi))
      else if bpf_opc bi = 0x75 then
        Some (BPF_JUMP SGe  dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0x7d then
        Some (BPF_JUMP SGe  dst (SOReg src)          (bpf_off bi))
      else if bpf_opc bi = 0xc5 then
        Some (BPF_JUMP SLt dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0xcd then
        Some (BPF_JUMP SLt dst (SOReg src)          (bpf_off bi))
      else if bpf_opc bi = 0xd5 then
        Some (BPF_JUMP SLe dst (SOImm (bpf_imm bi)) (bpf_off bi))
      else if bpf_opc bi = 0xdd then
        Some (BPF_JUMP SLe dst (SOReg src)          (bpf_off bi))

      else if bpf_opc bi = 0x8d then
        Some (BPF_CALL_REG src (bpf_imm bi))
      else if bpf_opc bi = 0x85 then
        Some (BPF_CALL_IMM src (bpf_imm bi))

      else if bpf_opc bi = 0x95 then
        Some BPF_EXIT
      else  None)))"
    
fun disassemble :: "ebpf_bin \<Rightarrow> ebpf_asm option" where
"disassemble [] = Some []" |
"disassemble (h#t) = (
  if bpf_opc h = 0x18 then
    case t of
    [] \<Rightarrow> None |
    (h1#t1) \<Rightarrow> (
      case disassemble_lddw (bpf_dst h) (bpf_imm h) h1 of
      None \<Rightarrow> None |
      Some ins \<Rightarrow> (
        case disassemble t1 of
        None \<Rightarrow> None |
        Some t2 \<Rightarrow> Some (ins#t2)))
  else
    case disassemble_one_instruction h of
    None \<Rightarrow> None |
    Some ins \<Rightarrow> (
      case disassemble t of
      None \<Rightarrow> None |
      Some t2 \<Rightarrow> Some (ins#t2)) )"

end