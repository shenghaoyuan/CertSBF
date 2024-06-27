theory Disassembler
imports
  Main
  rBPFCommType rBPFSyntax
begin

definition disassemble_lddw :: "ebpf_binary \<Rightarrow> ebpf_binary \<Rightarrow> bpf_instruction option" where
"disassemble_lddw i1 i2 =
  ( if (bpf_src i1 = 0 \<and> bpf_off i1 = 0 \<and> bpf_opc i2 = 0 \<and>
        bpf_dst i2 = 0 \<and> bpf_src i2 = 0 \<and> bpf_off i2 = 0)
    then
      case u4_to_bpf_ireg (bpf_dst i1) of
      None \<Rightarrow> None |
      Some d \<Rightarrow> Some (BPF_LD_IMM d (bpf_imm i1) (bpf_imm i2))
    else None)"

    (**  \<and>
        (\<not> (imm <s (-2147483648) \<or> 2147483647 <s imm)) \<and>
        (\<not> ((bpf_imm imm_h) <s (-2147483648) \<or> 2147483647 <s (bpf_imm imm_h)))  *)

definition disassemble_one_instruction :: "ebpf_binary \<Rightarrow> bpf_instruction option" where
"disassemble_one_instruction bi = (
  if 10 < (bpf_dst bi) \<or> 10 < (bpf_src bi) then None
  else

  case u4_to_bpf_ireg (bpf_dst bi) of
  None \<Rightarrow> None |
  Some dst \<Rightarrow> (
    case u4_to_bpf_ireg (bpf_src bi) of
    None \<Rightarrow> None |
    Some src \<Rightarrow> (
      if bpf_opc bi = 0x71 then
        if bpf_imm bi = 0 then
          Some (BPF_LDX Byte      dst src         (bpf_off bi))
        else None
      else if bpf_opc bi = 0x69 then
        if bpf_imm bi = 0 then
          Some (BPF_LDX HalfWord  dst src         (bpf_off bi))
        else None
      else if bpf_opc bi = 0x61 then
        if bpf_imm bi = 0 then
          Some (BPF_LDX SWord     dst src         (bpf_off bi))
        else None
      else if bpf_opc bi = 0x79 then
        if bpf_imm bi = 0 then
          Some (BPF_LDX DWord     dst src         (bpf_off bi))
        else None

      else if bpf_opc bi = 0x72 then
        if bpf_src bi = 0 then
        Some (BPF_ST  Byte      dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0x6a then
        if bpf_src bi = 0 then
        Some (BPF_ST  HalfWord  dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0x62 then
        if bpf_src bi = 0 then
        Some (BPF_ST  SWord     dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0x7a then
        if bpf_src bi = 0 then
        Some (BPF_ST  DWord     dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None

      else if bpf_opc bi = 0x73 then
        if bpf_imm bi = 0 then
          Some (BPF_ST  Byte      dst (SOReg src) (bpf_off bi))
        else None
      else if bpf_opc bi = 0x6b then
        if bpf_imm bi = 0 then
          Some (BPF_ST  HalfWord  dst (SOReg src) (bpf_off bi))
        else None
      else if bpf_opc bi = 0x63 then
        if bpf_imm bi = 0 then
          Some (BPF_ST  SWord     dst (SOReg src) (bpf_off bi))
        else None
      else if bpf_opc bi = 0x7b then
        if bpf_imm bi = 0 then
          Some (BPF_ST  DWord     dst (SOReg src) (bpf_off bi))
        else None

      else if bpf_opc bi = 0x04 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU BPF_ADD   dst (SOImm (bpf_imm bi)))
        else None                                          
      else if bpf_opc bi = 0x0c then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU BPF_ADD   dst (SOReg src))
        else None                                          
      else if bpf_opc bi = 0x14 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU BPF_SUB   dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x1c then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU BPF_SUB   dst (SOReg src))
        else None
      else if bpf_opc bi = 0x24 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU BPF_MUL   dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x2c then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU BPF_MUL   dst (SOReg src))
        else None
      else if bpf_opc bi = 0x34 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU BPF_DIV   dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x3c then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU BPF_DIV   dst (SOReg src))
        else None
      else if bpf_opc bi = 0x44 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU BPF_OR    dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x4c then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU BPF_OR    dst (SOReg src))
        else None
      else if bpf_opc bi = 0x54 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU BPF_AND   dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x5c then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU BPF_AND   dst (SOReg src))
        else None
      else if bpf_opc bi = 0x64 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU BPF_LSH   dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x6c then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU BPF_LSH   dst (SOReg src))
        else None
      else if bpf_opc bi = 0x74 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU BPF_RSH   dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x7c then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU BPF_RSH   dst (SOReg src))
        else None

      else if bpf_opc bi = 0x84 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_NEG32_REG     dst)
        else None

      else if bpf_opc bi = 0x94 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU BPF_MOD   dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x9c then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU BPF_MOD   dst (SOReg src))
        else None
      else if bpf_opc bi = 0xa4 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU BPF_XOR   dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0xac then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU BPF_XOR   dst (SOReg src))
        else None
      else if bpf_opc bi = 0xb4 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU BPF_MOV   dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0xbc then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU BPF_MOV   dst (SOReg src))
        else None
      else if bpf_opc bi = 0xc4 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU BPF_ARSH  dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0xcc then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU BPF_ARSH  dst (SOReg src))
        else None

      else if bpf_opc bi = 0xd4 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_LE            dst (bpf_imm bi))
        else None
      else if bpf_opc bi = 0xdc then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_BE            dst (bpf_imm bi))
        else None

      else if bpf_opc bi = 0x07 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU64 BPF_ADD dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x0f then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU64 BPF_ADD dst (SOReg src))
        else None
      else if bpf_opc bi = 0x17 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU64 BPF_SUB dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x1f then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU64 BPF_SUB dst (SOReg src))
        else None
      else if bpf_opc bi = 0x27 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU64 BPF_MUL dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x2f then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU64 BPF_MUL dst (SOReg src))
        else None
      else if bpf_opc bi = 0x37 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU64 BPF_DIV dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x3f then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU64 BPF_DIV dst (SOReg src))
        else None
      else if bpf_opc bi = 0x47 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU64 BPF_OR  dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x4f then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU64 BPF_OR  dst (SOReg src))
        else None
      else if bpf_opc bi = 0x57 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU64 BPF_AND dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x5f then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU64 BPF_AND dst (SOReg src))
        else None
      else if bpf_opc bi = 0x67 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU64 BPF_LSH dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x6f then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU64 BPF_LSH dst (SOReg src))
        else None
      else if bpf_opc bi = 0x77 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU64 BPF_RSH dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x7f then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU64 BPF_RSH dst (SOReg src))
        else None

      else if bpf_opc bi = 0x87 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_NEG64_REG     dst)
        else None

      else if bpf_opc bi = 0x97 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU64 BPF_MOD dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x9f then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU64 BPF_MOD dst (SOReg src))
        else None
      else if bpf_opc bi = 0xa7 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU64 BPF_XOR dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0xaf then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU64 BPF_XOR dst (SOReg src))
        else None
      else if bpf_opc bi = 0xb7 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU64 BPF_MOV dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0xbf then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU64 BPF_MOV dst (SOReg src))
        else None
      else if bpf_opc bi = 0xc7 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU64 BPF_ARSH  dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0xcf then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_ALU64 BPF_ARSH  dst (SOReg src))
        else None

      else if bpf_opc bi = 0xf7 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_HOR64_IMM     dst (bpf_imm bi))
        else None

      else if bpf_opc bi = 0x86 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_PQR BPF_LMUL    dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x8e then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_PQR BPF_LMUL    dst (SOReg src))
        else None
      else if bpf_opc bi = 0x96 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_PQR64 BPF_LMUL  dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x9e then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_PQR64 BPF_LMUL  dst (SOReg src))
        else None

      else if bpf_opc bi = 0x36 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_PQR2 BPF_UHMUL  dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x3e then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_PQR2 BPF_UHMUL  dst (SOReg src))
        else None
      else if bpf_opc bi = 0xb6 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_PQR2 BPF_SHMUL  dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0xbe then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_PQR2 BPF_SHMUL  dst (SOReg src))
        else None

      else if bpf_opc bi = 0x46 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_PQR BPF_UDIV    dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x4e then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_PQR BPF_UDIV    dst (SOReg src))
        else None
      else if bpf_opc bi = 0x56 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_PQR64 BPF_UDIV  dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x5e then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_PQR64 BPF_UDIV  dst (SOReg src))
        else None

      else if bpf_opc bi = 0x66 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_PQR BPF_UREM    dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x6e then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_PQR BPF_UREM    dst (SOReg src))
        else None
      else if bpf_opc bi = 0x76 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_PQR64 BPF_UREM  dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0x7e then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_PQR64 BPF_UREM  dst (SOReg src))
        else None

      else if bpf_opc bi = 0xc6 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_PQR BPF_SDIV    dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0xce then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_PQR BPF_SDIV    dst (SOReg src))
        else None
      else if bpf_opc bi = 0xd6 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_PQR64 BPF_SDIV  dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0xde then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_PQR64 BPF_SDIV  dst (SOReg src))
        else None

      else if bpf_opc bi = 0xe6 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_PQR BPF_SREM    dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0xee then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_PQR BPF_SREM    dst (SOReg src))
        else None
      else if bpf_opc bi = 0xf6 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_PQR64 BPF_SREM  dst (SOImm (bpf_imm bi)))
        else None
      else if bpf_opc bi = 0xfe then
        if bpf_off bi = 0 \<and> bpf_imm bi = 0 then
          Some (BPF_PQR64 BPF_SREM  dst (SOReg src))
        else None

      else if bpf_opc bi = 0x05 then
        if bpf_imm bi = 0 \<and> bpf_dst bi = 0 \<and> bpf_src bi = 0 then
        Some (BPF_JA (bpf_off bi))
        else None

      else if bpf_opc bi = 0x15 then
        if bpf_src bi = 0 then
        Some (BPF_JUMP Eq  dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0x1d then
        if bpf_imm bi = 0 then
        Some (BPF_JUMP Eq  dst (SOReg src)          (bpf_off bi))
        else None
      else if bpf_opc bi = 0x25 then
        if bpf_src bi = 0 then
        Some (BPF_JUMP Gt  dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0x2d then
        if bpf_imm bi = 0 then
        Some (BPF_JUMP Gt  dst (SOReg src)          (bpf_off bi))
        else None
      else if bpf_opc bi = 0x35 then
        if bpf_src bi = 0 then
        Some (BPF_JUMP Ge  dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0x3d then
        if bpf_imm bi = 0 then
        Some (BPF_JUMP Ge  dst (SOReg src)          (bpf_off bi))
        else None
      else if bpf_opc bi = 0xa5 then
        if bpf_src bi = 0 then
        Some (BPF_JUMP Lt  dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0xad then
        if bpf_imm bi = 0 then
        Some (BPF_JUMP Lt  dst (SOReg src)          (bpf_off bi))
        else None
      else if bpf_opc bi = 0xb5 then
        if bpf_src bi = 0 then
        Some (BPF_JUMP Le  dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0xbd then
        if bpf_imm bi = 0 then
        Some (BPF_JUMP Le  dst (SOReg src)          (bpf_off bi))
        else None
      else if bpf_opc bi = 0x45 then
        if bpf_src bi = 0 then
        Some (BPF_JUMP SEt dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0x4d then
        if bpf_imm bi = 0 then
        Some (BPF_JUMP SEt dst (SOReg src)          (bpf_off bi))
        else None
      else if bpf_opc bi = 0x55 then
        if bpf_src bi = 0 then
        Some (BPF_JUMP Ne  dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0x5d then
        if bpf_imm bi = 0 then
        Some (BPF_JUMP Ne  dst (SOReg src)          (bpf_off bi))
        else None
      else if bpf_opc bi = 0x65 then
        if bpf_src bi = 0 then
        Some (BPF_JUMP SGt dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0x6d then
        if bpf_imm bi = 0 then
        Some (BPF_JUMP SGt dst (SOReg src)          (bpf_off bi))
        else None
      else if bpf_opc bi = 0x75 then
        if bpf_src bi = 0 then
        Some (BPF_JUMP SGe  dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0x7d then
        if bpf_imm bi = 0 then
        Some (BPF_JUMP SGe  dst (SOReg src)          (bpf_off bi))
        else None
      else if bpf_opc bi = 0xc5 then
        if bpf_src bi = 0 then
        Some (BPF_JUMP SLt dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0xcd then
        if bpf_imm bi = 0 then
        Some (BPF_JUMP SLt dst (SOReg src)          (bpf_off bi))
        else None
      else if bpf_opc bi = 0xd5 then
        if bpf_src bi = 0 then
        Some (BPF_JUMP SLe dst (SOImm (bpf_imm bi)) (bpf_off bi))
        else None
      else if bpf_opc bi = 0xdd then
        if bpf_imm bi = 0 then
        Some (BPF_JUMP SLe dst (SOReg src)          (bpf_off bi))
        else None

      else if bpf_opc bi = 0x8d then
        if bpf_off bi = 0 \<and> bpf_dst bi = 0 then
          Some (BPF_CALL_REG src (bpf_imm bi))
        else None
      else if bpf_opc bi = 0x85 then
        if bpf_off bi = 0 \<and> bpf_dst bi = 0 then
          Some (BPF_CALL_IMM src (bpf_imm bi))
        else None

      else if bpf_opc bi = 0x95 then (
        if (bpf_dst bi = 0 \<and> bpf_src bi = 0 \<and> bpf_off bi = 0 \<and> bpf_imm bi = 0) then
          Some BPF_EXIT
        else
          None)
      else  None)))"
    
fun disassemble :: "ebpf_bin \<Rightarrow> ebpf_asm option" where
"disassemble [] = Some []" |
"disassemble (h#t) = (
  if bpf_opc h = 0x18 then
    case t of
    [] \<Rightarrow> None |
    (h1#t1) \<Rightarrow> (
      case disassemble_lddw h h1 of
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