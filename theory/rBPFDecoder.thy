theory rBPFDecoder
imports
  Main
  rBPFCommType rBPFSyntax ebpf
begin
                                                                    
definition rbpf_decoder :: "u8 \<Rightarrow> u4 \<Rightarrow> u4 \<Rightarrow> i16 \<Rightarrow> i32 \<Rightarrow> bpf_instruction option" where
"rbpf_decoder opc dv sv off imm  = (
  if opc = 0x07 then
    if dv = 11 then
      Some (BPF_ADD_STK imm)
    else (
      case u4_to_bpf_ireg dv of
      None \<Rightarrow> None |
      Some dst \<Rightarrow>
        Some (BPF_ALU64 BPF_ADD dst (SOImm imm)) )
  else (
    case u4_to_bpf_ireg dv of
    None \<Rightarrow> None |
    Some dst \<Rightarrow> (
      case u4_to_bpf_ireg sv of
      None \<Rightarrow> None |
      Some src \<Rightarrow>
        if opc = 0x71 then
          Some (BPF_LDX M8  dst src         off)
        else if opc = 0x69 then
          Some (BPF_LDX M16 dst src         off)
        else if opc = 0x61 then
          Some (BPF_LDX M32 dst src         off)
        else if opc = 0x79 then
          Some (BPF_LDX M64 dst src         off)
  
        else if opc = 0x72 then
          Some (BPF_ST  M8  dst (SOImm imm) off)
        else if opc = 0x6a then
          Some (BPF_ST  M16 dst (SOImm imm) off)
        else if opc = 0x62 then
          Some (BPF_ST  M32 dst (SOImm imm) off)
        else if opc = 0x7a then
          Some (BPF_ST  M64 dst (SOImm imm) off)
  
        else if opc = 0x73 then
          Some (BPF_ST  M8  dst (SOReg src) off)
        else if opc = 0x6b then
          Some (BPF_ST  M16 dst (SOReg src) off)
        else if opc = 0x63 then
          Some (BPF_ST  M32 dst (SOReg src) off)
        else if opc = 0x7b then
          Some (BPF_ST  M64 dst (SOReg src) off)
  
        else if opc = 0x04 then
          Some (BPF_ALU BPF_ADD   dst (SOImm imm))
        else if opc = 0x0c then
          Some (BPF_ALU BPF_ADD   dst (SOReg src))
        else if opc = 0x14 then
          Some (BPF_ALU BPF_SUB   dst (SOImm imm))
        else if opc = 0x1c then
          Some (BPF_ALU BPF_SUB   dst (SOReg src))
        else if opc = 0x24 then
          Some (BPF_ALU BPF_MUL   dst (SOImm imm))
        else if opc = 0x2c then
          Some (BPF_ALU BPF_MUL   dst (SOReg src))
        else if opc = 0x34 then
          Some (BPF_ALU BPF_DIV   dst (SOImm imm))
        else if opc = 0x3c then
          Some (BPF_ALU BPF_DIV   dst (SOReg src))
        else if opc = 0x44 then
          Some (BPF_ALU BPF_OR    dst (SOImm imm))
        else if opc = 0x4c then
          Some (BPF_ALU BPF_OR    dst (SOReg src))
        else if opc = 0x54 then
          Some (BPF_ALU BPF_AND   dst (SOImm imm))
        else if opc = 0x5c then
          Some (BPF_ALU BPF_AND   dst (SOReg src))
        else if opc = 0x64 then
          Some (BPF_ALU BPF_LSH   dst (SOImm imm))
        else if opc = 0x6c then
          Some (BPF_ALU BPF_LSH   dst (SOReg src))
        else if opc = 0x74 then
          Some (BPF_ALU BPF_RSH   dst (SOImm imm))
        else if opc = 0x7c then
          Some (BPF_ALU BPF_RSH   dst (SOReg src))

        else if opc = 0x84 then
          Some (BPF_NEG32_REG     dst)

        else if opc = 0x94 then
          Some (BPF_ALU BPF_MOD   dst (SOImm imm))
        else if opc = 0x9c then
          Some (BPF_ALU BPF_MOD   dst (SOReg src))
        else if opc = 0xa4 then
          Some (BPF_ALU BPF_XOR   dst (SOImm imm))
        else if opc = 0xac then
          Some (BPF_ALU BPF_XOR   dst (SOReg src))
        else if opc = 0xb4 then
          Some (BPF_ALU BPF_MOV   dst (SOImm imm))
        else if opc = 0xbc then
          Some (BPF_ALU BPF_MOV   dst (SOReg src))
        else if opc = 0xc4 then
          Some (BPF_ALU BPF_ARSH  dst (SOImm imm))
        else if opc = 0xcc then
          Some (BPF_ALU BPF_ARSH  dst (SOReg src))

        else if opc = 0xd4 then
          Some (BPF_LE            dst imm)
        else if opc = 0xdc then
          Some (BPF_BE            dst imm)
\<comment>\<open>
      else if opc = 0x07 then
        if bpf_off bi = 0 \<and> bpf_src bi = 0 then
          Some (BPF_ALU64 BPF_ADD dst (SOImm imm))
        else None \<close>
        else if opc = 0x0f then
          Some (BPF_ALU64 BPF_ADD dst (SOReg src))
        else if opc = 0x17 then
          Some (BPF_ALU64 BPF_SUB dst (SOImm imm))
        else if opc = 0x1f then
          Some (BPF_ALU64 BPF_SUB dst (SOReg src))
        else if opc = 0x27 then
          Some (BPF_ALU64 BPF_MUL dst (SOImm imm))
        else if opc = 0x2f then
          Some (BPF_ALU64 BPF_MUL dst (SOReg src))
        else if opc = 0x37 then
          Some (BPF_ALU64 BPF_DIV dst (SOImm imm))
        else if opc = 0x3f then
          Some (BPF_ALU64 BPF_DIV dst (SOReg src))
        else if opc = 0x47 then
          Some (BPF_ALU64 BPF_OR  dst (SOImm imm))
        else if opc = 0x4f then
          Some (BPF_ALU64 BPF_OR  dst (SOReg src))
        else if opc = 0x57 then
          Some (BPF_ALU64 BPF_AND dst (SOImm imm))
        else if opc = 0x5f then
          Some (BPF_ALU64 BPF_AND dst (SOReg src))
        else if opc = 0x67 then
          Some (BPF_ALU64 BPF_LSH dst (SOImm imm))
        else if opc = 0x6f then
          Some (BPF_ALU64 BPF_LSH dst (SOReg src))
        else if opc = 0x77 then
          Some (BPF_ALU64 BPF_RSH dst (SOImm imm))
        else if opc = 0x7f then
          Some (BPF_ALU64 BPF_RSH dst (SOReg src))

        else if opc = 0x87 then
          Some (BPF_NEG64_REG     dst)

        else if opc = 0x97 then
          Some (BPF_ALU64 BPF_MOD dst (SOImm imm))
        else if opc = 0x9f then
          Some (BPF_ALU64 BPF_MOD dst (SOReg src))
        else if opc = 0xa7 then
          Some (BPF_ALU64 BPF_XOR dst (SOImm imm))
        else if opc = 0xaf then
          Some (BPF_ALU64 BPF_XOR dst (SOReg src))
        else if opc = 0xb7 then
          Some (BPF_ALU64 BPF_MOV dst (SOImm imm))
        else if opc = 0xbf then
          Some (BPF_ALU64 BPF_MOV dst (SOReg src))
        else if opc = 0xc7 then
          Some (BPF_ALU64 BPF_ARSH  dst (SOImm imm))
        else if opc = 0xcf then
          Some (BPF_ALU64 BPF_ARSH  dst (SOReg src))

        else if opc = 0xf7 then
          Some (BPF_HOR64_IMM     dst imm)

        else if opc = 0x86 then
          Some (BPF_PQR BPF_LMUL    dst (SOImm imm))
        else if opc = 0x8e then
          Some (BPF_PQR BPF_LMUL    dst (SOReg src))
        else if opc = 0x96 then
          Some (BPF_PQR64 BPF_LMUL  dst (SOImm imm))
        else if opc = 0x9e then
          Some (BPF_PQR64 BPF_LMUL  dst (SOReg src))

        else if opc = 0x36 then
          Some (BPF_PQR2 BPF_UHMUL  dst (SOImm imm))
        else if opc = 0x3e then
          Some (BPF_PQR2 BPF_UHMUL  dst (SOReg src))
        else if opc = 0xb6 then
          Some (BPF_PQR2 BPF_SHMUL  dst (SOImm imm))
        else if opc = 0xbe then
          Some (BPF_PQR2 BPF_SHMUL  dst (SOReg src))

        else if opc = 0x46 then
          Some (BPF_PQR BPF_UDIV    dst (SOImm imm))
        else if opc = 0x4e then
          Some (BPF_PQR BPF_UDIV    dst (SOReg src))
        else if opc = 0x56 then
          Some (BPF_PQR64 BPF_UDIV  dst (SOImm imm))
        else if opc = 0x5e then
          Some (BPF_PQR64 BPF_UDIV  dst (SOReg src))

        else if opc = 0x66 then
          Some (BPF_PQR BPF_UREM    dst (SOImm imm))
        else if opc = 0x6e then
          Some (BPF_PQR BPF_UREM    dst (SOReg src))
        else if opc = 0x76 then
          Some (BPF_PQR64 BPF_UREM  dst (SOImm imm))
        else if opc = 0x7e then
          Some (BPF_PQR64 BPF_UREM  dst (SOReg src))

        else if opc = 0xc6 then
          Some (BPF_PQR BPF_SDIV    dst (SOImm imm))
        else if opc = 0xce then
          Some (BPF_PQR BPF_SDIV    dst (SOReg src))
        else if opc = 0xd6 then
          Some (BPF_PQR64 BPF_SDIV  dst (SOImm imm))
        else if opc = 0xde then
          Some (BPF_PQR64 BPF_SDIV  dst (SOReg src))

        else if opc = 0xe6 then
          Some (BPF_PQR BPF_SREM    dst (SOImm imm))
        else if opc = 0xee then
          Some (BPF_PQR BPF_SREM    dst (SOReg src))
        else if opc = 0xf6 then
          Some (BPF_PQR64 BPF_SREM  dst (SOImm imm))
        else if opc = 0xfe then
          Some (BPF_PQR64 BPF_SREM  dst (SOReg src))

        else if opc = 0x05 then
          Some (BPF_JA off)

        else if opc = 0x15 then
          Some (BPF_JUMP Eq  dst (SOImm imm) off)
        else if opc = 0x1d then
          Some (BPF_JUMP Eq  dst (SOReg src)          off)
        else if opc = 0x25 then
          Some (BPF_JUMP Gt  dst (SOImm imm) off)
        else if opc = 0x2d then
          Some (BPF_JUMP Gt  dst (SOReg src)          off)
        else if opc = 0x35 then
          Some (BPF_JUMP Ge  dst (SOImm imm) off)
        else if opc = 0x3d then
          Some (BPF_JUMP Ge  dst (SOReg src)          off)
        else if opc = 0xa5 then
          Some (BPF_JUMP Lt  dst (SOImm imm) off)
        else if opc = 0xad then
          Some (BPF_JUMP Lt  dst (SOReg src)          off)
        else if opc = 0xb5 then
          Some (BPF_JUMP Le  dst (SOImm imm) off)
        else if opc = 0xbd then
          Some (BPF_JUMP Le  dst (SOReg src)          off)
        else if opc = 0x45 then
          Some (BPF_JUMP SEt dst (SOImm imm) off)
        else if opc = 0x4d then
          Some (BPF_JUMP SEt dst (SOReg src)          off)
        else if opc = 0x55 then
          Some (BPF_JUMP Ne  dst (SOImm imm) off)
        else if opc = 0x5d then
          Some (BPF_JUMP Ne  dst (SOReg src)          off)
        else if opc = 0x65 then
          Some (BPF_JUMP SGt dst (SOImm imm) off)
        else if opc = 0x6d then
          Some (BPF_JUMP SGt dst (SOReg src)          off)
        else if opc = 0x75 then
          Some (BPF_JUMP SGe  dst (SOImm imm) off)
        else if opc = 0x7d then
          Some (BPF_JUMP SGe  dst (SOReg src)          off)
        else if opc = 0xc5 then
          Some (BPF_JUMP SLt dst (SOImm imm) off)
        else if opc = 0xcd then
          Some (BPF_JUMP SLt dst (SOReg src)          off)
        else if opc = 0xd5 then
          Some (BPF_JUMP SLe dst (SOImm imm) off)
        else if opc = 0xdd then
          Some (BPF_JUMP SLe dst (SOReg src)          off)

        else if opc = 0x8d then
          Some (BPF_CALL_REG src imm)
        else if opc = 0x85 then
          Some (BPF_CALL_IMM src imm)

        else if opc = 0x95 then
          Some BPF_EXIT
        else
          None ))
)"

definition bpf_find_instr :: "nat \<Rightarrow> u8 list \<Rightarrow> bpf_instruction option" where
"bpf_find_instr pc l = (
  let npc= pc*INSN_SIZE in
  let op = l!(npc) in
  let reg = l!(npc+1) in
  let dst = unsigned_bitfield_extract_u8 0 4 reg in
  let src = unsigned_bitfield_extract_u8 4 4 reg in
    case u16_of_u8_list [l!(npc+2), l!(npc+3)] of
    None \<Rightarrow> None |
    Some off_v \<Rightarrow> (
      case u32_of_u8_list [l!(npc+4), l!(npc+5), l!(npc+6), l!(npc+7)] of
      None \<Rightarrow> None |
      Some i \<Rightarrow>
        let (off::i16) = scast off_v in
        let (imm::i32) = scast i in
          rbpf_decoder op (ucast dst) (ucast src) off imm
    )
)"


value "bpf_find_instr 0 [0x07::u8,0x0B,0x00,0x00,0x01,0x02,0x03,0x04] "

end