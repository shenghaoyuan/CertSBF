section \<open> x64 Assembler \<close>

theory x64Assembler
imports
  Main
  rBPFCommType
  x86CommType x64Syntax
begin

fun x64_encode :: "instruction \<Rightarrow> x64_bin option" where
"x64_encode ins = (
  case ins of
  \<comment> \<open> P518 `Operand-size override prefix is encoded using 66H` \<close> 
  \<comment> \<open> P2887 `ROL : register by immediate count` -> `0x66 1100 000w : 11 000 reg : imm8` \<close>
  Prolw_ri rd n \<Rightarrow>
    let (prefix:: u8) = 0x66 in
    let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> `0R0B` \<close>
        False \<comment> \<open> W \<close>
        False \<comment> \<open> R \<close>
        False \<comment> \<open> X \<close>
        (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
        ) in
    let (op:: u8) = 0xc1 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b000 (u8_of_ireg rd) in
    let (imm::u8) = ucast n in
    if rex = 0x40 then
      Some [prefix, op, rop, imm]
    else
      Some [prefix, rex, op, rop, imm] |
  \<comment> \<open> P2882 ` MOV: memory to reg`             ->  `0100 0RXB : 1000 101w : mod reg r/m`\<close>
  \<comment> \<open> P2882 ` MOV: memory64 to qwordregister` ->  `0100 1RXB : 1000 1011 : mod qwordreg r/m`\<close>
  Pmov_rm rd a c \<Rightarrow>( 
    case a of Addrmode (Some rb) None dis \<Rightarrow> (
      let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> WRXB \<close>
        (c = M64) \<comment> \<open> W \<close>
        (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
        False \<comment> \<open> X \<close>
        (and (u8_of_ireg rb) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
        ) in
      if dis \<le> 127 \<or> dis \<ge> -128 then   \<comment> \<open> displacement8 : mod 01\<close>
        let (dis::u8) = scast dis in
        let (rop::u8) = construct_modsib_to_u8 0b01 (u8_of_ireg rd) (u8_of_ireg rb) in
        if rex = 0x40 then    
          case c of 
            M32 \<Rightarrow> Some [0x8b, rop, dis] |
            _   \<Rightarrow> None
        else 
          case c of 
            M32 \<Rightarrow> Some [rex, 0x8b, rop, dis] |
            M64 \<Rightarrow> Some [rex, 0x8b, rop, dis] |
            _   \<Rightarrow> None
      else if (and (u8_of_ireg rb) 0b0111 \<noteq> 0b100) then   \<comment> \<open> displacement8 : mod 10\<close>
        let (rop::u8) = construct_modsib_to_u8 0b10 (u8_of_ireg rd) (u8_of_ireg rb) in
          if rex = 0x40 then    
            case c of 
              M32 \<Rightarrow> Some ([0x8b, rop] @ (u8_list_of_u32 dis)) |
              _   \<Rightarrow> None
          else 
            case c of 
              M32 \<Rightarrow> Some ([rex, 0x8b, rop] @ (u8_list_of_u32 dis)) |
              M64 \<Rightarrow> Some ([rex, 0x8b, rop] @ (u8_list_of_u32 dis)) |
              _   \<Rightarrow> None  
        else None)
    |  Addrmode (Some rb) (Some (ri,scale)) dis \<Rightarrow>(
        if scale > 3 | c \<noteq> M64 then None
        else( 
          let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> 1RXB \<close>
            True \<comment> \<open> W \<close>
            (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
            (and (u8_of_ireg ri) 0b1000 \<noteq> 0) \<comment> \<open> X \<close>
            (and (u8_of_ireg rb) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
            ) in
          let (op:: u8) = 0x8b in
          let (rop::u8) = construct_modsib_to_u8 0b10 (u8_of_ireg rd) 0b100 in
          let (sib::u8) = construct_modsib_to_u8 scale (u8_of_ireg ri) (u8_of_ireg rb) in
            Some ([rex, op, rop, sib] @ (u8_list_of_u32 dis))))
    | _ \<Rightarrow> None) 
  |
  \<comment> \<open> P2882 ` MOV: reg to memory`             ->  `0100 0RXB : 1000 1000 : mod reg r/m `\<close>
  \<comment> \<open> P2882 ` MOV: reg to memory`             ->  `66H 0100 0RXB : 1000 1001 : mod reg r/m `\<close>
  \<comment> \<open> P2882 ` MOV: reg to memory`             ->  `0100 0RXB : 1000 1001 : mod reg r/m` \<close>
  \<comment> \<open> P2882 ` MOV: qwordregister to memory64` ->  `0100 1RXB 1000 1001 : mod qwordreg r/m` \<close>
  Pmov_mr  a r1 c \<Rightarrow> (
    case a of Addrmode (Some rb) None dis \<Rightarrow> 
      let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> WRXB \<close>
        (c = M64) \<comment> \<open> W \<close>
        (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
        False \<comment> \<open> X \<close>
        (and (u8_of_ireg rb) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
        ) in
      if dis \<le> 127 \<or> dis \<ge> -128  then   \<comment> \<open> displacement8 : mod 01 \<close>
        let (dis::u8) = scast dis in
        let (rop::u8) = construct_modsib_to_u8 0b01 (u8_of_ireg r1) (u8_of_ireg rb) in
        if rex = 0x40 then(
          case c of 
            M8  \<Rightarrow> Some [0x88, rop, dis] |
            M16 \<Rightarrow> Some [0x66, 0x89, rop, dis] |
            M32 \<Rightarrow> Some [0x89, rop, dis] |
            _   \<Rightarrow> None)
        else (
          case c of 
            M8  \<Rightarrow> Some [rex, 0x88, rop, dis] |
            M16 \<Rightarrow> Some [0x66,rex, 0x89, rop, dis] |
            M32 \<Rightarrow> Some [rex, 0x89, rop, dis] |
            M64 \<Rightarrow> Some [rex, 0x89, rop, dis])
      else if (and (u8_of_ireg rb) 0b0111 \<noteq> 0b100) then   \<comment> \<open> displacement8 : mod 10\<close>       
        let (rop::u8) = construct_modsib_to_u8 0b10 (u8_of_ireg r1) (u8_of_ireg rb) in
        if rex = 0x40 then(
          case c of 
            M32 \<Rightarrow> Some ([0x89, rop] @ (u8_list_of_u32 dis)) |
            _   \<Rightarrow> None)
        else (
          case c of 
            M32 \<Rightarrow> Some ([rex, 0x89, rop] @ (u8_list_of_u32 dis)) |
            M64 \<Rightarrow> Some ([rex, 0x89, rop] @ (u8_list_of_u32 dis)) |
            _   \<Rightarrow> None)
        else None
    |  Addrmode (Some rb) (Some (ri,scale)) dis \<Rightarrow>
        if scale > 3 | c \<noteq> M64 then None
        else 
          let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> 1RXB \<close>
            True \<comment> \<open> W \<close>
            (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
            (and (u8_of_ireg ri) 0b1000 \<noteq> 0) \<comment> \<open> X \<close>
            (and (u8_of_ireg rb) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
            ) in
        let (op:: u8) = 0x89 in
        let (rop::u8) = construct_modsib_to_u8 0b10 (u8_of_ireg r1) 0b100 in
        let (sib::u8) = construct_modsib_to_u8 scale (u8_of_ireg ri) (u8_of_ireg rb) in
            Some ([rex, op, rop, sib] @ (u8_list_of_u32 dis))
    | _ \<Rightarrow> None) 
  |
  \<comment> \<open> P2887 `MOV register1 to register2` -> `0100 0R0B : 1000 1001 : 11 reg1 reg2` \<close>
  Pmovl_rr rd r1 \<Rightarrow>
    let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> `0R0B` \<close>
      False \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x89 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
    if rex = 0x40 then
      Some [op, rop]
    else
      Some [rex, op, rop] |
  \<comment> \<open> P2882 `MOV qwordregister1 to qwordregister2` -> `0100 1R0B : 1000 1001 : 11 reg1 reg2` \<close>
  Pmovq_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x89 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop ] |
  \<comment> \<open> P2882 `MOV immediate to register` -> `0100 000B : 1100 011w : 11 000 reg : imm` \<close>
  Pmovl_ri rd n \<Rightarrow>
    let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xc7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b000 (u8_of_ireg rd) in
      if rex = 0x40 then
        Some ([op, rop] @ (u8_list_of_u32 n))
      else
        Some ([rex, op, rop] @ (u8_list_of_u32 n)) |
  \<comment> \<open> P2882 `MOV immediate64 to qwordregister (alternate encoding)` -> `0100 100B 1011 1reg : imm64` \<close>
  Pmovq_ri rd n \<Rightarrow>
    let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = bitfield_insert_u8 0 3 0xb8 (u8_of_ireg rd) in
      Some ([rex, op] @ u8_list_of_u64 n)|
  \<comment> \<open> P2882 `MOV immediate32 to memory64 (zero extend)` -> ` 0100 10XB 1100 0111 : mod 000 r/m : imm32` \<close>
  Pmov_mi a n M64 \<Rightarrow>(
    case a of Addrmode (Some rd) None dis \<Rightarrow>( 
      let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
        True \<comment> \<open> W \<close>
        False \<comment> \<open> R \<close>
        False \<comment> \<open> X \<close>
        (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
        ) in
      let (op:: u8) = 0xc7 in
        if dis \<le> 127 \<or> dis \<ge> -128  then   \<comment> \<open> displacement8 : mod 01 \<close>
          let (dis::u8) = scast dis in
          let (rop::u8) = construct_modsib_to_u8 0b01 0b000 (u8_of_ireg rd) in
            Some ([ rex, op, rop, dis ] @ (u8_list_of_u32 n))
        else  \<comment> \<open> displacement32 : mod 10 \<close>
          let (rop::u8) = construct_modsib_to_u8 0b10 0b000 (u8_of_ireg rd) in
            Some ([ rex, op, rop ] @ (u8_list_of_u32 dis) @ (u8_list_of_u32 n)) )
    | _\<Rightarrow> None) |
  \<comment> \<open> P2883 `MOVXD dwordregister2 to qwordregister1` -> ` 0100 1R0B 0110 0011 : 11 quadreg1 dwordreg2` \<close>
  Pmovsq_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x63 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg rd) (u8_of_ireg r1) in
      Some [ rex, op, rop ] |
  \<comment> \<open> P2919 `MOVcc : resgister2  to resgister1 ` -> `0100 0R0B 0000 1111: 0100 tttn : 11 reg1 reg2` \<close>
  Pcmovl t rd r1 \<Rightarrow>
    let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> `0R0B` \<close>
      False \<comment> \<open> W \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (ex:: u8) = 0x0f in
    let (op:: u8) = bitfield_insert_u8 0 4 0x40 (u8_of_cond t) in   \<comment> \<open> 45 : NZ/NE （ZF=0 \<close>   
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg rd) (u8_of_ireg r1) in
    if rex = 0x40 then
      Some [ex, op, rop]
    else
      Some [rex, ex, op, rop] |
  \<comment> \<open> P2919 `MOVcc : qwordregister2 to qwordregister1` -> ` 0100 1R0B 0000 1111: 0100 tttn : 11 qwordreg1 qwordreg2` \<close>
  Pcmovq t rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (ex:: u8) = 0x0f in
    let (op:: u8) = bitfield_insert_u8 0 4 0x40 (u8_of_cond t) in  \<comment> \<open> 45 : NZ/NE （ZF=0 \<close> 
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg rd) (u8_of_ireg r1) in
      Some [rex, ex, op, rop] |
  \<comment> \<open> P2893 `XCHG: register1 with register2 `   -> ` 0100 1R0B 1000 011w : 11 reg1 reg2 ` \<close>
  Pxchgq_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op::u8) = 0x87 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [rex, op, rop] |
  \<comment> \<open> P2893 `XCHG: memory64 with qwordregister `   -> ` 0100 1R0B 1000 011w : 11 reg1 reg2 ` \<close>
  Pxchgq_rm r1 a M64 \<Rightarrow>( 
    case a of Addrmode (Some rb) (Some (ri,scale)) dis \<Rightarrow>(
      if scale > 3 then None
      else 
        let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1RXB` \<close>
          True \<comment> \<open> W \<close>
          (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
          (and (u8_of_ireg ri) 0b1000 \<noteq> 0) \<comment> \<open> X \<close>
          (and (u8_of_ireg rb) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
          ) in
        let (op:: u8) = 0x87 in
        let (rop::u8) = construct_modsib_to_u8 0b10 (u8_of_ireg r1) 0b100 in
        let (sib::u8) = construct_modsib_to_u8 scale (u8_of_ireg ri) (u8_of_ireg rb) in
            Some ([rex, op, rop, sib] @ (u8_list_of_u32 dis))
      ) |
      _ \<Rightarrow> None)|
  \<comment> \<open> P2878 `CDQ : sign_extend_eax_edx `   -> ` 1001 1001 ` \<close>  
  Pcdq \<Rightarrow>
    Some [0x99] |
  \<comment> \<open> P2878 `CQO : sign_extend_rax_rdx `   -> ` 0100 1001 1001 1001 ` \<close>
  Pcqo \<Rightarrow>
    Some [0x48, 0x99] |
  \<comment> \<open> P2876 `ADD register1 to register2` -> `0100 0R0B : 0000 000w : 11 reg1 reg2` \<close>
  Paddl_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `0R0B` \<close>
      False \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x01 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      if rex = 0x40 then
        Some [ op, rop ] 
      else 
        Some [ rex, op, rop ] |
 \<comment> \<open> P2876 `ADD immediate to register` -> `0100 000B : 1000 00sw : 11 000 reg : immediate data` \<close>
  Paddl_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x81 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b000 (u8_of_ireg rd) in
    if rex = 0x40 then
      Some ([op, rop] @ u8_list_of_u32 n) 
    else 
      Some  ([rex, op, rop] @ u8_list_of_u32 n) |
 \<comment> \<open> P2876 `ADD imm16 to reg16` -> `0x66 0100 000B : 1000 00sw : 11 000 reg : imm16` \<close>
  Paddw_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x81 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b000 (u8_of_ireg rd) in
    if rex = 0x40 then
      Some ([0x66, op, rop] @ u8_list_of_u16 n) 
    else 
      Some  ([0x66, rex, op, rop] @ u8_list_of_u16 n) |
  \<comment> \<open> P2876 `ADD qwordregister1 to qwordregister2` -> `0100 1R0B : 0000 0001 : 11 reg1 reg2` \<close>
  Paddq_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x01 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop ] |
  \<comment> \<open> P2876 `ADD immediate32 to memory64` -> ` 0100 10XB : 1000 0001 : mod 000 r/m : imm32` \<close>
  Paddq_mi a n M64 \<Rightarrow>( 
    case a of Addrmode (Some rb) (Some (ri,scale)) dis \<Rightarrow>(
      if scale > 3 then None
      else 
        let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `10XB` \<close>
          True \<comment> \<open> W \<close>
          False \<comment> \<open> R \<close>
          (and (u8_of_ireg ri) 0b1000 \<noteq> 0) \<comment> \<open> X \<close>
          (and (u8_of_ireg rb) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
          ) in
        let (op:: u8) = 0x81 in
        let (rop::u8) = construct_modsib_to_u8 0b10 0b000 0b100 in
        let (sib::u8) = construct_modsib_to_u8 scale (u8_of_ireg ri) (u8_of_ireg rb) in
            Some ([rex, op, rop, sib] @ (u8_list_of_u32 dis) @ (u8_list_of_u32 n))
      ) |
      _ \<Rightarrow> None)|
  \<comment> \<open> P2891 `SUB register1 from register2` -> `0100 0R0B : 0010 100w : 11 reg1 reg2` \<close>
  Psubl_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `0R0B` \<close>
      False \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x29 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      if rex = 0x40 then
        Some [ op, rop ] 
      else 
        Some [ rex, op, rop ] |
  \<comment> \<open> P2891 `SUB qwordregister1 from qwordregister2` -> `0100 1R0B : 0010 1001 : 11 reg1 reg2` \<close>
  Psubq_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x29 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop ] |
  \<comment> \<open> P2884 `NEG register2` -> `0100 000B : 1111 011w : 11011reg` \<close>
  Pnegl rd \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b011 (u8_of_ireg rd) in
      if rex = 0x40 then
        Some [ op, rop ] 
      else 
        Some [ rex, op, rop ] |
 \<comment> \<open> P2891 `SUB: immediate from register` -> `0100 000B 1000 00sw : 11 101 reg : imm` \<close>
  Psubl_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x81 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b101 (u8_of_ireg rd) in
      if rex = 0x40 then
        Some ([op, rop] @ u8_list_of_u32 n) 
      else 
        Some  ([rex, op, rop] @ u8_list_of_u32 n) |
  \<comment> \<open> P2884 `NEG register2` -> `0100 100B : 1111 0111 : 11011reg` \<close>
  Pnegq rd \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b011 (u8_of_ireg rd) in
      Some [rex, op, rop ] |
  \<comment> \<open> P2884 `OR register1 to register2` -> ` 0000 100w : 11 reg1 reg2` \<close>
  Porl_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `0R0B` \<close>
      False \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x09 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      if rex = 0x40 then
        Some [ op, rop ] 
      else 
        Some [ rex, op, rop ] |
  \<comment> \<open> P2884 `OR qwordregister1 to qwordregister2` -> ` 0100 1R0B : 0000 1001 : 11 reg1 reg2` \<close>
  Porq_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x09 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop] |
 \<comment> \<open> P2891 `OR: immediate to register` -> `0100 000B  1000 00sw : 11 001 reg : imm` \<close>
  Porl_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x81 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b001 (u8_of_ireg rd) in
      if rex = 0x40 then
        Some ([op, rop] @ u8_list_of_u32 n) 
      else 
        Some  ([rex, op, rop] @ u8_list_of_u32 n) |
  \<comment> \<open> P2876 `AND register1 to register2` -> ` 0100 0R0B : 0010 000w : 11 reg1 reg2` \<close>
  Pandl_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `0R0B` \<close>
      False \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x21 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      if rex = 0x40 then
        Some [ op, rop ] 
      else 
        Some [ rex, op, rop ] |
  \<comment> \<open> P2876 `AND qwordregister1 to qwordregister2` -> ` 0100 1R0B : 0010 0001 : 11 reg1 reg2` \<close>
  Pandq_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x21 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop] |
 \<comment> \<open> P2891 `AND: immediate to register` -> `0100 000B : 1000 00sw : 11 100 reg : immediate` \<close>
  Pandl_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x81 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b100 (u8_of_ireg rd) in
      if rex = 0x40 then
        Some ([op, rop] @ u8_list_of_u32 n) 
      else 
        Some  ([rex, op, rop] @ u8_list_of_u32 n) |
  \<comment> \<open> P2893 `XOR register1 to register2` -> ` 0100 0RXB : 0011 000w : 11 reg1 reg2` \<close>
  Pxorl_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `0R0B` \<close>
      False \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x31 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      if rex = 0x40 then
        Some [ op, rop ] 
      else 
        Some [ rex, op, rop ] |
  \<comment> \<open> P2893 `XOR qwordregister1 to qwordregister2` -> ` 0100 1R0B : 0011 0001 : 11 reg1 reg2` \<close>
  Pxorq_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x31 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2893 `XOR: immediate to register` -> ` 0100 000B 1000 00sw : 11 110 reg : imm` \<close>
  Pxorl_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x81 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b110 (u8_of_ireg rd) in
      if rex = 0x40 then
        Some ([op, rop] @ u8_list_of_u32 n) 
      else 
        Some  ([rex, op, rop] @ u8_list_of_u32 n) |
  \<comment> \<open> P2884 `MUL AL, AX, or EAX with register2` -> ` 0100 000B : 1111 011w : 11 100 reg` \<close>
  Pmull_r r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b100 (u8_of_ireg r1) in
      if rex = 0x40 then
        Some [ op, rop ] 
      else 
        Some [ rex, op, rop ] |
  \<comment> \<open> P2884 `MUL RAX with qwordregister (to RDX:RAX)` -> ` 0100 100B : 1111 0111 : 11 100 qowrdreg` \<close>
  Pmulq_r r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b100 (u8_of_ireg r1) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2880 `IMUL AL, AX, or EAX with register2` -> ` 0100 000B : 1111 011w : 11 101 reg` \<close>
  Pimull_r r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b101 (u8_of_ireg r1) in
      if rex = 0x40 then
        Some [ op, rop ] 
      else 
        Some [ rex, op, rop ] |
  \<comment> \<open> P2880 `IMUL RAX with qwordregister (to RDX:RAX)` -> ` 0100 100B : 1111 0111 : 11 101 qwordreg` \<close>
  Pimulq_r r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b101 (u8_of_ireg r1) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2879 `DIV AL, AX, or EAX by register2` -> ` 0100 000B : 1111 011w : 11 110eg` \<close>
  Pdivl_r r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b110 (u8_of_ireg r1) in
      if rex = 0x40 then
        Some [ op, rop ] 
      else 
        Some [ rex, op, rop ] |
  \<comment> \<open> P2879 `DIV EAX by qwordregister (to RDX:RAX)` -> ` 0100 100B : 1111 0111 : 11 110 qwordreg` \<close>
  Pdivq_r r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b110 (u8_of_ireg r1) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2879 `IDIV AL, AX, or EAX by register2` -> ` 0100 000B : 1111 011w : 11 111 reg` \<close>
  Pidivl_r r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b111 (u8_of_ireg r1) in
      if rex = 0x40 then
        Some [ op, rop ] 
      else 
        Some [ rex, op, rop ] |
  \<comment> \<open> P2879 `IDIV RAX by qwordregister (to RDX:RAX)` -> ` 0100 100B : 1111 0111 : 11 111 qwordreg` \<close>
  Pidivq_r r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b111 (u8_of_ireg r1) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2889 `SHL register by immediate count`      -> ` 0100 000B 1100 000w : 11 100 reg : imm8 ` \<close>
  Pshll_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xc1 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b100 (u8_of_ireg rd) in
    let (imm::u8) = ucast n in
      if rex = 0x40 then
        Some [ op, rop, imm ] 
      else 
        Some [ rex, op, rop, imm ] |
  \<comment> \<open> P2889 `SHL qwordregister by immediate count` -> ` 0100 100B 1100 0001 : 11 100 reg : imm8 ` \<close>
  Pshlq_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xc1 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b100 (u8_of_ireg rd) in
    let (imm::u8) = ucast n in
      Some [ rex, op, rop, imm ] |
  \<comment> \<open> P2889 `SHL register by CL`                   -> ` 0100 000B 1101 001w : 11 100 reg ` \<close>
  Pshll_r rd  \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xd3 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b100 (u8_of_ireg rd) in
      if rex = 0x40 then
        Some [ op, rop ] 
      else 
        Some [ rex, op, rop ] |
  \<comment> \<open> P2889 `SHL qwordregister by CL`              -> ` 0100 100B 1101 001w : 11 100 reg ` \<close>
  Pshlq_r rd  \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xd3 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b100 (u8_of_ireg rd) in
      Some [ rex, op, rop ] |
  \<comment> \<open> P2890 `SHR register by immediate count`      -> ` 0100 000B 1100 000w : 11 101 reg : imm8 ` \<close>
  Pshrl_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xc1 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b101 (u8_of_ireg rd) in
    let (imm::u8) = ucast n in
      if rex = 0x40 then
        Some [ op, rop, imm ] 
      else 
        Some [ rex, op, rop, imm ] |
  \<comment> \<open> P2890 `SHR qwordregister by immediate count` -> ` 0100 100B 1100 000w : 11 101 reg : imm8 ` \<close>
  Pshrq_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xc1 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b101 (u8_of_ireg rd) in
    let (imm::u8) = ucast n in
      Some [ rex, op, rop, imm] |
  \<comment> \<open> P2890 `SHR register by CL`     -> ` 0100 000B 1101 001w : 11 101 reg ` \<close>
  Pshrl_r rd  \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xd3 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b101 (u8_of_ireg rd) in
      if rex = 0x40 then
        Some [ op, rop ] 
      else 
        Some [ rex, op, rop ] |
  \<comment> \<open> P2890 `SHR qwrodregister by CL`   -> ` 0100 100B 1101 001w : 11 101 reg ` \<close>
  Pshrq_r rd  \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xd3 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b101 (u8_of_ireg rd) in
      Some [ rex, op, rop ] |
  \<comment> \<open> P2888 `SAR register by immediate count`      -> ` 0100 000B 1100 000w : 11 111 reg : imm8 ` \<close>
  Psarl_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xc1 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b111 (u8_of_ireg rd) in
    let (imm::u8) = ucast n in
      if rex = 0x40 then
        Some [ op, rop, imm ] 
      else 
        Some [ rex, op, rop, imm ] |
  \<comment> \<open> P2888 `SAR qwordregister by immediate count` -> ` 0100 100B 1100 000w : 11 111 reg : imm8 ` \<close>
  Psarq_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xc1 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b111 (u8_of_ireg rd) in
    let (imm::u8) = ucast n in
      Some [ rex, op, rop, imm ] |
  \<comment> \<open> P2888 `SAR register by CL`     -> ` 0100 000B 1101 001w : 11 111 reg ` \<close>
  Psarl_r rd  \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xd3 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b111 (u8_of_ireg rd) in
      if rex = 0x40 then
        Some [ op, rop ] 
      else 
        Some [ rex, op, rop ] |
  \<comment> \<open> P2888 `SAR qwordregister by CL`     -> ` 0100 100B 1101 001w : 11 111 reg ` \<close>
  Psarq_r rd  \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xd3 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b111 (u8_of_ireg rd) in
      Some [ rex, op, rop ] |
  \<comment> \<open> P2877 `BSWAP: register `   -> `0000 1111 : 1100 1 reg` \<close>
  Pbswapl rd  \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (ex:: u8) = 0x0f in
    let (op:: u8) = bitfield_insert_u8 0 3 0xc8 (u8_of_ireg rd) in
      if rex = 0x40 then
        Some [ex, op]
      else 
        Some [rex, ex, op] |
  \<comment> \<open> P2877 `BSWAP: qwordregister `   -> `0100 100B 0000 1111 : 1100 1 qwordreg` \<close>
  Pbswapq rd  \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (ex:: u8) = 0x0f in
    let (op:: u8) = bitfield_insert_u8 0 3 0xc8 (u8_of_ireg rd) in
      Some [rex, ex, op] |
  \<comment> \<open> P2881 `LEA: Load Effective Address: in qwordregister `  -> `0100 1RXB : 1000 1101 : mod qwordreg r/m` \<close>
  Pleaq rd a \<Rightarrow>(
    case a of Addrmode (Some rb) None dis \<Rightarrow>(
      let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
        True \<comment> \<open> W \<close>
        (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
        False \<comment> \<open> X \<close>
        (and (u8_of_ireg rb) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
        ) in
      let (op:: u8) = 0x8d in
        if dis \<le> 127 \<or> dis \<ge> -128  then   \<comment> \<open> displacement8 : mod 01 \<close>
          let (dis::u8) = scast dis in
          let (rop::u8) = construct_modsib_to_u8 0b01 (u8_of_ireg rd) (u8_of_ireg rb) in
            Some ([ rex, op, rop, dis ])
        else  \<comment> \<open> displacement32 : mod 10 \<close>
          let (rop::u8) = construct_modsib_to_u8 0b10 (u8_of_ireg rd) (u8_of_ireg rb) in
              Some ([ rex, op, rop ] @ (u8_list_of_u32 dis)))
      | _ \<Rightarrow> None)|
  \<comment> \<open> P2886 `RDTSC – Read Time-Stamp Counter`   -> ` 0000 1111 0011 0001 ` \<close>
  Prdtsc \<Rightarrow>
    let (opes::u8) = 0x0f in
    let (op  ::u8) = 0x31 in
      Some [opes,op] |
  \<comment> \<open> P2885 `PUSH: qwordregister (alternate encoding)`   -> ` 0100 W00BS : 0101 0 reg64` \<close>
  Ppushl_r  r1 \<Rightarrow>
    let (rex::u8) = (construct_rex_to_u8    \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op::u8) = bitfield_insert_u8 0 3 0x50 (u8_of_ireg r1) in
      if rex = 0x40 then
        Some [op]
      else 
        Some [rex, op] |
  \<comment> \<open> P2885 `PUSH: memory64`   -> ` 0100 W00BS : 1111 1111 : 11 110 reg64 ` \<close>
  \<comment> \<open> P2885 `PUSH: imm32`   -> ` 0110 1000 : imm32 ` \<close>
  Ppushl_i n \<Rightarrow>
    let (rex::u8) = (construct_rex_to_u8    \<comment> \<open> `100B` \<close>
      True  \<comment> \<open> W ; Solana may made mistake here, but it won't bring mistakes \<close> 
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      False \<comment> \<open> B \<close>
      ) in
    let (op::u8) = 0x68 in
      Some ([rex,op] @ (u8_list_of_u32 n)) |
  \<comment> \<open> P2885 `PUSH: memory64`   -> `0100 W00BS : 1111 1111 : mod 110 r/m ` \<close>
  Ppushq_m a M64 \<Rightarrow>(
    case a of Addrmode (Some rb) (Some (ri,scale)) dis \<Rightarrow>(
      if scale > 3 then None
      else 
        let (rex::u8) = (construct_rex_to_u8    \<comment> \<open> `100B` \<close>
        True \<comment> \<open> W \<close>
        False \<comment> \<open> R \<close>
        (and (u8_of_ireg ri) 0b1000 \<noteq> 0) \<comment> \<open> X \<close>
        (and (u8_of_ireg rb) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
        ) in
      let (op::u8) = 0xff in 
      let (rop::u8) = construct_modsib_to_u8 0b10 0b110 0b100 in
      let (sib::u8) = construct_modsib_to_u8 scale (u8_of_ireg ri) (u8_of_ireg rb) in
         Some ([rex, op, rop, sib] @ (u8_list_of_u32 dis)))
    | _ \<Rightarrow> None)|
  \<comment> \<open> P2885 `POP: qwordregister (alternate encoding)`   -> ` 0100 W00B : 0101 1 reg64 ` \<close>
  Ppopl rd \<Rightarrow>
    let (rex::u8) = (construct_rex_to_u8    \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op::u8) = bitfield_insert_u8 0 3 0x58 (u8_of_ireg rd) in
      if rex = 0x40 then
        Some [op]
      else 
        Some [rex, op] |
  \<comment> \<open> P2892 `TEST: register1 and register2`   -> ` 0100 0R0B 1000 010w : 11 reg1 reg2` \<close>
  Ptestl_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `0R0B` \<close>
      False \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x85 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      if rex = 0x40 then
        Some [op, rop]
      else 
        Some [rex, op, rop]|
 \<comment> \<open> P2892 `TEST:  qwordregister1 and qwordregister2`   -> ` 0100 1R0B 1000 0101 : 11 qwordreg1 qwordreg2` \<close>
  Ptestq_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x85 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [rex, op, rop]|
  \<comment> \<open> P2892 `TEST: immediate and register`   -> ` 0100 000B 1111 011w : 11 000 reg : imm ` \<close>
  Ptestl_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b000 (u8_of_ireg rd) in
      if rex = 0x40 then
        Some ([op, rop] @ (u8_list_of_u32 n))
      else 
        Some ([rex, op, rop] @ (u8_list_of_u32 n))|
  \<comment> \<open> P2892 `TEST: immediate32 and qwordregister `   -> ` 0100 100B 1111 0111 : 11 000 qwordreg : imm32 ` \<close>
  Ptestq_ri rd n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `0R0B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b000 (u8_of_ireg rd) in
      Some ([rex, op, rop] @ (u8_list_of_u32 n))|
  \<comment> \<open> P2878 `CMP: register1 with register2`   -> ` 0100 0R0B 0011 100w : 11 reg1 reg2 ` \<close>
  Pcmpl_rr r1 r2 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `0R0B` \<close>
      False \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r2) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x39 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg r2) in
      if rex = 0x40 then
        Some [op, rop]
      else 
        Some [rex, op, rop] |
  \<comment> \<open> P2878 `CMP: qwordregister1 with qwordregister2`   -> `0100 1R0B 0011 1001 : 11 qwordreg1 qwordreg2` \<close>
  Pcmpq_rr r1 r2 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True  \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r2) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x39 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg r2) in
      Some [rex, op, rop]|
  \<comment> \<open> P2878 `CMP: immediate with register`   -> `0100 000B 1000 00sw : 11 111 reg : imm` \<close>
  Pcmpl_ri r1 n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `0R0B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x81 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b111 (u8_of_ireg r1) in
      if rex = 0x40 then
        Some ([op, rop] @ (u8_list_of_u32 n))
      else 
        Some ([rex, op, rop] @ (u8_list_of_u32 n))|
  \<comment> \<open> P2878 `CMP: immediate32 with qwordregister`   -> `0100 100B 1000 0001 : 11 111 qwordreg : imm32` \<close>
  Pcmpq_ri r1 n \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `0R0B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x81 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b111 (u8_of_ireg r1) in
      Some ([rex, op, rop] @ (u8_list_of_u32 n))|
  \<comment> \<open> P2881 `JMP: direct` -> `1110 1001 : displacement32` \<close>
  Pjmp d \<Rightarrow>
    let (op:: u8) = 0xe9 in
      Some ([op] @ (u8_list_of_u32 (ucast d)))|
  \<comment> \<open> P2880 `JCC: full displacement` -> `0000 1111 : 1000 tttn : full displacement` \<close>
  Pjcc t d \<Rightarrow>
    let (ex:: u8) = 0x0f in
    let (op:: u8) = bitfield_insert_u8 0 4 0x80 (u8_of_cond t) in
    Some ([ex, op] @ (u8_list_of_u32 (ucast d))) |
  \<comment> \<open> P2878 `CALL: register indirect`   -> `0100 W00Bw 1111 1111 : 11 010 reg ` \<close>
  Pcall_r r1 \<Rightarrow>
    let (rex::u8) = (construct_rex_to_u8    \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
      let (op:: u8) = 0xff in
      let (rop::u8) = construct_modsib_to_u8 0b11 0b010 (u8_of_ireg r1) in
      if rex = 0x40 then
        Some [op, rop]
      else 
        Some [rex, op, rop] |
  \<comment> \<open> P2878 `CALL: direct`   -> `1110 1000 : displacement32` \<close>
  Pcall_i d  \<Rightarrow>
      Some ([0xe8] @ (u8_list_of_u32 d))|
  \<comment> \<open> P2887 ` RET near`   -> ` 1100 0011` \<close>
  Pret \<Rightarrow>
    Some [0xc3]|
  \<comment> \<open> P2884 `NOP – No Operation` -> `1001 0000` \<close>
  Pnop \<Rightarrow> Some [0x90] |
  _ \<Rightarrow> None
  )"

fun x64_assemble :: "x64_asm \<Rightarrow> x64_bin option" where
"x64_assemble [] = Some []" |
"x64_assemble (h#t) = (
  case x64_encode h of
  None \<Rightarrow> None |
  Some l1 \<Rightarrow> (
    case x64_assemble t of
    None \<Rightarrow> None |
    Some l \<Rightarrow> Some (l1@l)
  )
)"

(*
definition x64_encode :: "instruction \<Rightarrow> x64_bin \<Rightarrow> x64_bin option" where
"x64_encode ins l_bin = (
  case x64_assemble_one_instruction ins of
  None    \<Rightarrow> None |
  Some l  \<Rightarrow> Some (l_bin@l)
)"


fun x64_assemble :: "x64_asm \<Rightarrow> x64_bin option" where
"x64_assemble [] = Some []" |
"x64_assemble (h#t) = (
  case x64_assemble t of
  None \<Rightarrow> None |
  Some l1 \<Rightarrow> (
    case x64_encode h [] of
    None \<Rightarrow> None |
    Some l \<Rightarrow> Some (l@l1)
  )
)" 
  Ppushq r1 \<Rightarrow>
    let (rex::u8) = (construct_rex_to_u8    \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op::u8) = 0xff in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b110 (u8_of_ireg r1) in
      Some [rex,op,op] |



*)

fun list_in_list :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool" where
"list_in_list [] _ _ = True" |
"list_in_list (h#t) n l = (h = l!n \<and> list_in_list t (Suc n) l)"

end