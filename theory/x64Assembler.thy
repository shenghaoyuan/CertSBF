section \<open> x64 Assembler \<close>

theory x64Assembler
imports
  Main
  rBPFCommType
  x86CommType x64Syntax
begin

fun x64_assemble_one_instruction :: "instruction \<Rightarrow> x64_bin option" where
"x64_assemble_one_instruction ins = (
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
    let (op:: u8) = 0x89 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b000 (u8_of_ireg rd) in
    let (imm::u8) = ucast n in
    if rex = 0 then
      Some [prefix, op, rop, imm]
    else
      let rex = bitfield_insert_u8 4 4 rex 0x4 in 
        Some [prefix, rex, op, rop, imm] |
  Pmov_rm a r1 c \<Rightarrow> 
    if r1 = R10 then 
      case a of Addrmode (Some r11) None z \<Rightarrow> 
        if r11 =  R11 \<and> z = 0 then (
          let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> 0R0B \<close>
            (c = M64) \<comment> \<open> W \<close>
            True \<comment> \<open> R \<close>
            True \<comment> \<open> X \<close>
            True \<comment> \<open> B \<close>
            ) in
          let (rop::u8) = construct_modsib_to_u8 0b01 (u8_of_ireg R10) (u8_of_ireg R11) in
          \<comment> \<open> P2882 ` MOV: reg to memory`             ->  `0100 0RXB : 1000 1000 : mod reg r/m `\<close>
          \<comment> \<open> P2882 ` MOV: reg to memory`             ->  `66H 0100 0RXB : 1000 1001 : mod reg r/m `\<close>
          \<comment> \<open> P2882 ` MOV: reg to memory`             ->  `0100 0RXB : 1000 1001 : mod reg r/m` \<close>
          \<comment> \<open> P2882 ` MOV: qwordregister to memory64` ->  `0100 1RXB 1000 1001 : mod qwordreg r/m` \<close>
          case c of 
            M8  \<Rightarrow> Some [rex, 0x88, rop] |
            M16 \<Rightarrow> Some [0x66,rex, 0x89, rop] |
            M32 \<Rightarrow> Some [rex, 0x89, rop] |
            M64 \<Rightarrow> Some [rex, 0x89, rop]
          )
        else None
      | _ \<Rightarrow> None 
    else None |
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
    if rex = 0 then
      Some [op, rop]
    else
      let rex = bitfield_insert_u8 4 4 rex 0x4 in 
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
      Some [ rex, op, rop] |
  \<comment> \<open> P2876 `ADD register1 to register2` -> `0100 1R0B : 0000 000w : 11 reg1 reg2` \<close>
  Paddl_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `0R0B` \<close>
      False \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x01 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop] |
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
      Some [ rex, op, rop] |
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
      Some [ rex, op, rop] |
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
      Some [ rex, op, rop] |
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
      Some [rex, op, rop] |
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
      Some [rex, op, rop] |
  \<comment> \<open> P2884 `OR register1 to register2` -> ` 0000 100w : 11 reg1 reg2` \<close>
  Porl_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      False \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x09 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop] |
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
      Some [ rex, op, rop] |
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
      Some [ rex, op, rop] |
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
      Some [ rex, op, rop] |
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
      Some [ rex, op, rop] |
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
      Some [ rex, op, rop] |
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
      Some [ rex, op, rop] |
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
      Some [ rex, op, rop, imm] |
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
      Some [ rex, op, rop, imm] |
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
      Some [ rex, op, rop] |
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
      Some [ rex, op, rop, imm] |
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
  \<comment> \<open> P2890 `SHR register by CL`                   -> ` 0100 000B 1101 001w : 11 101 reg ` \<close>
  Pshrl_r rd  \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xd3 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b101 (u8_of_ireg rd) in
      Some [ rex, op, rop ] |
  \<comment> \<open> P2890 `SHR qwrodregister by CL`              -> ` 0100 100B 1101 001w : 11 101 reg ` \<close>
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
      Some [ rex, op, rop, imm] |
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
      Some [ rex, op, rop, imm] |
  \<comment> \<open> P2888 `SAR register by CL`                   -> ` 0100 000B 1101 001w : 11 111 reg ` \<close>
  Psarl_r rd  \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xd3 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b111 (u8_of_ireg rd) in
      Some [ rex, op, rop ] |
  \<comment> \<open> P2888 `SAR qwordregister by CL`              -> ` 0100 100B 1101 001w : 11 111 reg ` \<close>
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
  Prdtsc \<Rightarrow> 
    let (opes::u8) = 0x0f in
    let (op::u8)   = 0x31 in
      Some [opes,op] |
  \<comment> \<open> P2884 `NOP – No Operation` -> `1001 0000` \<close>
  Pnop \<Rightarrow> Some [0x90] |
  _ \<Rightarrow> None
  )"

fun x64_assemble :: "x64_asm \<Rightarrow> x64_bin option" where
"x64_assemble [] = Some []" |
"x64_assemble (h#t) = (
  case x64_assemble_one_instruction h of
  None \<Rightarrow> None |
  Some l1 \<Rightarrow> (
    case x64_assemble t of
    None \<Rightarrow> None |
    Some l \<Rightarrow> Some (l1@l)
  )
)"

end