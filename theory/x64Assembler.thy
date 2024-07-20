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
  \<comment> \<open> P2882 `MOV register1 to register2` -> `0100 0R0B : 1000 100w : 11 reg1 reg2` \<close>
  Pmovq_rr rd r1 \<Rightarrow>
    \<comment> \<open> P518 `Operand-size override prefix is encoded using 66H` \<close> 
    \<comment> \<open> let (prefix:: u8) = 0x66 in \<close>
    let (rex:: u8) = or 0x40 (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x89 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2887 `ADD register1 to register2` -> `0100 1R0B : 0000 000w : 11 reg1 reg2` \<close>
  Paddq_rr rd r1 \<Rightarrow>
    \<comment>\<open>let (prefix:: u8) = 0x66 in\<close>
    let (rex:: u8) = or 0x40 (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x01 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2891 `SUB register1 from register2` -> `0100 1R0B : 0010 100w : 11 reg1 reg2` \<close>
  Psubq_rr rd r1 \<Rightarrow>
    \<comment> \<open> let (prefix:: u8) = 0x66 in\<close>
    let (rex:: u8) = or 0x40 (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x29 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2884 `NEG register2` -> `0100 100B : 1111 011w : 11011reg` \<close>
  Pnegq rd \<Rightarrow>
    \<comment> \<open> let (prefix:: u8) = 0x66 in\<close>
    let (rex:: u8) = or 0x40 (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b011 (u8_of_ireg rd) in
      Some [rex, op, rop] |
  \<comment> \<open> P2884 `OR register1 to register2` -> ` 0100 1R0B : 0000 100w : 11 reg1 reg2` \<close>
  Porq_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = or 0x40 (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x09 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2876 `AND register1 to register2` -> ` 0100 1R0B : 0000 100w : 11 reg1 reg2` \<close>
  Pandq_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = or 0x40 (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x21 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2893 `XOR qwordregister1 to qwordregister2` -> ` 0100 1R0B : 0011 000w : 11 reg1 reg2` \<close>
  Pxorq_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = or 0x40 (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x31 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2893 `XOR register1 to register2` -> ` 0100 0RXB : 0011 000w : 11 reg1 reg2` \<close>
  Pxorl_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = or 0x40 (construct_rex_to_u8  \<comment> \<open> `0R0B` \<close>
      False \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x31 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2884 `MUL AL, AX, or EAX with register2` -> ` 0100 000B : 1111 100w : 11 reg1 reg2` \<close>
  Pmull_r r1 \<Rightarrow>
    let (rex:: u8) = or 0x40 (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b100 (u8_of_ireg r1) in
      Some [ rex, op, rop] |
 \<comment> \<open> P2884 `MUL RAX with qwordregister (to RDX:RAX)` -> ` 0100 100B : 1111 100w : 11 reg1 reg2` \<close>
  Pmulq_r r1 \<Rightarrow>
    let (rex:: u8) = or 0x40 (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b100 (u8_of_ireg r1) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2884 `IMUL AL, AX, or EAX with register2` -> ` 0100 000B : 1111 101w : 11 reg1 reg2` \<close>
  Pimull_r r1 \<Rightarrow>
    let (rex:: u8) = or 0x40 (construct_rex_to_u8  \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b101 (u8_of_ireg r1) in
      Some [ rex, op, rop] |
 \<comment> \<open> P2880 `IMUL RAX with qwordregister (to RDX:RAX)` -> ` 0100 100B : 1111 101w : 11 reg1 reg2` \<close>
  Pimulq_r r1 \<Rightarrow>
    let (rex:: u8) = or 0x40 (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b101 (u8_of_ireg r1) in
      Some [ rex, op, rop] |
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