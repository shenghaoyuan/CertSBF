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
  Pmov_rr rd r1 \<Rightarrow>
    let (prefix:: u8) = 0x66 in  \<comment> \<open> P518 `Operand-size override prefix is encoded using 66H`  \<close>
    let (rex:: u8) = or 0x40 (construct_rex_to_u8  \<comment> \<open> `0R0B` \<close>
      False \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x89 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg rd) (u8_of_ireg r1) in
      Some [prefix, rex, op, rop] |

  \<comment> \<open> P2884 `NOP – No Operation` -> `1001 0000` \<close>
  Pnop \<Rightarrow> Some [0x90] |
  _ \<Rightarrow> None
  )"

fun x64_assemble :: "x64_asm \<Rightarrow> x64_bin option" where
"x64_assemble l = None"


end