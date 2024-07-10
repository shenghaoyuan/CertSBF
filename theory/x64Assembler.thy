section \<open> x64 Assembler \<close>

theory x64Assembler
imports
  Main
  rBPFCommType
  x64Syntax
begin

fun x64_assemble_one_instruction :: "instruction \<Rightarrow> x64_bin option" where
"x64_assemble_one_instruction ins = (
  case ins of
  Pmov_rr rd r1 \<Rightarrow>
    let (prefix:: u8) = 0x66 in
    let (rex:: u8) = 0x41 in  \<comment> \<open> `TBC: 0R0B` Currently, I set it to 1, just for test \<close>
    let (op:: u8) = 0x89 in \<comment> \<open> MOV register1 to register2 : 0100 0R0B : 1000 100w : 11 reg1 reg2 \<close>
    let (rop::u8) = (or (or (0b11 << 6)
                            ((u8_of_ireg rd) << 3) )
                            (u8_of_ireg r1) ) in
      Some [prefix, rex, op, rop] |
  _ \<Rightarrow> None
  )"

fun x64_assemble :: "x64_asm \<Rightarrow> x64_bin option" where
"x64_assemble l = None"


end