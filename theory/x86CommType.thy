section \<open> x86 Common Type \<close>

theory x86CommType
imports
  Main
  rBPFCommType
begin

abbreviation "RAX:: u8 \<equiv> 0"
abbreviation "RCX:: u8 \<equiv> 1"
abbreviation "RDX:: u8 \<equiv> 2"
abbreviation "RBX:: u8 \<equiv> 3"
abbreviation "RSP:: u8 \<equiv> 4"
abbreviation "RBP:: u8 \<equiv> 5"
abbreviation "RSI:: u8 \<equiv> 6"
abbreviation "RDI:: u8 \<equiv> 7"
abbreviation "R8 :: u8 \<equiv> 8"
abbreviation "R9 :: u8 \<equiv> 9"
abbreviation "R10:: u8 \<equiv> 10"
abbreviation "R11:: u8 \<equiv> 11"
abbreviation "R12:: u8 \<equiv> 12"
abbreviation "R13:: u8 \<equiv> 13"
abbreviation "R14:: u8 \<equiv> 14"
abbreviation "R15:: u8 \<equiv> 15"

abbreviation "ARGUMENT_REGISTERS
  :: u8 list \<equiv> [RDI, RSI, RDX, RCX, R8, R9]"
abbreviation "CALLER_SAVED_REGISTERS
  :: u8 list \<equiv> [RAX, RCX, RDX, RSI, RDI, R8, R9, R10, R11]"
abbreviation "CALLEE_SAVED_REGISTERS
  :: u8 list \<equiv> [RBP, RBX, R12, R13, R14, R15]"

text \<open> 0100WRXB
@source: P524 (Vol.2A 2.2.1.2 Table 2-4)
The REX prefix allows the use of extended registers and 64-bit operand sizes in the X86 ISA.

 \<close>

record X86Rex =
x86_rex_w :: bool \<comment> \<open> 1 = 64-bit operand size, 0 = Operand size determined by CS.D \<close>
x86_rex_r :: bool \<comment> \<open> Extension of the ModR/M reg field \<close>
x86_rex_x :: bool \<comment> \<open> Extension of the SIB index field \<close>
x86_rex_b :: bool \<comment> \<open> Extension of the ModR/M r/m field, SIB base field, or Opcode reg field \<close>

text \<open> size = 3, align = 0x1 \<close>
record X86ModRm =
x86_rm_mode :: u8
x86_rm_r    :: u8
x86_rm_m    :: u8

text \<open> size = 3, align = 0x1 \<close>
record X86Sib =
x86_sib_scale :: u8
x86_sib_index :: u8
x86_sib_base  :: u8

definition construct_rex_to_u8 :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> u8" where
"construct_rex_to_u8 w r x b =
  or (or (or  ((u8_of_bool w) << 3)
              ((u8_of_bool r) << 2))
          ((u8_of_bool x) << 1))
     (u8_of_bool b)
"

definition construct_modsib_to_u8 :: "u8 \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> u8" where
"construct_modsib_to_u8 op1 op2 op3 = or (or (op1 << 6) (op2 << 3)) op3"

end