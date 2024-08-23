section \<open> x86 Common Type \<close>

theory x86CommType
imports
  Main
  rBPFCommType
begin

definition "RAX:: u8 \<equiv> 0"
definition "RCX:: u8 \<equiv> 1"
definition "RDX:: u8 \<equiv> 2"
definition "RBX:: u8 \<equiv> 3"
definition "RSP:: u8 \<equiv> 4"
definition "RBP:: u8 \<equiv> 5"
definition "RSI:: u8 \<equiv> 6"
definition "RDI:: u8 \<equiv> 7"
definition "R8 :: u8 \<equiv> 8"
definition "R9 :: u8 \<equiv> 9"
definition "R10:: u8 \<equiv> 10"
definition "R11:: u8 \<equiv> 11"
definition "R12:: u8 \<equiv> 12"
definition "R13:: u8 \<equiv> 13"
definition "R14:: u8 \<equiv> 14"
definition "R15:: u8 \<equiv> 15"

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

definition construct_rex_to_u8 :: "bool\<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>u8" where
"construct_rex_to_u8 w r x b =
   bitfield_insert_u8 4 4 
    (bitfield_insert_u8 3 1
      (bitfield_insert_u8 2 1
        (bitfield_insert_u8 1 1 (u8_of_bool b)
                                (u8_of_bool x))
        (u8_of_bool r))
      (u8_of_bool w))
     0x4
"

\<comment> \<open>\\\value "construct_rex_to_u8 False False False True" \<close>

definition construct_modsib_to_u8 :: "u8 \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> u8" where
"construct_modsib_to_u8 op1 op2 op3 =
  bitfield_insert_u8 6 2
    (bitfield_insert_u8 3 3 (and 0b111 op3) (and 0b111 op2))
    op1"

end