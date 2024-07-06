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

end