section \<open> A collection of common type of JIT \<close>

theory JITCommType
imports
  Main
  rBPFCommType rBPFSyntax
  vm x86CommType
begin

text \<open> RDI: Used together with slot_in_vm() \<close>
abbreviation "REGISTER_PTR_TO_VM:: u8 \<equiv> ARGUMENT_REGISTERS ! 0"
text \<open> RBX: Program counter limit \<close>
abbreviation "REGISTER_INSTRUCTION_METER:: u8 \<equiv> CALLEE_SAVED_REGISTERS ! 1"
text \<open> R10: Other scratch register \<close>
abbreviation "REGISTER_OTHER_SCRATCH:: u8 \<equiv> CALLER_SAVED_REGISTERS ! 7"
text \<open> R11: Scratch register \<close>
abbreviation "REGISTER_SCRATCH :: u8 \<equiv> CALLER_SAVED_REGISTERS ! 8"


definition u8_of_bool :: "bool \<Rightarrow> u8" where
"u8_of_bool b = (
  case b of
    True \<Rightarrow> 1 |
    False \<Rightarrow> 0
)"

definition u8_list_of_u16 :: "u16 \<Rightarrow> u8 list" where
"u8_list_of_u16 i =
  [ (ucast (and i 0xff)),
    (ucast (i >> 8))
  ]"

definition u8_list_of_u32 :: "u32 \<Rightarrow> u8 list" where
"u8_list_of_u32 i =
  [ (ucast (and i 0xff)),
    (ucast (i >> 8)),
    (ucast (i >> 16)),
    (ucast (i >> 24))
  ]"

definition u8_list_of_u64 :: "u64 \<Rightarrow> u8 list" where
"u8_list_of_u64 i =
  [ (ucast (and i 0xff)),
    (ucast (i >> 8)),
    (ucast (i >> 16)),
    (ucast (i >> 24)),
    (ucast (i >> 32)),
    (ucast (i >> 40)),
    (ucast (i >> 48)),
    (ucast (i >> 56))
  ]"

datatype OperandSize = S0 | S8 | S16 | S32 | S64

datatype RuntimeEnvironmentSlot =
  HostStackPointer |
  CallDepth |
  StackPointer |
  ContextObjectPointer |
  PreviousInstructionMeter |
  DueInsnCount |
  StopwatchNumerator |
  StopwatchDenominator |
  Registers |
  ProgramResult |
  MemoryMapping

definition i32_of_RuntimeEnvironmentSlot :: "RuntimeEnvironmentSlot \<Rightarrow> i32" where
"i32_of_RuntimeEnvironmentSlot slot = (
  case slot of
  HostStackPointer          \<Rightarrow> 0 |
  CallDepth                 \<Rightarrow> 1 |
  StackPointer              \<Rightarrow> 2 |
  ContextObjectPointer      \<Rightarrow> 3 |
  PreviousInstructionMeter  \<Rightarrow> 4 |
  DueInsnCount              \<Rightarrow> 5 |
  StopwatchNumerator        \<Rightarrow> 6 |
  StopwatchDenominator      \<Rightarrow> 7 |
  Registers                 \<Rightarrow> 8 |
  ProgramResult             \<Rightarrow> 20 |
  MemoryMapping             \<Rightarrow> 28
)"

record JitProgram =
page_size     :: usize
pc_section    :: "usize list"
text_section  :: "u8 list"

record JitCompiler =
jit_result :: JitProgram (*
text_section_jumps: Vec<Jump>,
    anchors: [*const u8; ANCHOR_COUNT], *)
offset_in_text_section :: nat \<comment> \<open> usize is refined to nat \<close>
(*
    executable: &'a Executable<C>,
    program: &'a [u8],
    program_vm_addr: u64, *)
jit_config  :: Config
jit_pc :: usize (*
    last_instruction_meter_validation_pc: usize,
    next_noop_insertion: u32, *)
runtime_environment_key :: i32 (*
    diversification_rng: SmallRng,
    stopwatch_is_active: bool, *)

definition jit_emit :: "JitCompiler \<Rightarrow> u8 list  \<Rightarrow> JitCompiler" where
"jit_emit l n = l
 \<lparr>
  jit_result              := (jit_result l)\<lparr> text_section := (text_section (jit_result l))@n \<rparr>,
  offset_in_text_section  := (offset_in_text_section l) + length n
 \<rparr>"

definition slot_in_vm :: "JitCompiler \<Rightarrow> RuntimeEnvironmentSlot \<Rightarrow> i32" where
"slot_in_vm l slot =
  8 * ((i32_of_RuntimeEnvironmentSlot slot) - (runtime_environment_key l))"

definition jit_emit_variable_length ::
  "JitCompiler \<Rightarrow> OperandSize \<Rightarrow> u64  \<Rightarrow> JitCompiler" where
"jit_emit_variable_length l sz data = (
  case sz of
  S0 \<Rightarrow> l |
  S8 \<Rightarrow> jit_emit l [(ucast (and data 0xff))] |
  S16 \<Rightarrow> jit_emit l (u8_list_of_u16 (ucast data)) |
  S32 \<Rightarrow> jit_emit l (u8_list_of_u32 (ucast data)) |
  S64 \<Rightarrow> jit_emit l (u8_list_of_u64 (ucast data))
)"

end