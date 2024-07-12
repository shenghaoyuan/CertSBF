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

abbreviation bit_left_shift ::
  "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" (infix "<<" 50)
where "x << n \<equiv> push_bit n x"

abbreviation bit_right_shift ::
  "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" (infix ">>" 50)
where "x >> n \<equiv> drop_bit n x"

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
    program_vm_BPF_ADDr: u64, *)
jit_config  :: Config
jit_pc :: usize (*
    last_instruction_meter_validation_pc: usize,
    next_noop_insertion: u32,
    runtime_environment_key: i32,
    diversification_rng: SmallRng,
    stopwatch_is_active: bool, *)

definition jit_emit :: "JitCompiler \<Rightarrow> u8 list  \<Rightarrow> JitCompiler" where
"jit_emit l n =
 \<lparr>
  jit_result = (jit_result l)\<lparr> text_section := (text_section (jit_result l))@n \<rparr>,
  offset_in_text_section = (offset_in_text_section l) + length n,
  jit_config = jit_config l,
  jit_pc = jit_pc l
 \<rparr>"



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

text \<open> 
pub(crate) fn emit_variable_length(&mut self, size: OperandSize, data: u64) {
        match size {
            OperandSize::S0 => {},
            OperandSize::S8 => self.emit::<u8>(data as u8),
            OperandSize::S16 => self.emit::<u16>(data as u16),
            OperandSize::S32 => self.emit::<u32>(data as u32),
            OperandSize::S64 => self.emit::<u64>(data),
        }
    }
 \<close>

end