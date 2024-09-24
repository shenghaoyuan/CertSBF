section \<open> vm_state \<close>

theory vm_state
imports
  Main
  rBPFCommType rBPFSyntax
begin

(*
context_object_pointer maybe context should be global *)

subsection  \<open> A call frame used for function calls inside the Interpreter \<close>

record CallFrame = (*  /// The caller saved registers
    pub caller_saved_registers: [u64; ebpf::SCRATCH_REGS],
*)
frame_pointer :: u64
target_pc :: u64

type_synonym reg_map = "bpf_ireg \<Rightarrow> u64"

record EbpfVmState =
host_stack_pointer :: u64 (**r  *mut u64 *)
call_depth :: u64
stack_pointer :: u64
previous_instruction_meter:: u64
due_insn_count:: u64
stopwatch_numerator :: u64
stopwatch_denominator:: u64
registers :: reg_map (* [u64; 12] *)
program_result:: "u64 option" (**r ProgramResult \<rightarrow> could be refined to Ok monad type *)
memory_mapping :: "(u64, u64) map" (**r TBC, check mem of phi-system *)
call_frames :: "CallFrame list"
loader :: bpf_bin    

end