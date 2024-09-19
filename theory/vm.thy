section \<open> VM \<close>

theory vm
imports
  Main
  rBPFCommType rBPFSyntax
begin

record Config =
\<comment> \<open> Maximum call depth \<close>
max_call_depth :: usize
\<comment> \<open> Size of a stack frame in bytes,
  must match the size specified in the LLVM BPF backend \<close>
stack_frame_size :: usize
\<comment> \<open> Enables gaps in VM address space between the stack frames \<close>
enable_stack_frame_gaps :: bool
\<comment> \<open> Have the verifier reject "callx r10" \<close>
reject_callx_r10 :: bool
(*
record Config =
\<comment> \<open> Maximum call depth \<close>
max_call_depth :: usizemax_call_depth
\<comment> \<open> Size of a stack frame in bytes,
  must match the size specified in the LLVM BPF backend \<close>
stack_frame_size :: usize
\<comment> \<open> Enables the use of MemoryMapping and MemoryRegion for address translation \<close>
enable_address_translation :: bool
\<comment> \<open> Enables gaps in VM address space between the stack frames \<close>
enable_stack_frame_gaps :: bool
\<comment> \<open> Maximal pc distance after which a new instruction meter validation
  is emitted by the JIT \<close>
instruction_meter_checkpoint_distance :: usize
\<comment> \<open> Enable instruction meter and limiting \<close>
enable_instruction_meter :: bool
\<comment> \<open> Enable instruction tracing \<close>
enable_instruction_tracing :: bool
\<comment> \<open> Enable dynamic string allocation for labels \<close>
enable_symbol_and_section_labels :: bool
\<comment> \<open> Reject ELF files containing issues that the verifier 
did not catch before (up to v0.2.21) \<close>
reject_broken_elfs :: bool
\<comment> \<open> Ratio of native host instructions per random no-op in JIT (0 = OFF) \<close>
noop_instruction_rate :: u32
\<comment> \<open> Enable disinfection of immediate values and offsets 
provided by the user in JIT \<close>
sanitize_user_provided_values :: bool
\<comment> \<open> Throw ElfError::SymbolHashCollision when 
a BPF function collides with a registered syscall \<close>
external_internal_function_hash_collision :: bool

\<comment> \<open> Avoid copying read only sections when possible \<close>
optimize_rodata :: bool
\<comment> \<open> Use the new ELF parser \<close>
new_elf_parser :: bool
\<comment> \<open> Use aligned memory mapping \<close>
aligned_memory_mapping :: bool
\<comment> \<open> Allow ExecutableCapability::V1 \<close>
enable_sbpf_v1 :: bool
\<comment> \<open> Allow ExecutableCapability::V2 \<close>
enable_sbpf_v2 :: bool
*)

text \<open> TBC \<close>



end