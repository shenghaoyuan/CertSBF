section \<open> ebpf \<close>

theory ebpf
imports
  Main
  rBPFCommType rBPFSyntax
begin

text \<open> Number of scratch registers \<close>
definition SCRATCH_REGS :: nat where
"SCRATCH_REGS = 4"

definition INSN_SIZE :: nat where 
"INSN_SIZE = 8"


consts program_vm_addr::u64 

type_synonym func_key = u32

type_synonym func_val = u64

type_synonym func_map = "(func_key, func_val) map"

consts fm::func_map

definition get_function_registry ::"func_key \<Rightarrow> func_val option" where
"get_function_registry key = fm key"

end