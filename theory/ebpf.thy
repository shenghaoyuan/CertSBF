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

end