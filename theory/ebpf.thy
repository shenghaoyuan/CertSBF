section \<open> ebpf \<close>

theory ebpf
imports
  Main
  rBPFCommType rBPFSyntax
begin

text \<open> Number of scratch registers \<close>
definition SCRATCH_REGS :: nat where
"SCRATCH_REGS = 4"

end