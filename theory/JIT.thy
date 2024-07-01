section \<open> x86_64 Just-In-Time Compiler of Solana rBPF \<close>

theory JIT
imports
  Main
  rBPFCommType rBPFSyntax
begin

text \<open> TBC \<close>


subsection  \<open> JIT State \<close>
text \<open> the state is a record including
- a list of rBPF instructions (maybe as global varaible of `step`)
- registers
- memory_model
- VM configuration
- ... \<close>

subsection  \<open> ALU \<close>
subsection  \<open> JUMP \<close>
subsection  \<open> MEM \<close>
subsection  \<open> CALL \<close>
subsection  \<open> EXIT \<close>
subsection  \<open> JIT_One \<close>



end