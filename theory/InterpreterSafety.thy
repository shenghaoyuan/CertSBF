section \<open> The Safety proof of the Interpreter in Solana rBPF \<close>

theory InterpreterSafety
imports
  Main
  rBPFCommType rBPFSyntax vm_state vm Mem
  ebpf rBPFDecoder
  verifier Interpreter
begin
  
lemma interpreter_safe: "verifier l sv fm cb = True \<Longrightarrow>
  bpf_interp fuel l (BPF_OK pc rs m ss sv fm cur_cu remain_cu) eb \<noteq> BPF_Err"


end