section \<open> Axiom Memory model \<close>

theory Mem
imports
  Main
  rBPFCommType Val
begin

type_synonym mem = "(u64, u8 option) map"

datatype memory_chunk = M8 | M16 | M32 | M64

type_synonym addr_type = val

axiomatization
  loadv   :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val option" and
  storev  :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val \<Rightarrow> mem option"


end