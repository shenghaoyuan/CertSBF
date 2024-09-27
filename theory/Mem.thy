section \<open> Axiom Memory model \<close>

theory Mem
imports
  Main
  rBPFCommType Val
begin

type_synonym mem = "(u64, u8 option) map"

definition init_mem :: "mem" where
"init_mem = (\<lambda> _. None)"

datatype memory_chunk = M8 | M16 | M32 | M64

type_synonym addr_type = u64

axiomatization
  loadv   :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val option" and
  storev  :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val \<Rightarrow> mem option"

(*
definition load :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val option" where
"load mc m addr = (
  case mc of
  M8 \<Rightarrow> 
)" *)

definition vlong_of_memory_chunk :: "memory_chunk \<Rightarrow> val" where
"vlong_of_memory_chunk chunk = (
  case chunk of
  M8  \<Rightarrow> Vlong 8 |
  M16 \<Rightarrow> Vlong 16 |
  M32 \<Rightarrow> Vlong 32 |
  M64 \<Rightarrow> Vlong 64
)"

end
