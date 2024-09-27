theory Interpreter_Code_Gen
imports
  Main
  rBPFCommType rBPFSyntax vm_state vm Mem
  ebpf rBPFDecoder Interpreter
begin

definition init_rs :: "reg_map" where
"init_rs r = 0"

definition test_eval_reg :: "u64" where
"test_eval_reg = eval_reg BR0 init_rs"

definition test_prog :: "int list \<Rightarrow> int" where
"test_prog l = 1"

code_printing
  type_constructor nat \<rightharpoonup> (OCaml) "nat"
code_printing
  type_constructor int \<rightharpoonup> (OCaml) "int"

declare [[code abort: storev loadv]]
(*
export_code eval_reg in OCaml
  module_name Test_eval_reg file \<open>test_eval_reg.ml\<close>
*)

end