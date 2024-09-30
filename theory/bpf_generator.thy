theory bpf_generator
  imports Main Interpreter rBPFSyntax vm_state rBPFCommType

begin


export_code  eval_reg  in OCaml
  module_name Test file_prefix test

(*
code_printing type_constructor nat \<rightharpoonup> (OCaml) "nat"
  | constant Nat.Zero_Rep  \<rightharpoonup> (OCaml) "Zero"
  | constant Suc  \<rightharpoonup> (OCaml) "Succ" *)

export_code bpf_interp_test in OCaml
  module_name Interp_test2 file_prefix interp_test2

(*export_code eval_alu32 in OCaml
  module_name Alu32 file_prefix alu32

export_code eval_neg32 in OCaml
  module_name Neg32 file_prefix neg32

export_code eval_neg64 in OCaml
  module_name Neg64 file_prefix neg64*)

end