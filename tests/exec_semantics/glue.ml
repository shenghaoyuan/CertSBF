(**ocaml glue code just for CLoC *)

let rec num_to_int (n: num) : int64 =
  match n with
  | One -> 1L
  | Bit0 m -> Int64.mul 2L (num_to_int m)
  | Bit1 m -> Int64.add (Int64.mul 2L (num_to_int m)) 1L     

let myint_to_int (mi: myint) : int64 =
  match mi with
  | Zero_int -> 0L
  | Pos n -> num_to_int n
  | Neg n -> Int64.neg (num_to_int n)

let rec num_of_int (n: int64) =
  if n = 1L then One
  else if Int64.rem n 2L = 0L then Bit0 (num_of_int (Int64.div n 2L))
  else Bit1 (num_of_int (Int64.div n 2L))


let int_of_standard_int (n: int64) =
  if n = 0L then Zero_int
  else if n > 0L then  Pos (num_of_int (n))
  else Neg (num_of_int (Int64.sub 0L n))

let int_list_of_standard_int_list lst =
  List.map int_of_standard_int lst


open Interp_test

type test_case = {
  dis : string; 
  lp_std : int64 list;
  lm_std : int64 list;
  lc_std : int64 list;
  v : int64;
  fuel : int64;
  result_expected : int64;
}

let green = "\027[32m"  (* ANSI green *)
let red = "\027[31m"    (* ANSI red *)
let reset = "\027[0m"   (* Reset color *)
let n = ref 0
let passed = ref 0
let failed = ref 0

let run_test_case test_case =
  let v = Interp_test.int_of_standard_int test_case.v in
  let fuel = Interp_test.int_of_standard_int test_case.fuel in
  let res = Interp_test.int_of_standard_int test_case.result_expected in
  let lp = Interp_test.int_list_of_standard_int_list test_case.lp_std in
  let lm = Interp_test.int_list_of_standard_int_list test_case.lm_std in
  let lc = Interp_test.int_list_of_standard_int_list test_case.lc_std in
  let result = Interp_test.bpf_interp_test lp lm lc v fuel res in
  let color = if result then green else red in
  n := !n + 1;
  if result then (
    passed := !passed + 1;
  ) else (
    failed := !failed + 1;
  );
  Printf.printf "%s%d %-40s result: %s%b%s\n" color !n test_case.dis color result reset  

  
let () =
  List.iter run_test_case test_cases;
  Printf.printf "\nSummary:\n";
  Printf.printf "%sPassed: %d%s\n" green !passed reset;
  Printf.printf "%sFailed: %d%s\n" red !failed reset

open Step_test
open Yojson.Basic.Util

type test_case = {
  dis : string; 
  lp_std : int64 list;
  lr_std : int64 list;
  lm_std : int64 list;
  lc_std : int64 list;
  v : int64;
  fuel : int64;
  ipc : int64;
  index : int64;
  result_expected : int64;
}

let green = "\027[32m"  (* ANSI green *)
let red = "\027[31m"    (* ANSI red *)
let reset = "\027[0m"   (* Reset color *)
let n = ref 0
let passed = ref 0
let failed = ref 0

let run_test_case test_case =
  let v = Step_test.int_of_standard_int test_case.v in
  let fuel = Step_test.int_of_standard_int test_case.fuel in
  let index = Step_test.int_of_standard_int test_case.index in
  let ipc = Step_test.int_of_standard_int test_case.ipc in
  let res = Step_test.int_of_standard_int test_case.result_expected in
  let lp = Step_test.int_list_of_standard_int_list test_case.lp_std in
  let lr = Step_test.int_list_of_standard_int_list test_case.lr_std in
  let lm = Step_test.int_list_of_standard_int_list test_case.lm_std in
  let lc = Step_test.int_list_of_standard_int_list test_case.lc_std in
  let result = Step_test.step_test lp lr lm lc v fuel ipc index res in
  let color = if result then green else red in
  if result then (
    passed := !passed + 1;
  ) else (
    failed := !failed + 1;
  );
  n := !n + 1;
  Printf.printf "%s%d %-40s result: %s%b%s\n" color !n test_case.dis color result reset