
open Interp_test

type test_case = {
  dis : string; 
  lp_std : int64 list;
  lm_std : int64 list;
  lc_std : int64 list;
  v : int64;
  fuel : int64;
  result_expected : int64;
  isok : bool;
}

let green = "\027[32m"  (* ANSI green *)
let red = "\027[31m"    (* ANSI red *)
let reset = "\027[0m"   (* Reset color *)
let n = ref 0

let run_test_case test_case =
  let v = Interp_test.int_of_standard_int test_case.v in
  let fuel = Interp_test.int_of_standard_int test_case.fuel in
  let res = Interp_test.int_of_standard_int test_case.result_expected in
  let lp = Interp_test.int_list_of_standard_int_list test_case.lp_std in
  let lm = Interp_test.int_list_of_standard_int_list test_case.lm_std in
  let lc = Interp_test.int_list_of_standard_int_list test_case.lc_std in
  let result = Interp_test.bpf_interp_test lp lm lc v fuel res test_case.isok  in
  let color = if result then green else red in
  n := !n + 1;
  Printf.printf "%s%d %-40s result: %s%b%s\n" color !n test_case.dis color result reset
  

let test_cases = [
(*

*)
{
  dis = "test_tcp_sack_nomatch";
  lp_std =[183L; 0L; 0L; 0L; 245L; 255L; 255L; 255L; 151L; 0L; 0L; 0L; 10L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
  lm_std = [];
  lc_std = [];
  v = 1L;
  fuel = 3L;
  result_expected = 0x5L;
  isok = true;
};
]

let () =
  List.iter run_test_case test_cases
