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

let run_test_case test_case =
  let v = Interp_test.int_of_standard_int test_case.v in
  let fuel = Interp_test.nat_of_int test_case.fuel in
  let res = Interp_test.int_of_standard_int test_case.result_expected in
  let lp = Interp_test.int_list_of_standard_int_list test_case.lp_std in
  let lm = Interp_test.int_list_of_standard_int_list test_case.lm_std in
  let lc = Interp_test.int_list_of_standard_int_list test_case.lc_std in
  let result = Interp_test.bpf_interp_test lp lm lc v fuel res in
  let color = if result then green else red in
  Printf.printf "%s%-25s result: %s%b%s\n" color test_case.dis color result reset


let test_cases = [
  (* //Fatal error: exception Stack_overflow
    ldxdw r0, [r1+2]
    exit*)
  {
    dis = "test_ldxh_same_reg";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 106L; 0L; 0L; 0L; 52L; 18L; 0L; 0L; 105L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0xffL; 0xffL];
    lc_std = [];
    v = 2L;
    fuel = 4L;
    result_expected = 0x1234L;      
  };
]

let () =
  List.iter run_test_case test_cases
