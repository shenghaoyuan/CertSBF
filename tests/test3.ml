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
  let fuel = Interp_test.int_of_standard_int test_case.fuel in
  let res = Interp_test.int_of_standard_int test_case.result_expected in
  let lp = Interp_test.int_list_of_standard_int_list test_case.lp_std in
  let lm = Interp_test.int_list_of_standard_int_list test_case.lm_std in
  let lc = Interp_test.int_list_of_standard_int_list test_case.lc_std in
  let result = Interp_test.bpf_interp_test lp lm lc v fuel res in
  let color = if result then green else red in
  Printf.printf "%s%-25s result: %s%b%s\n" color test_case.dis color result reset


let test_cases = [
(*  
    add r11, -8
    call function_foo
    exit
    function_foo:
    mov r0, r10
    exit
    //ProgramResult::Ok(ebpf::MM_STACK_START + config.stack_size() as u64 - 8),
*)
  {
    dis = "test_dynamic_frame_ptr";
    lp_std = [7L; 11L; 0L; 0L; 248L; 255L; 255L; 255L; 133L; 16L; 0L; 0L; 3L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 160L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    v = 2L;
    fuel = 5L;
    result_expected = 8590196728L;
  };
]

let () =
  List.iter run_test_case test_cases
