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
  (*
    mov r0, r1
    ldxb r9, [r0+0]
    lsh r9, 0
    ldxb r8, [r0+1]
    lsh r8, 4
    ldxb r7, [r0+2]
    lsh r7, 8
    ldxb r6, [r0+3]
    lsh r6, 12
    ldxb r5, [r0+4]
    lsh r5, 16
    ldxb r4, [r0+5]
    lsh r4, 20
    ldxb r3, [r0+6]
    lsh r3, 24
    ldxb r2, [r0+7]
    lsh r2, 28
    ldxb r1, [r0+8]
    lsh r1, 32
    ldxb r0, [r0+9]
    lsh r0, 36
    or r0, r1
    or r0, r2
    or r0, r3
    or r0, r4
    or r0, r5
    or r0, r6
    or r0, r7
    or r0, r8
    or r0, r9
    exit*)
  {
    dis = "test_ldxb_all";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 113L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 103L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 113L; 8L; 1L; 0L; 0L; 0L; 0L; 0L; 103L; 8L; 0L; 0L; 4L; 0L; 0L; 0L; 113L; 7L; 2L; 0L; 0L; 0L; 0L; 0L; 103L; 7L; 0L; 0L; 8L; 0L; 0L; 0L; 113L; 6L; 3L; 0L; 0L; 0L; 0L; 0L; 103L; 6L; 0L; 0L; 12L; 0L; 0L; 0L; 113L; 5L; 4L; 0L; 0L; 0L; 0L; 0L; 103L; 5L; 0L; 0L; 16L; 0L; 0L; 0L; 113L; 4L; 5L; 0L; 0L; 0L; 0L; 0L; 103L; 4L; 0L; 0L; 20L; 0L; 0L; 0L; 113L; 3L; 6L; 0L; 0L; 0L; 0L; 0L; 103L; 3L; 0L; 0L; 24L; 0L; 0L; 0L; 113L; 2L; 7L; 0L; 0L; 0L; 0L; 0L; 103L; 2L; 0L; 0L; 28L; 0L; 0L; 0L; 113L; 1L; 8L; 0L; 0L; 0L; 0L; 0L; 103L; 1L; 0L; 0L; 32L; 0L; 0L; 0L; 113L; 0L; 9L; 0L; 0L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 36L; 0L; 0L; 0L; 79L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 80L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 96L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x01L; 0x02L; 0x03L; 0x04L; 0x05L; 0x06L; 0x07L; 0x08L; 0x09L];
    lc_std = [];
    v = 2L;
    fuel = 31L;
    result_expected = 0x9876543210L;   
  };
]

let () =
  List.iter run_test_case test_cases
