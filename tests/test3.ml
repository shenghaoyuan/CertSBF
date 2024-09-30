open Interp_test2

type test_case = {
  dis : string; 
  lp_std : nat list;
  lm_std : nat list;
  lc_std : nat list;
  v : nat;
  fuel : nat;
  result_expected : nat;
}

let green = "\027[32m"  (* ANSI green *)
let red = "\027[31m"    (* ANSI red *)
let reset = "\027[0m"   (* Reset color *)

let run_test_case test_case =
  let v =  test_case.v in
  let fuel = test_case.fuel in
  let res =  test_case.result_expected in
  let lp =  test_case.lp_std in
  let lm =  test_case.lm_std in
  let lc =  test_case.lc_std in
  let result = Interp_test2.bpf_interp_test lp lm lc v fuel res in
  let color = if result then green else red in
  Printf.printf "%s%-25s result: %s%b%s\n" color test_case.dis color result reset


let test_cases = [
  (* //Fatal error: exception Stack_overflow
    ldxdw r0, [r1+2]
    exit*)
  {
    dis = "test_lldxdw";
    lp_std = [121; 16; 2; 0; 0; 0; 0; 0; 149; 0; 0; 0; 0; 0; 0; 0];
    lm_std = [0xaa; 0xbb; 0x11; 0x22; 0x33; 0x44; 0x55; 0x66; 0x77; 0x88; 0xcc; 0xdd];
    lc_std = [];
    v = 2;
    fuel = 2;
    result_expected = 0x8877665544332211;   
  };
]

let () =
  List.iter run_test_case test_cases
