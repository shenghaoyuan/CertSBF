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

let parse_test_case json =
  let dis = json |> member "dis" |> to_string in
  let lp_std = json |> member "lp_std" |> to_list |> List.map to_string in
  let lr_std = json |> member "lr_std" |> to_list |> List.map to_string in
  let lm_std = json |> member "lm_std" |> to_list |> List.map to_string in
  let lc_std = json |> member "lc_std" |> to_list |> List.map to_string in
  let v = json |> member "v" |> to_string in
  let fuel = json |> member "fuel" |> to_string in
  let index = json |> member "index" |> to_string in
  let ipc = json |> member "ipc" |> to_string in
  let result_expected = json |> member "result_expected" |> to_string in

  let parse_int64 s = Int64.of_string s in

  let lp_std = List.map parse_int64 lp_std in
  let lr_std = List.map parse_int64 lr_std in
  let lm_std = List.map parse_int64 lm_std in
  let lc_std = List.map parse_int64 lc_std in
  let v = parse_int64 v in
  let fuel = parse_int64 fuel in
  let index = parse_int64 index in
  let ipc = parse_int64 ipc in
  let result_expected = parse_int64 result_expected in

  { dis; lp_std; lr_std; lm_std; lc_std; v; fuel; ipc; index; result_expected }

let read_test_cases filename =
  let json = Yojson.Basic.from_file filename in
  match json with
  | `List test_cases_json -> List.map parse_test_case test_cases_json
  | _ -> failwith "Expected a list of test cases"

let () =
  let test_cases = read_test_cases "../data/ocaml_in.json" in
  List.iter run_test_case test_cases;
  Printf.printf "\nSummary:\n";
  Printf.printf "%sPassed: %d%s\n" green !passed reset;
  Printf.printf "%sFailed: %d%s\n" red !failed reset
