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

let rec nat_of_int (n: int64) =
  if n <= 0L then Zero_nat
  else Suc (nat_of_int (Int64.sub n 1L))  

let int_list_of_standard_int_list lst =
  List.map int_of_standard_int lst

let print_regmap rs =
  let reg_list = [("R0", BR0); ("R1", BR1); ("R2", BR2); ("R3", BR3);
                  ("R4", BR4); ("R5", BR5); ("R6", BR6); ("R7", BR7);
                  ("R8", BR8); ("R9", BR9); ("R10", BR10)] in
  List.iter (fun (name, reg) ->
    Printf.printf "%s: %Lx\n" name (myint_to_int (the_int
    (len_bit0
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (rs reg)))
  ) reg_list

let print_bpf_state st =
  match st with
    BPF_OK (pc, rs, m, ss, sv, fm, cur_cu, remain_cu) -> 
    let _ = print_regmap rs in
      Printf.printf "PC: %Lx\n" (myint_to_int (the_int
    (len_bit0
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        pc))
  | BPF_Success _ -> print_endline("success")
  | _ -> print_endline("error")