theory rBPFCommType
imports
  Main
  "Word_Lib.Signed_Words"
begin

type_synonym u4 = "4 word"
type_synonym u8 = "8 word"
type_synonym i8 = "8 sword"
type_synonym i16 = "16 sword"
type_synonym u16 = "16 word"
type_synonym i32 = "32 sword"
type_synonym u32 = "32 word"
type_synonym i64 = "64 sword"
type_synonym u64 = "64 word"
type_synonym i128 = "128 sword"
type_synonym u128 = "128 word"

type_synonym usize = "64 word" \<comment> \<open> Assume the hardware is 64-bit \<close>

definition i8_MIN :: "i8" where
"i8_MIN = 0x80"

definition i8_MAX :: "i8" where
"i8_MAX = 0x7F"

definition i32_MIN :: "i32" where
"i32_MIN = 0x80000000"

definition i32_MAX :: "i32" where
"i32_MAX = 0x7FFFFFFF"

definition u32_MAX :: "u32" where
"u32_MAX = 0xFFFFFFFF"

definition i64_MIN :: "i64" where
"i64_MIN = 0x8000000000000000"

definition i64_MAX :: "i64" where
"i64_MAX = 0x7FFFFFFFFFFFFFFF"

definition u64_MAX :: "u64" where
"u64_MAX = 0xFFFFFFFFFFFFFFFF"


record ebpf_binary =
bpf_opc :: u8
bpf_dst :: u4
bpf_src :: u4
bpf_off :: i16
bpf_imm :: i32

type_synonym ebpf_bin = "ebpf_binary list"

abbreviation bit_left_shift ::
  "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" (infix "<<" 50)
where "x << n \<equiv> push_bit n x"

abbreviation bit_right_shift ::
  "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" (infix ">>" 50)
  where "x >> n \<equiv> drop_bit n x"

fun unsigned_bitfield_extract_u8 :: "nat \<Rightarrow> nat \<Rightarrow> u8 \<Rightarrow> u8" where
"unsigned_bitfield_extract_u8 pos width n = and ((2 ^ width) - 1) (n >> pos)"

definition bitfield_insert_u8 :: "nat \<Rightarrow> nat \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> u8" where
"bitfield_insert_u8 pos width n p = (
  let mask = ((2 ^ width) - 1) << pos in
    or ((and ((2 ^ width) - 1) p) << pos)
       (and n (not mask))
)"

(* something is wrong
definition unsigned_bitfield_extract_i8 :: "nat \<Rightarrow> nat \<Rightarrow> i8 \<Rightarrow> i8" where
"unsigned_bitfield_extract_i8 pos width n = and ((2 ^ width) - 1) (n >> pos)" *)

(* Test
value "drop_bit 3 0b10101010::u8"
value "0b10101::u8"

value "and ((2 ^ 4) - 1) 0b10101::u8"
value "bitfield_insert_u8 0 3 0x50 12"
value "unsigned_bitfield_extract_u8 3 4 0b10101010"

This one is wrong
value "(scast (unsigned_bitfield_extract_i8 3 4 0b11101010)) :: i16" 



*)

definition u8_of_bool :: "bool \<Rightarrow> u8" where
"u8_of_bool b = (
  case b of
    True \<Rightarrow> 1 |
    False \<Rightarrow> 0
)"

definition u4_of_bool :: "bool \<Rightarrow> u4" where
"u4_of_bool b = (
  case b of
    True \<Rightarrow> 1 |
    False \<Rightarrow> 0
)"

definition u8_list_of_u16 :: "u16 \<Rightarrow> u8 list" where
"u8_list_of_u16 i =
  [ (ucast (and  i       0xff)),
    (ucast (and (i >> 8) 0xff))
  ]"

definition u8_list_of_u32 :: "u32 \<Rightarrow> u8 list" where
"u8_list_of_u32 i =
  [ (ucast (and (i >> 24) 0xff)),
    (ucast (and (i >> 16) 0xff)),
    (ucast (and (i >> 8 ) 0xff)),
    (ucast (and  i        0xff))
  ]"

definition u8_list_of_u64 :: "u64 \<Rightarrow> u8 list" where
"u8_list_of_u64 i =
  [ (ucast (and (i >> 56) 0xff)),
    (ucast (and (i >> 48) 0xff)), 
    (ucast (and (i >> 40) 0xff)),
    (ucast (and (i >> 32) 0xff)),
    (ucast (and (i >> 24) 0xff)),
    (ucast (and (i >> 16) 0xff)),
    (ucast (and (i >> 8 ) 0xff)), 
    (ucast (and  i        0xff))
  ]"

definition u64_of_u8_list :: "u8 list \<Rightarrow> u64 option" where
"u64_of_u8_list l = (
  if length l \<noteq> 8 then
    None
  else
    Some (
      or ((ucast (l!(0))) << 56) (
      or ((ucast (l!(1))) << 48) (
      or ((ucast (l!(2))) << 40) (
      or ((ucast (l!(3))) << 32) (
      or ((ucast (l!(4))) << 24) (
      or ((ucast (l!(5))) << 16) (
      or ((ucast (l!(6))) << 8 ) (
          (ucast (l!(7))))
      )))))))
  )"

definition u32_of_u8_list :: "u8 list \<Rightarrow> u32 option" where
"u32_of_u8_list l = (
  if length l \<noteq> 4 then
    None
  else
    Some (
      or ((ucast (l!(0))) << 24) (
      or ((ucast (l!(1))) << 16) (
      or ((ucast (l!(2))) << 8 ) (
          (ucast (l!(3))))
      )))
  )"

definition u16_of_u8_list :: "u8 list \<Rightarrow> u16 option" where
"u16_of_u8_list l = (
  if length l \<noteq> 2 then
    None
  else
    Some (
      or ((ucast (l!(0))) << 8 ) (
          (ucast (l!(1))
      )))
  )"

(*
fun ua_of_u8_list_aux :: "u8 list \<Rightarrow> ('a :: len word) option" where
"ua_of_u8_list_aux [] = None" |
"ua_of_u8_list_aux [h] = Some(ucast h)"|
"ua_of_u8_list_aux (h#t) = (
  case ua_of_u8_list_aux t of
  None \<Rightarrow> None |
  Some v \<Rightarrow> Some (or (ucast h) (v << 8))
)"

fun ua_of_u8_list_aux2 :: "u8 list \<Rightarrow> ('a :: len word) option" where
"ua_of_u8_list_aux2 [] = None" |
"ua_of_u8_list_aux2 [h] = Some(ucast h)"|
"ua_of_u8_list_aux2 (h#t) = (
  case ua_of_u8_list_aux2 t of
  None \<Rightarrow> None |
  Some v \<Rightarrow> Some (or ((ucast h)<<(length(t))*8) (v))
)"

definition u64_of_u8_list :: "u8 list \<Rightarrow> u64 option" where
"u64_of_u8_list l = (if length l = 8 then ua_of_u8_list_aux (rev l) else None)"

definition u64_of_u8_list2 :: "u8 list \<Rightarrow> u64 option" where
"u64_of_u8_list2 l = (if length l = 8 then ua_of_u8_list_aux2 (l) else None)"

definition u32_of_u8_list :: "u8 list \<Rightarrow> u32 option" where
"u32_of_u8_list l = (if length l = 4 then ua_of_u8_list_aux (rev l) else None)"

definition u32_of_u8_list2 :: "u8 list \<Rightarrow> u32 option" where
"u32_of_u8_list2 l = (if length l = 4 then ua_of_u8_list_aux2 (l) else None)"

definition u16_of_u8_list :: "u8 list \<Rightarrow> u16 option" where
"u16_of_u8_list l = (if length l = 2 then ua_of_u8_list_aux (rev l) else None)"

definition int_of_u8 :: "u8 \<Rightarrow> int" where
"int_of_u8 n = uint n"

definition u8_of_int :: "int \<Rightarrow> u8" where        
"u8_of_int n = of_int n" *)



(*
value "u64_of_u8_list [0x12, 0x35, 0x55, 0x89, 0x64, 0x23, 0x65, 0x44]"
value "u64_of_u8_list2 [0x12, 0x35, 0x55, 0x89, 0x64, 0x23, 0x65, 0x44]"
value "a=ua_of_u8_list_aux  [0x12,0x34]"
value "ua_of_u8_list_aux2 [0x12,0x34]"
*)

lemma [simp]: "u8_of_bool False = 0" by (unfold u8_of_bool_def, simp)

lemma [simp]: "u8_of_bool True = 1" by (unfold u8_of_bool_def, simp)


lemma u8_ge_8_bit_false : "n \<ge> 8 \<Longrightarrow> \<not>bit (v::u8) n"
  apply (rule impossible_bit)
  apply simp
  done

lemma u8_bit_true_ge_8 : "bit (v::u8) n \<Longrightarrow> n < 8"
  by (metis le_neq_implies_less nat_le_linear u8_ge_8_bit_false)

lemma bit_power_k_minus_1_le: "bit (2^k -1::int) n \<longleftrightarrow> n < k"
  apply (simp only: bit_iff_odd)
  by (simp add: even_decr_exp_div_exp_iff' linorder_not_le)

lemma bit_power_k_add_m_ge : "bit (2^(k+m)-2^k::int) n \<Longrightarrow> k \<le> n \<and> n < k+m"
  apply (induction k arbitrary: m n)
  subgoal for m n
    apply simp
    using bit_power_k_minus_1_le by blast

  subgoal for k m n
    apply simp
    apply (cases n)
    subgoal
      apply simp
      by (simp add: bit_0)
    subgoal for n1
      apply simp
      using bit_double_iff diff_Suc_1' by fastforce
    done
  done

lemma bit_power_k_add_m_lt: "n < k+m \<Longrightarrow> \<not> bit (2^(k+m)-2^k::int) n \<Longrightarrow> n < k"
  apply (induction k arbitrary: m n)
  subgoal for m n
    apply simp
    by (simp add: bit_power_k_minus_1_le)

  subgoal for k m n
    apply simp
    apply (cases n)
    subgoal by simp
    subgoal for n1
      apply simp
      by (smt (verit, best) bit_double_Suc_iff possible_bit_def power_eq_0_iff)
    done
  done

end