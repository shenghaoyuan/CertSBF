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

lemma ucast64_ucast8_and_255_eq [simp]: "ucast (((ucast (and v 255))::u8)) = and (v:: u64) 255"
  apply (simp only: ucast_eq)
(**r 
word_of_int (uint (word_of_int (uint (and v 255)))) is

(word_of_int (uint (and v 255)))::u8

word_of_int (uint v_u8)  :: u64

*)
  apply (simp only: uint_word_of_int_eq word_and_def word_of_int_eq_iff)
  apply (simp)
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n
    apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal for n5 apply (cases n5, simp_all)
              subgoal for n6 apply (cases n6, simp_all)
                subgoal for n6 apply (cases n6, simp_all)
                  done
                done
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "n \<ge> 8 \<Longrightarrow> \<not>bit (v::u8) n"
  apply (rule impossible_bit)
  apply simp
  done

lemma [simp]: "n \<le> 56 \<Longrightarrow> ((ucast (v::u8) ::u64) << n) >> n = (ucast (v::u8) ::u64)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for k
    apply (cases k, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal for n5 apply (cases n5, simp_all)
              subgoal for n6 apply (cases n6, simp_all)
                subgoal for n6 apply (cases n6, simp_all)
                  done
                done
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "n+8 \<le> m \<Longrightarrow> ((ucast (v::u8) ::u64) << n) >> m = (0 ::u64)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  done

lemma [simp]: "(n::nat) \<le> 56 \<Longrightarrow> m \<le> n \<Longrightarrow> k < 64 \<Longrightarrow> n - m \<le> k \<Longrightarrow> k + m - n < 8 \<Longrightarrow> m + k < 64"
  by simp

lemma [simp]: "bit (v::u8) n \<Longrightarrow> n < 8"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              subgoal for n6 apply (cases n6, simp_all)
                done
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "n \<le> 56 \<Longrightarrow> m \<le> n \<Longrightarrow> ((ucast (v::u8) ::u64) << n) >> m = ((ucast (v::u8) ::u64) << (n-m))"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for k
    by (simp add: add.commute)
  subgoal for k
    by (metis add.commute)
  done

lemma [simp]: "8 \<le> m \<Longrightarrow> (ucast (v::u8) ::u64) >> m = (0 ::u64)"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  done

lemma [simp]: "8 \<le> n \<Longrightarrow> (and (or ((v::u64) << n) k) 255) = and k 255"
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for t apply (cases t, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal for n5 apply (cases n5, simp_all)
              subgoal for n6 apply (cases n6, simp_all)
                subgoal for n6 apply (cases n6, simp_all)
                  done
                done
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "(ucast (and (ucast (v::u8)) (255::u64)) ::u8) = v"
  apply (simp only: ucast_eq)
  apply (simp only: uint_word_of_int_eq word_and_def word_of_int_eq_iff)
  apply simp
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  subgoal for n apply (cases n, simp_all)
    subgoal for n1 apply (cases n1, simp_all)
      subgoal for n2 apply (cases n2, simp_all)
        subgoal for n3 apply (cases n3, simp_all)
          subgoal for n4 apply (cases n4, simp_all)
            subgoal for n5 apply (cases n5, simp_all)
              subgoal for n6 apply (cases n6, simp_all)
                subgoal for n6 apply (cases n6, simp_all)
                  done
                done
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "length l = 8 \<Longrightarrow> l = [l ! 0, l ! Suc 0, l ! 2, l ! 3, l ! 4, l ! 5, l ! 6, l ! 7]"
  apply (cases l, simp_all)
  subgoal for a0 l apply (cases l, simp_all)
    subgoal for a1 l apply (cases l, simp_all)
      subgoal for a2 l apply (cases l, simp_all)
        subgoal for a3 l apply (cases l, simp_all)
          subgoal for a4 l apply (cases l, simp_all)
            subgoal for a5 l apply (cases l, simp_all)
              subgoal for a6 l apply (cases l, simp_all)
                done
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "bit (255::int) n \<Longrightarrow> n < 8"
  apply (cases n, simp_all)
  subgoal for n1 apply (cases n1, simp_all)
    subgoal for n2 apply (cases n2, simp_all)
      subgoal for n3 apply (cases n3, simp_all)
        subgoal for n4 apply (cases n4, simp_all)
          subgoal for n5 apply (cases n5, simp_all)
            subgoal for n6 apply (cases n6, simp_all)
              subgoal for n6 apply (cases n6, simp_all)
                done
              done
            done
          done
        done
      done
    done
  done

lemma [simp]: "n \<le> 56 \<Longrightarrow> ((ucast ((ucast (and ((v::u64) >> n) 255)) ::u8) ::u64) << n) =
  ((and ((v::u64) >> n) 255) << n)"
  apply (simp only: ucast_eq)
  apply (simp only: uint_word_of_int_eq word_and_def word_of_int_eq_iff)
  apply simp
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  done

lemma bit_power_k_minus_1_le: "bit (2^k -1::int) n \<longleftrightarrow> n < k"
  apply (simp only: bit_iff_odd)
  by (simp add: even_decr_exp_div_exp_iff' linorder_not_le)

lemma bit_power_k_minus_1_le_56 [simp]: "bit (0xffffffffffffff::int) n \<longleftrightarrow> n < 56"
  using bit_power_k_minus_1_le [of 56 n] by simp

lemma [simp]: "(v::u64) =
    or (and ((v >> 56) << 56) 18374686479671623680)
     (or (and ((v >> 48) << 48) 71776119061217280)
       (or (and ((v >> 40) << 40) 280375465082880)
         (or (and ((v >> 32) << 32) 1095216660480) (or (and ((v >> 24) << 24) 4278190080)
            (or (and ((v >> 16) << 16) 16711680) (or (and ((v >> 8) << 8) 65280) (and v 255)))))))"
  apply (simp add: bit_eq_iff)
  apply (simp add: bit_or_iff)

  apply (rule allI)
  subgoal for n
    apply (cases "n \<ge> 56", simp_all)
    subgoal


lemma [simp]: "(Some v = u64_of_u8_list l) = (l = u8_list_of_u64 v)"
  apply (unfold u64_of_u8_list_def u8_list_of_u64_def)
  apply (cases "length l \<noteq> 8", simp_all)
  subgoal by fastforce
  subgoal
    apply (rule iffI)
    subgoal by simp

    subgoal
      apply (simp add: bit_eq_iff)
      apply (simp add: bit_or_iff)


      done
    done
  sorry

(*lemma [simp]: "u8_list_of_u32 v = l \<Longrightarrow> u32_of_u8_list2 l = Some v " 
  apply (unfold u8_list_of_u32_def u32_of_u8_list2_def,simp)
  apply (cases l)
  subgoal by simp
  subgoal for v1 l1
    apply (auto)
    subgoal
      apply(cases l1)
      subgoal by simp
      subgoal for v2 l2
        apply(cases l2)
        subgoal by simp
        subgoal for v3 l3
          apply(cases l3)
          subgoal by simp
          subgoal for v4 l4
            apply (cases l4)
             apply (auto)
            apply(cases v)
            subgoal for n*)

end