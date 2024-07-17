section \<open> CompCert Value Type \<close>

theory Val
imports
  Main
  rBPFCommType
begin

definition sub_overflowi32 :: "u32 \<Rightarrow> u32 \<Rightarrow> u32 \<Rightarrow> u32" where
"sub_overflowi32 x y bin = (
  let s = (scast x) - (scast y) - (scast bin) in
    if i32_MIN \<le>s s \<and> s \<le>s i32_MAX then 0 else 1
)"

definition sub_overflowi64 :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64" where
"sub_overflowi64 x y bin = (
  let s = (scast x) - (scast y) - (scast bin) in
    if i64_MIN \<le>s s \<and> s \<le>s i64_MAX then 0 else 1
)"


datatype val = Vundef | Vint u32 | Vlong u64

subsection \<open> 32-bit Arithmetic operations \<close>

definition neg :: "val \<Rightarrow> val" where
"neg v = (
  case v of
  Vint n \<Rightarrow> Vint (- n) |
  _ => Vundef
)"

definition maketotal :: "val option \<Rightarrow> val" where
"maketotal ov = (case ov of Some v \<Rightarrow> v | None \<Rightarrow> Vundef)"

definition add :: "val \<Rightarrow> val \<Rightarrow> val" where
"add v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (n1 + n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition sub :: "val \<Rightarrow> val \<Rightarrow> val" where
"sub v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (n1 - n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition mul :: "val \<Rightarrow> val \<Rightarrow> val" where
"mul v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (n1 * n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition sub_overflow :: "val \<Rightarrow> val \<Rightarrow> val" where
"sub_overflow v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (sub_overflowi32 n1 n2 0) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition negative :: "val \<Rightarrow> val" where
"negative v = (
  case v of
  Vint n \<Rightarrow> Vint (if (scast n) <s (0::i32) then 1 else 0 ) |
  _ \<Rightarrow> Vundef
)"

definition or :: "val \<Rightarrow> val \<Rightarrow> val" where
"or v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (Bit_Operations.or n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition andd :: "val \<Rightarrow> val \<Rightarrow> val" where
"andd v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (Bit_Operations.and n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"


subsection \<open> 64-bit Arithmetic operations \<close>

definition negl :: "val \<Rightarrow> val" where
"negl v = (
  case v of
  Vlong n \<Rightarrow> Vlong (- n) |
  _ => Vundef
)"

definition addl :: "val \<Rightarrow> val \<Rightarrow> val" where
"addl v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (n1 + n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition subl :: "val \<Rightarrow> val \<Rightarrow> val" where
"subl v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (n1 - n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition mull :: "val \<Rightarrow> val \<Rightarrow> val" where
"mull v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (n1 * n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition subl_overflow :: "val \<Rightarrow> val \<Rightarrow> val" where
"subl_overflow v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vint (ucast (sub_overflowi64 n1 n2 0)) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition negativel :: "val \<Rightarrow> val" where
"negativel v = (
  case v of
  Vlong n \<Rightarrow> Vlong (if (scast n) <s (0::i64) then 1 else 0 ) |
  _ \<Rightarrow> Vundef
)"

definition orl :: "val \<Rightarrow> val \<Rightarrow> val" where
"orl v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (Bit_Operations.or n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition andl :: "val \<Rightarrow> val \<Rightarrow> val" where
"andl v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (Bit_Operations.and n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

subsection \<open> Comparisons \<close>

datatype comparison =
    Ceq (* same *)
  | Cne (* different *)
  | Clt (* less than *)
  | Cle (* less than or equal *)
  | Cgt (* greater than *)
  | Cge (* greater than or equal *)


definition cmpi32 :: "comparison \<Rightarrow> i32 \<Rightarrow> i32 \<Rightarrow> bool" where
"cmpi32 c x y = (
  case c of
  Ceq \<Rightarrow> x = y |
  Cne \<Rightarrow> x \<noteq> y |
  Clt \<Rightarrow> x <s y |
  Cle \<Rightarrow> x \<le>s y |
  Cgt \<Rightarrow> y <s x |
  Cge \<Rightarrow> y \<le>s x
)"

definition cmpu32 :: "comparison \<Rightarrow> u32 \<Rightarrow> u32 \<Rightarrow> bool" where
"cmpu32 c x y = (
  case c of
  Ceq \<Rightarrow> x = y |
  Cne \<Rightarrow> x \<noteq> y |
  Clt \<Rightarrow> x < y |
  Cle \<Rightarrow> x \<le> y |
  Cgt \<Rightarrow> y < x |
  Cge \<Rightarrow> y \<le> x
)"


definition cmpi64 :: "comparison \<Rightarrow> i64 \<Rightarrow> i64 \<Rightarrow> bool" where
"cmpi64 c x y = (
  case c of
  Ceq \<Rightarrow> x = y |
  Cne \<Rightarrow> x \<noteq> y |
  Clt \<Rightarrow> x <s y |
  Cle \<Rightarrow> x \<le>s y |
  Cgt \<Rightarrow> y <s x |
  Cge \<Rightarrow> y \<le>s x
)"

definition cmpu64 :: "comparison \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> bool" where
"cmpu64 c x y = (
  case c of
  Ceq \<Rightarrow> x = y |
  Cne \<Rightarrow> x \<noteq> y |
  Clt \<Rightarrow> x < y |
  Cle \<Rightarrow> x \<le> y |
  Cgt \<Rightarrow> y < x |
  Cge \<Rightarrow> y \<le> x
)"

definition cmp_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool option" where
"cmp_bool c v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Some (cmpi32 c (scast n1) (scast n2)) | _ \<Rightarrow> None) |
  _ \<Rightarrow> None
)"

definition cmpu_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool option" where
"cmpu_bool c v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Some (cmpu32 c n1 n2) | _ \<Rightarrow> None) |
  _ \<Rightarrow> None
)"

definition cmpl_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool option" where
"cmpl_bool c v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Some (cmpi64 c (scast n1) (scast n2)) | _ \<Rightarrow> None) |
  _ \<Rightarrow> None
)"

definition cmplu_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool option" where
"cmplu_bool c v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Some (cmpu64 c n1 n2) | _ \<Rightarrow> None) |
  _ \<Rightarrow> None
)"

definition of_optbool :: " bool option \<Rightarrow> val" where
"of_optbool ob = (case ob of None \<Rightarrow> Vundef | Some True \<Rightarrow> Vint 1 | Some False \<Rightarrow> Vint 0)"

definition cmp :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
"cmp c v1 v2 = of_optbool (cmp_bool c v1 v2)"

definition cmpu :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
"cmpu c v1 v2 = of_optbool (cmpu_bool c v1 v2)"

definition cmpl :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
"cmpl c v1 v2 = of_optbool (cmpl_bool c v1 v2)"

definition cmplu :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
"cmplu c v1 v2 = of_optbool (cmplu_bool c v1 v2)"

end