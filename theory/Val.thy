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


datatype val = Vundef | Vbyte u8 | Vshort | Vint u32 | Vlong u64

subsection \<open> 32-bit Arithmetic operations \<close>

definition neg32 :: "val \<Rightarrow> val" where
"neg32 v = (
  case v of
  Vint n \<Rightarrow> Vint (- n) |
  _ => Vundef
)"

definition maketotal :: "val option \<Rightarrow> val" where
"maketotal ov = (case ov of Some v \<Rightarrow> v | None \<Rightarrow> Vundef)"

definition add32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"add32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (n1 + n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition sub32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"sub32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (n1 - n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition mul32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"mul32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (n1 * n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition mulhu32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"mulhu32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint ((n1 * n2) div (2 ^ 32) ) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition mulhs32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"mulhs32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> 
              Vint ( ((scast n1) * (scast n2)) div (2 ^ 32) )  | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition divu32 :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (val \<times> val) option" where
"divu32 v1 v2 v3 = (
  case v1 of 
    Vint nh \<Rightarrow> (case v2 of 
      Vint nl \<Rightarrow> (case v3 of 
        Vint d \<Rightarrow> Some (Vint 1, Vint 1)
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)
  | _ \<Rightarrow> None
)"


definition sub_overflow32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"sub_overflow32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (sub_overflowi32 n1 n2 0) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition negative32 :: "val \<Rightarrow> val" where
"negative32 v = (
  case v of
  Vint n \<Rightarrow> Vint (if (scast n) <s (0::i32) then 1 else 0 ) |
  _ \<Rightarrow> Vundef
)"

definition or32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"or32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (Bit_Operations.or n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition and32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"and32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (Bit_Operations.and n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition shl32 :: "val \<Rightarrow> u8 \<Rightarrow> val" where
"shl32 v n = (
  case v of
  Vint i  \<Rightarrow> Vint (i << (unsigned n)) |
  _ \<Rightarrow> Vundef
)"

definition shlr32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"shlr32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vbyte n2 \<Rightarrow> Vint (n1 >> (unsigned n2)) | _ \<Rightarrow> Vundef) | \<comment> \<open>`v2 = RCX - CL::u8`\<close>
  _ \<Rightarrow> Vundef
)"

definition shr32 :: "val \<Rightarrow> u8 \<Rightarrow> val" where
"shr32 v n = (
  case v of
  Vint i  \<Rightarrow> Vint (i >> (unsigned n)) |
  _ \<Rightarrow> Vundef
)"

definition shrr32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"shrr32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vbyte n2 \<Rightarrow> Vint (n1 >> (unsigned n2)) | _ \<Rightarrow> Vundef) | \<comment> \<open>`v2 = RCX - CL::u8`\<close>
  _ \<Rightarrow> Vundef
)"

definition sar32 :: "val \<Rightarrow> u8 \<Rightarrow> val" where
"sar32 v n = (
  case v of
  Vint i  \<Rightarrow> Vint (ucast (((scast i)::i32) >> (unsigned n))) |
  _ \<Rightarrow> Vundef
)"

definition sarr32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"sarr32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vbyte n2 \<Rightarrow> Vint (ucast (((scast n1)::i64) >> (unsigned n2))) | _ \<Rightarrow> Vundef) | \<comment>\<open>`v2 = RCX - CL::u8`\<close>
  _ \<Rightarrow> Vundef
)"


subsection \<open> 64-bit Arithmetic operations \<close>

definition neg64 :: "val \<Rightarrow> val" where
"neg64 v = (
  case v of
  Vlong n \<Rightarrow> Vlong (- n) |
  _ => Vundef
)"

definition add64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"add64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (n1 + n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition sub64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"sub64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (n1 - n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition mul64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"mul64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (n1 * n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition mullhu64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"mullhu64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong ((n1 * n2) div (2 ^ 64) ) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition mullhs64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"mullhs64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> 
                Vlong (((scast n1) * (scast n2)) div (2 ^ 64) ) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition sub_overflow64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"sub_overflow64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vint (ucast (sub_overflowi64 n1 n2 0)) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition negative64 :: "val \<Rightarrow> val" where
"negative64 v = (
  case v of
  Vlong n \<Rightarrow> Vlong (if (scast n) <s (0::i64) then 1 else 0 ) |
  _ \<Rightarrow> Vundef
)"

definition or64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"or64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (Bit_Operations.or n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition and64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"and64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (Bit_Operations.and n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition shl64 :: "val \<Rightarrow> u8 \<Rightarrow> val" where
"shl64 v n = (
  case v of
  Vlong i  \<Rightarrow> Vlong (i << (unsigned n)) |
  _ \<Rightarrow> Vundef
)"

definition shllr64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"shllr64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vbyte n2 \<Rightarrow> Vlong (n1 << (unsigned n2)) | _ \<Rightarrow> Vundef) | \<comment> \<open>`v2 = RCX - CL`\<close>
  _ \<Rightarrow> Vundef
)"

definition shr64 :: "val \<Rightarrow> u8 \<Rightarrow> val" where
"shr64 v n = (
  case v of
  Vlong i  \<Rightarrow> Vlong (i >> (unsigned n)) |
  _ \<Rightarrow> Vundef
)"

definition shrlr64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"shrlr64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vbyte n2 \<Rightarrow> Vlong (n1 >> (unsigned n2)) | _ \<Rightarrow> Vundef) | \<comment> \<open>`v2 = RCX - CL`\<close>
  _ \<Rightarrow> Vundef
)"

definition sar64 :: "val \<Rightarrow> u8 \<Rightarrow> val" where
"sar64 v n = (
  case v of
  Vlong i  \<Rightarrow> Vlong (ucast (((scast i)::i64) >> (unsigned n))) |
  _ \<Rightarrow> Vundef
)"

definition sarlr64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"sarlr64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vbyte n2 \<Rightarrow> Vlong (ucast (((scast n1)::i64) >> (unsigned n2))) | _ \<Rightarrow> Vundef) | \<comment>\<open>`v2 = RCX - CL`\<close>
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