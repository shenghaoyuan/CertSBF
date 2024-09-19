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


datatype val = Vundef | Vbyte u8 | Vshort u16 | Vint u32 | Vlong u64

subsection \<open> 16-bit Arithmetic operations \<close>

definition rol16 :: "val \<Rightarrow> val \<Rightarrow> val" where \<comment> \<open> bswap 16 \<close>
"rol16 v n = (
  case v of                     
  Vshort v1 \<Rightarrow> (case n of Vbyte n1 \<Rightarrow>
    let n1 = n1 mod 16 in
    Vshort (Bit_Operations.or (v1 << (unat n1)) (v1 >> (unat (16 - n1))))
  | _ \<Rightarrow> Vundef)                                               
 |  _ \<Rightarrow> Vundef
)"

definition add16 :: "val \<Rightarrow> val \<Rightarrow> val" where
"add16 v1 v2 = (
  case v1 of
    Vshort n1 \<Rightarrow> (case v2 of Vshort n2 \<Rightarrow> Vshort (n1 + n2) | _ \<Rightarrow> Vundef) |
    _ \<Rightarrow> Vundef
)"

subsection \<open> 32-bit Arithmetic operations \<close>


definition longofintu :: "val \<Rightarrow> val" where
"longofintu v = (
  case v of
    Vint i \<Rightarrow> Vlong (ucast i) |
    _ \<Rightarrow> Vundef
)"

definition longofints :: "val \<Rightarrow> val" where
"longofints v = (
  case v of
    Vint i \<Rightarrow> Vlong (scast i) |
    _ \<Rightarrow> Vundef
)"

definition intoflongl:: "val \<Rightarrow> val" where
"intoflongl v = (
  case v of
    Vlong i \<Rightarrow> Vint (ucast i) |
    _ \<Rightarrow> Vundef
)"

definition intoflongh :: "val \<Rightarrow> val" where
"intoflongh v = (
  case v of
    Vlong i \<Rightarrow> Vint (ucast(i>>32)) |
    _ \<Rightarrow> Vundef
)"

definition signex32 :: "val \<Rightarrow> val" where
"signex32 v = (
  case v of
    Vint n \<Rightarrow> 
      let i::u64 = scast n in
      let d::u32 = ucast (i >> 32) in
        (Vint d)|
      _ \<Rightarrow> Vundef
)"
 \<comment> \<open> value "signex32 (Vint 0xFFFF8000)" \<close>

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

\<comment>\<open> ` x86 style extended division and modulusv` \<close>
definition divmod32u :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (val \<times> val) option" where
"divmod32u v1 v2 v3 = (           
  case v1 of 
    Vint nh \<Rightarrow> (case v2 of 
      Vint nl \<Rightarrow> (case v3 of 
        Vint d \<Rightarrow> if d \<noteq> 0 then
           let
              divisor::u64   = ucast d;
              dividend::u64  = Bit_Operations.or ((ucast nh) << 32)(ucast nl);
              quotient::u64  = dividend div divisor;
              remainder::u64 = dividend mod divisor
            in
              if quotient \<le> ucast u32_MAX then
                Some (Vint (ucast quotient), Vint (ucast remainder))
              else
                None
            else
              None
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)
  | _ \<Rightarrow> None
)"

definition bswap32 :: "val \<Rightarrow> val" where
"bswap32 v =(
  case v of 
    Vint n \<Rightarrow>( 
      let byte0 = (and n 0xFF) << 24 in
      let byte1 = (and n 0xFF00) << 8 in
      let byte2 = (and n 0xFF0000) >> 8 in                       
      let byte3 = (and n 0xFF000000) >> 24 in
      Vint (or (or (or byte0 byte1) byte2) byte3)
  )
  | _ \<Rightarrow> Vundef
)"

definition divmod32s :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (val \<times> val) option" where
"divmod32s v1 v2 v3 = (
  case v1 of 
    Vint nh \<Rightarrow> (case v2 of 
      Vint nl \<Rightarrow> (case v3 of 
        Vint d \<Rightarrow> if d \<noteq> 0 then
           let
              divisor::i64   = scast d;
              dividend::i64  = Bit_Operations.or ((scast nh) << 32) (scast nl);
              quotient::i64  = dividend div divisor;
              remainder::i64 = dividend mod divisor
            in
              if quotient \<le>s (scast i32_MAX) \<and> (scast i32_MIN) \<le>s quotient then
                Some (Vint (ucast quotient), Vint(ucast remainder))
              else
                None
            else
              None
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

definition xor32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"xor32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow> Vint (Bit_Operations.xor n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition shl32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"shl32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vbyte n2 \<Rightarrow> Vint (n1 << (unsigned n2)) | _ \<Rightarrow> Vundef) | \<comment> \<open> v2 = RCX - CL::u8 \<close>
  _ \<Rightarrow> Vundef
)"

definition shr32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"shr32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vbyte n2 \<Rightarrow> Vint (n1 >> (unsigned n2)) | _ \<Rightarrow> Vundef) | \<comment> \<open> v2 = RCX - CL::u8 \<close>
  _ \<Rightarrow> Vundef
)"

definition sar32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"sar32 v1 v2 = (
  case v1 of
  Vint n1 \<Rightarrow> (case v2 of Vbyte n2 \<Rightarrow> Vint (ucast (((scast n1)::i64) >> (unsigned n2))) | _ \<Rightarrow> Vundef) | \<comment>\<open> v2 = RCX - CL::u8 \<close>
  _ \<Rightarrow> Vundef
)"

definition ror32 :: "val \<Rightarrow> val \<Rightarrow> val" where
"ror32 v n = (                                                   
  case v of                     
  Vshort v1 \<Rightarrow> (case n of Vbyte n1 \<Rightarrow>
    let  n1 = n1 mod 32 in
     Vshort (Bit_Operations.or (v1 >> (unat n1)) (v1 << (unat (32 - n1))))
  | _ \<Rightarrow> Vundef)  
 |  _ \<Rightarrow> Vundef
)"

subsection \<open> 64-bit Arithmetic operations \<close>

definition signex64 :: "val \<Rightarrow> val" where
"signex64 v = (
  case v of
    Vlong n \<Rightarrow> 
      let i::u128 = scast n in
      let d::u64  = ucast (i >> 64) in
        (Vlong d)|
      _ \<Rightarrow> Vundef
)"

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

\<comment>\<open> ` x86 style extended division and modulusv` \<close>
definition divmod64u :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (val \<times> val) option" where
"divmod64u v1 v2 v3 = (
  case v1 of 
    Vlong nh \<Rightarrow> (case v2 of 
      Vlong nl \<Rightarrow> (case v3 of 
        Vlong d \<Rightarrow> if d \<noteq> 0 then
           let
              divisor::u128   = ucast d;
              dividend::u128  = Bit_Operations.or ((ucast nh) << 64) (ucast nl);
              quotient::u128  = dividend div divisor;
              remainder::u128 = dividend mod divisor
            in
              if quotient \<le> ucast u64_MAX then
                Some (Vlong (ucast quotient), Vlong (ucast remainder))
              else
                None
            else
              None
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)
  | _ \<Rightarrow> None
)"

definition divmod64s :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (val \<times> val) option" where
"divmod64s v1 v2 v3 = (
  case v1 of 
    Vlong nh \<Rightarrow> (case v2 of 
      Vlong nl \<Rightarrow> (case v3 of 
        Vlong d \<Rightarrow> if d \<noteq> 0 then
           let
              divisor::i128   = scast d;
              dividend::i128  = Bit_Operations.or ((scast nh) << 64) (scast nl);
              quotient::i128  = dividend div divisor;
              remainder::i128 = dividend mod divisor
            in
              if quotient \<le>s(scast i64_MAX) \<and> (scast i64_MIN) \<le>s quotient then
                Some (Vlong (ucast quotient), Vlong (ucast remainder))
              else
                None
            else
              None
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)
  | _ \<Rightarrow> None
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

definition xor64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"xor64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (Bit_Operations.xor n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition and64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"and64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow> Vlong (Bit_Operations.and n1 n2) | _ \<Rightarrow> Vundef) |
  _ \<Rightarrow> Vundef
)"

definition shl64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"shl64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vbyte n2 \<Rightarrow> Vlong (n1 << (unsigned n2)) | _ \<Rightarrow> Vundef) | \<comment> \<open>`v2 = RCX - CL`\<close>
  _ \<Rightarrow> Vundef
)"

definition shr64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"shr64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vbyte n2 \<Rightarrow> Vlong (n1 >> (unsigned n2)) | _ \<Rightarrow> Vundef) | \<comment> \<open>`v2 = RCX - CL`\<close>
  _ \<Rightarrow> Vundef
)"

definition sar64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"sar64 v1 v2 = (
  case v1 of
  Vlong n1 \<Rightarrow> (case v2 of Vbyte n2 \<Rightarrow> Vlong (ucast (((scast n1)::i64) >> (unsigned n2))) | _ \<Rightarrow> Vundef) | \<comment>\<open>`v2 = RCX - CL`\<close>
  _ \<Rightarrow> Vundef
)"

definition ror64 :: "val \<Rightarrow> val \<Rightarrow> val" where
"ror64 v n = (
  case v of                     
  Vshort v1 \<Rightarrow> (case n of Vbyte n1 \<Rightarrow>
    let  n1 = n1 mod 64 in
     Vshort (Bit_Operations.or (v1 >> (unat n1)) (v1 << (unat (32 - n1))))
  | _ \<Rightarrow> Vundef)  
 |  _ \<Rightarrow> Vundef
)"

definition bswap64 :: "val \<Rightarrow> val" where
"bswap64 v = (
  case v of 
    Vint n \<Rightarrow> (
      let byte0 = (and n 0xFF) << 56 in
      let byte1 = (and n 0xFF00) << 40 in
      let byte2 = (and n 0xFF0000) << 24 in
      let byte3 = (and n 0xFF000000) << 8 in
      let byte4 = (and n 0xFF00000000) >> 8 in
      let byte5 = (and n 0xFF0000000000) >> 24 in
      let byte6 = (and n 0xFF000000000000) >> 40 in
      let byte7 = (and n 0xFF00000000000000) >> 56 in
      Vint (or (or (or (or (or (or (or byte0 byte1) byte2) byte3) byte4) byte5) byte6) byte7)
    )
  | _ \<Rightarrow> Vundef
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