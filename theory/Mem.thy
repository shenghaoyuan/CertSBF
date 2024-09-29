section \<open> Axiom Memory model \<close>

theory Mem
imports
  Main
  rBPFCommType Val
begin

type_synonym mem = "(u64, u8) map"

definition init_mem :: "mem" where
"init_mem = (\<lambda> _. None)"

datatype memory_chunk = M8 | M16 | M32 | M64

type_synonym addr_type = u64

definition option_u64_of_u8_1 :: "u8 option \<Rightarrow> u64 option" where
"option_u64_of_u8_1 v0 = (
  case v0 of None \<Rightarrow> None |
  Some v \<Rightarrow> Some (ucast v)
)"

definition option_u64_of_u8_2 :: "u8 option \<Rightarrow> u8 option \<Rightarrow> u64 option" where
"option_u64_of_u8_2 v0 v1 = (
  case v0 of None \<Rightarrow> None |
  Some n0 \<Rightarrow> (
    case v1 of None \<Rightarrow> None |
    Some n1 \<Rightarrow> Some (or ((ucast n1) << 8) (ucast n0))
  )
)"

definition option_u64_of_u8_4 :: "u8 option \<Rightarrow> u8 option \<Rightarrow> u8 option \<Rightarrow> u8 option \<Rightarrow> u64 option" where
"option_u64_of_u8_4 v0 v1 v2 v3 = (
  case v0 of None \<Rightarrow> None |
  Some n0 \<Rightarrow> (
    case v1 of None \<Rightarrow> None |
    Some n1 \<Rightarrow> (
      case v2 of None \<Rightarrow> None |
      Some n2 \<Rightarrow> (
        case v3 of None \<Rightarrow> None |
        Some n3 \<Rightarrow>
          Some (or ((ucast n3) << 24)
                    (or ((ucast n2) << 16)
                        (or ((ucast n1) << 8) (ucast n0) ) ))))
  )
)"

definition option_u64_of_u8_8 :: "u8 option \<Rightarrow> u8 option \<Rightarrow> u8 option \<Rightarrow> u8 option \<Rightarrow>
  u8 option \<Rightarrow> u8 option \<Rightarrow> u8 option \<Rightarrow> u8 option \<Rightarrow>  u64 option" where
"option_u64_of_u8_8 v0 v1 v2 v3 v4 v5 v6 v7 = (
  case v0 of None \<Rightarrow> None |
  Some n0 \<Rightarrow> (
    case v1 of None \<Rightarrow> None |
    Some n1 \<Rightarrow> (
      case v2 of None \<Rightarrow> None |
      Some n2 \<Rightarrow> (
        case v3 of None \<Rightarrow> None |
        Some n3 \<Rightarrow> (
          case v4 of None \<Rightarrow> None |
          Some n4 \<Rightarrow> (
            case v5 of None \<Rightarrow> None |
            Some n5 \<Rightarrow> (
              case v6 of None \<Rightarrow> None |
              Some n6 \<Rightarrow> (
                case v7 of None \<Rightarrow> None |
                Some n7 \<Rightarrow>
                  Some (or ((ucast n7) << 56)
                            (or ((ucast n6) << 48)
                              (or ((ucast n5) << 40)
                                  (or ((ucast n4) << 32)
                                      (or ((ucast n3) << 24)
                                          (or ((ucast n2) << 16)
                                              (or ((ucast n1) << 8) (ucast n0) ) ))))))))))))
  )
)"

definition option_val_of_u64 :: "u64 option \<Rightarrow> val option" where
"option_val_of_u64 v = (
  case v of
  None \<Rightarrow> None |
  Some v1 \<Rightarrow> Some (Vlong v1)
)"

definition loadv :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val option" where
"loadv mc m addr = ( option_val_of_u64 (
  case mc of
  M8  \<Rightarrow> option_u64_of_u8_1 (m addr) |
  M16 \<Rightarrow> option_u64_of_u8_2 (m addr) (m (addr+1))|
  M32 \<Rightarrow> option_u64_of_u8_4 (m addr) (m (addr+1)) (m (addr+2)) (m (addr+3))|
  M64 \<Rightarrow> option_u64_of_u8_8 (m addr) (m (addr+1)) (m (addr+2)) (m (addr+3))
                        (m (addr+4)) (m (addr+5)) (m (addr+6)) (m (addr+7))
))"

definition storev :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val \<Rightarrow> mem option" where
"storev mc m addr v = (
  case mc of
  M8  \<Rightarrow> (
    case v of
    Vbyte n \<Rightarrow> Some (\<lambda> i. if i = addr then Some n else m i) |
    _ \<Rightarrow> None) |
  M16 \<Rightarrow> (
    case v of
    Vshort n \<Rightarrow>
      let l = u8_list_of_u16 n in
        Some (\<lambda> i. if i = addr    then Some (l!(0)) else
                   if i = addr+1  then Some (l!(1)) else
                      m i) |
    _ \<Rightarrow> None) |
  M32 \<Rightarrow> (
    case v of
    Vint n \<Rightarrow>
      let l = u8_list_of_u32 n in
        Some (\<lambda> i. if i = addr    then Some (l!(0)) else
                   if i = addr+1  then Some (l!(1)) else
                   if i = addr+2  then Some (l!(2)) else
                   if i = addr+3  then Some (l!(3)) else
                      m i) |
    _ \<Rightarrow> None) |
  M64 \<Rightarrow> (
    case v of
    Vlong n \<Rightarrow>
      let l = u8_list_of_u64 n in
        Some (\<lambda> i. if i = addr    then Some (l!(0)) else
                   if i = addr+1  then Some (l!(1)) else
                   if i = addr+2  then Some (l!(2)) else
                   if i = addr+3  then Some (l!(3)) else
                   if i = addr+4  then Some (l!(4)) else
                   if i = addr+5  then Some (l!(5)) else
                   if i = addr+6  then Some (l!(6)) else
                   if i = addr+7  then Some (l!(7)) else
                      m i) |
    _ \<Rightarrow> None)
)"

 (*
axiomatization
  loadv   :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val option" and
  storev  :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val \<Rightarrow> mem option"  *)

definition vlong_of_memory_chunk :: "memory_chunk \<Rightarrow> val" where
"vlong_of_memory_chunk chunk = (
  case chunk of
  M8  \<Rightarrow> Vlong 8 |
  M16 \<Rightarrow> Vlong 16 |
  M32 \<Rightarrow> Vlong 32 |
  M64 \<Rightarrow> Vlong 64
)"

end
