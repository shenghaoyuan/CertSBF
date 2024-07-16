section \<open> Interpreter of Solana rBPF \<close>

theory Interpreter
imports
  Main
  rBPFCommType rBPFSyntax vm_state vm Mem
begin

subsubsection  \<open> Interpreter State \<close>

type_synonym reg_map = "bpf_preg \<Rightarrow> u64"
                             
type_synonym mem = "(u64, val) map"

record stack_state = 
call_depth :: u64
stack_pointer :: u64
call_frames :: "CallFrame list"

type_synonym Location = u64

record rbpf_state =
registers :: reg_map
memory_mapping :: mem
stack :: stack_state
location :: Location

consts program_vm_addr::u64 

type_synonym func_key = u32

type_synonym func_val = u64

type_synonym func_map = "(func_key, func_val) map"

consts fm::func_map

definition eval_reg :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> u64" where
"eval_reg dst rs = rs (BR dst)"

(*
definition upd_reg :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> u64 \<Rightarrow> reg_map" where
"upd_reg dst rs v =  rs (BR dst := v)" *)

syntax "_upd_reg" :: "'a => 'b => 'c => 'a" ("_ # _ <-- _" [1000, 1000, 1000] 1)

(* Define the translation for the notation *)
translations
  "_upd_reg a b c" => "a(b := c)"

fun eval_snd_op_i32 :: "snd_op \<Rightarrow> reg_map \<Rightarrow> i32" where
"eval_snd_op_i32 (SOImm i) _ = scast i" |
"eval_snd_op_i32 (SOReg r) rs = scast (rs (BR r))"

fun eval_snd_op_u32 :: "snd_op \<Rightarrow> reg_map \<Rightarrow> u32" where
"eval_snd_op_u32 (SOImm i) _ = ucast i" |
"eval_snd_op_u32 (SOReg r) rs = ucast (rs (BR r))"

fun eval_snd_op_i64 :: "snd_op \<Rightarrow> reg_map \<Rightarrow> i64" where
"eval_snd_op_i64 (SOImm i) _ = scast i" |
"eval_snd_op_i64 (SOReg r) rs = scast (rs (BR r))"

fun eval_snd_op_u64 :: "snd_op \<Rightarrow> reg_map \<Rightarrow> u64" where
"eval_snd_op_u64 (SOImm i) _ = ucast i" |
"eval_snd_op_u64 (SOReg r) rs = rs (BR r)"

subsection  \<open> ALU \<close>

abbreviation bit_left_shift ::
  "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" (infix "<<" 50)
where "x << n \<equiv> push_bit n x"

abbreviation bit_right_shift ::
  "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" (infix ">>" 50)
where "x >> n \<equiv> drop_bit n x"

definition eval_alu32_aux1 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option" where
"eval_alu32_aux1 bop dst sop rs is_v1 = (
  let dv :: i32 = scast (eval_reg dst rs) in (
  let sv :: i32 = eval_snd_op_i32 sop rs in (
  case bop of
  BPF_ADD \<Rightarrow> Some (rs#(BR dst) <-- (ucast (dv + sv))) |
  BPF_SUB \<Rightarrow> (case sop of (SOReg i) \<Rightarrow> Some (rs#(BR dst) <-- (ucast (dv - sv))) |
                           _ \<Rightarrow> (if is_v1 then Some (rs#(BR dst) <-- (ucast (dv - sv))) 
                                else Some (rs#(BR dst) <-- (ucast (sv - dv))))) |
  BPF_MUL \<Rightarrow> Some (rs#(BR dst) <-- (ucast (dv * sv))) |
  _ \<Rightarrow> None
)))"

definition eval_alu32_aux2 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option" where
"eval_alu32_aux2 bop dst sop rs = (
  let dv :: u32 = ucast (eval_reg dst rs) in (
  let sv :: u32 = eval_snd_op_u32 sop rs in (
  case bop of
  BPF_DIV \<Rightarrow> if sv = 0 then None else Some (rs#(BR dst) <-- (ucast (dv div sv))) |
  BPF_OR  \<Rightarrow> Some (rs#(BR dst) <-- (ucast (or dv sv))) |
  BPF_AND \<Rightarrow> Some (rs#(BR dst) <-- (ucast (and dv sv))) |
  BPF_MOD \<Rightarrow> if sv = 0 then None else Some (rs#(BR dst) <-- (ucast (dv mod sv))) |
  BPF_XOR \<Rightarrow> Some (rs#(BR dst) <-- (ucast (xor dv sv))) |
  BPF_MOV \<Rightarrow> Some (rs#(BR dst) <-- (ucast sv)) |
  BPF_LSH \<Rightarrow> Some (rs#(BR dst) <-- (ucast (dv << unat sv))) |
  BPF_RSH \<Rightarrow> Some (rs#(BR dst) <-- (ucast (dv >> unat sv))) |
  _ \<Rightarrow> None
)))"

definition eval_alu32_aux3 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option" where
"eval_alu32_aux3 bop dst sop rs  = (
  let dv :: i32 = scast (eval_reg dst rs) in (
  let sv :: u32 = eval_snd_op_u32 sop rs in (
  case bop of
  BPF_ARSH \<Rightarrow> Some (rs#(BR dst) <-- (and (ucast (dv << unat sv)::u64) (ucast u32_MAX)) ) | 
  _ \<Rightarrow> None
)))"

definition eval_alu32 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option" where
"eval_alu32 bop dst sop rs is_v1 = (
  case bop of
  BPF_ADD   \<Rightarrow> eval_alu32_aux1 bop dst sop rs is_v1 |
  BPF_SUB   \<Rightarrow> eval_alu32_aux1 bop dst sop rs is_v1 |
  BPF_MUL   \<Rightarrow> if is_v1 then eval_alu32_aux1 bop dst sop rs is_v1 else None|
  BPF_DIV   \<Rightarrow> if is_v1 then eval_alu32_aux2 bop dst sop rs else None|
  BPF_OR    \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_AND   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_MOD   \<Rightarrow> if is_v1 then eval_alu32_aux2 bop dst sop rs else None|
  BPF_XOR   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_MOV   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_LSH   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  | 
  BPF_RSH   \<Rightarrow> eval_alu32_aux2 bop dst sop rs |
  BPF_ARSH  \<Rightarrow> eval_alu32_aux3 bop dst sop rs 
)"

definition eval_alu64_aux1 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> (reg_map \<times> stack_state) option" where
"eval_alu64_aux1 bop dst sop rs ss is_v1 = (
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u64 = eval_snd_op_u64 sop rs in (
  case bop of
  BPF_SUB \<Rightarrow> (case sop of (SOReg i) \<Rightarrow> Some (rs#(BR dst) <-- (dv - sv),ss) |
                           _ \<Rightarrow> (if is_v1 then Some (rs#(BR dst) <-- (dv - sv),ss) 
                                else Some (rs#(BR dst) <-- (sv - dv),ss))) |
  BPF_MUL \<Rightarrow> Some (rs#(BR dst) <-- (dv * sv),ss) |
  BPF_DIV \<Rightarrow> if sv = 0 then None else Some (rs#(BR dst) <-- (dv div sv),ss) |
  BPF_OR  \<Rightarrow> Some (rs#(BR dst) <-- (or dv sv),ss) |
  BPF_AND \<Rightarrow> Some (rs#(BR dst) <-- (and dv sv),ss) |
  BPF_MOD \<Rightarrow> if sv = 0 then None else Some (rs#(BR dst) <-- (dv mod sv),ss) |
  BPF_XOR \<Rightarrow> Some (rs#(BR dst) <-- (xor dv sv),ss) |
  BPF_MOV \<Rightarrow> Some (rs#(BR dst) <-- sv,ss) |
  _ \<Rightarrow> None
)))"


definition eval_alu64_aux2 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> (reg_map \<times> stack_state) option" where
"eval_alu64_aux2 bop dst sop rs ss = (
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u32 = eval_snd_op_u32 sop rs in (
  case bop of
  BPF_LSH \<Rightarrow> Some (rs#(BR dst) <-- (dv << unat sv),ss) |  \<comment> \<open> to unat \<close>
  BPF_RSH \<Rightarrow> Some (rs#(BR dst) <-- (dv >> unat sv),ss) |  \<comment> \<open> to unat \<close>
  _ \<Rightarrow> None
)))" 

definition eval_alu64_aux3 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> (reg_map \<times> stack_state) option" where
"eval_alu64_aux3 bop dst sop rs ss = (
  let dv :: i64 = scast (eval_reg dst rs) in (
  let sv :: u32 = eval_snd_op_u32 sop rs in (
  case bop of
  BPF_ARSH \<Rightarrow> Some (rs#(BR dst) <-- (ucast (dv >> unat sv)::u64),ss) |
  _ \<Rightarrow> None
)))"

definition eval_alu64_aux4 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> (reg_map \<times> stack_state) option" where
"eval_alu64_aux4 bop dst sop rs ss is_v1 = (
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u64 = eval_snd_op_u64 sop rs in (
  let sp = stack_pointer ss in 
  case bop of
  BPF_ADD \<Rightarrow> (case sop of SOImm _ \<Rightarrow> if \<not>is_v1 \<and> dst = BR10 then Some (rs, ss\<lparr>stack_pointer := sp+sv\<rparr>) else None |
                                _ \<Rightarrow> None)|
  _ \<Rightarrow> None

)))"

definition eval_alu64 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> (reg_map \<times> stack_state) option" where
"eval_alu64 bop dst sop rs ss is_v1 = (
  case bop of
  BPF_ADD \<Rightarrow> eval_alu64_aux4 bop dst sop rs ss is_v1 |
  BPF_SUB \<Rightarrow> eval_alu64_aux1 bop dst sop rs ss is_v1 |
  BPF_MUL \<Rightarrow> if is_v1 then eval_alu64_aux1 bop dst sop rs ss is_v1 else None |
  BPF_DIV \<Rightarrow> if is_v1 then eval_alu64_aux1 bop dst sop rs ss is_v1 else None |
  BPF_OR \<Rightarrow> eval_alu64_aux1 bop dst sop rs ss is_v1 |
  BPF_AND \<Rightarrow> eval_alu64_aux1 bop dst sop rs ss is_v1 |
  BPF_MOD \<Rightarrow> if is_v1 then eval_alu64_aux1 bop dst sop rs ss is_v1 else None |
  BPF_XOR \<Rightarrow> eval_alu64_aux1 bop dst sop rs ss is_v1 |
  BPF_MOV \<Rightarrow> eval_alu64_aux1 bop dst sop rs ss is_v1 |
  BPF_LSH \<Rightarrow> eval_alu64_aux2 bop dst sop rs ss |
  BPF_RSH \<Rightarrow> eval_alu64_aux2 bop dst sop rs ss |
  BPF_ARSH \<Rightarrow> eval_alu64_aux3 bop dst sop rs ss
)"

definition eval_neg32 :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option" where
"eval_neg32 dst rs is_v1 = (if is_v1 then (let dv::i32 = scast (eval_reg dst rs) in 
    Some ( rs#(BR dst) <-- (and (ucast(-dv)::u64) (ucast u32_MAX))) )
  else None
)"

definition eval_neg64 :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option" where
"eval_neg64 dst rs is_v1 = (if is_v1 then (let dv::i64 = scast (eval_reg dst rs) in 
    Some ( rs#(BR dst) <-- (ucast(-dv)::u64)) )
  else None
)"

(**r TODO: stop here *)

fun to_le_64 :: "u64 \<Rightarrow> nat \<Rightarrow> u8 list" where
  "to_le_64 w 0 = []" |
  "to_le_64 w n = (ucast(and w 0xFF)) # to_le_64 (w >> 8) (n - 1)"

definition to_be_64 :: "u64 \<Rightarrow> nat \<Rightarrow> u8 list" where
  "to_be_64 w n = rev (to_le_64 w n)"

(*
fun to_be_64 :: "u64 \<Rightarrow> nat \<Rightarrow> u8 list" where
  "to_be_64 w 0 = []" |
  "to_be_64 w n =  to_be_64 (w >> 8) (n - 1) @ [(ucast(and w 0xFF))]" *)

fun to_le_32 :: "u32 \<Rightarrow> nat \<Rightarrow> u8 list" where
  "to_le_32 w 0 = []" |
  "to_le_32 w n = (ucast(and w 0xFF)) # to_le_32 (w >> 8) (n - 1)"

fun to_be_32 :: "u32 \<Rightarrow> nat \<Rightarrow> u8 list" where
  "to_be_32 w 0 = []" |
  "to_be_32 w n =  to_be_32 (w >> 8) (n - 1) @ [(ucast(and w 0xFF))]"

fun to_le_16 :: "u16 \<Rightarrow> nat \<Rightarrow> u8 list" where
  "to_le_16 w 0 = []" |
  "to_le_16 w n = (ucast(and w 0xFF)) # to_le_16 (w >> 8) (n - 1)"

fun to_be_16 :: "u16 \<Rightarrow> nat \<Rightarrow> u8 list" where
  "to_be_16 w 0 = []" |
  "to_be_16 w n =  to_be_16 (w >> 8) (n - 1) @ [(ucast(and w 0xFF))]"

fun from_bytes :: "u8 list \<Rightarrow> nat \<Rightarrow> int" where
  "from_bytes _ 0 = 0" |
  "from_bytes x (Suc n) = (uint ((ucast(x!n)::u64) << 8*n)) + from_bytes x n"

fun u64_of_u8_list_aux :: "u8 list \<Rightarrow> u64" where
"u64_of_u8_list_aux [] = 0" |
"u64_of_u8_list_aux (h#t) = or (ucast h) ((u64_of_u8_list_aux t) << 8)"

definition u64_of_u8_list :: "u8 list \<Rightarrow> u64" where
"u64_of_u8_list l = u64_of_u8_list_aux (rev l)"

fun u64_of_u16_list1 :: "u8 list \<Rightarrow> u16" where
"u64_of_u16_list1 [] = 0" |
"u64_of_u16_list1 (h#t) = or ((ucast h) << (8*length(t))) (u64_of_u16_list1 t)"

fun u32_of_u8_list_aux :: "u8 list \<Rightarrow> u32" where
"u32_of_u8_list_aux [] = 0" |
"u32_of_u8_list_aux (h#t) = or (ucast h) ((u32_of_u8_list_aux t) << 8)"

definition u32_of_u8_list :: "u8 list \<Rightarrow> u32" where
"u32_of_u8_list l = u32_of_u8_list_aux (rev l)"

fun u16_of_u8_list_aux :: "u8 list \<Rightarrow> u16" where
"u16_of_u8_list_aux [] = 0" |
"u16_of_u8_list_aux (h#t) = or (ucast h) ((u16_of_u8_list_aux t) << 8)"

definition u16_of_u8_list :: "u8 list \<Rightarrow> u16" where
"u16_of_u8_list l = u16_of_u8_list_aux (rev l)"

(*text \<open> tests \<close>
definition a :: u64 where "a = 0x123456"
definition b :: u64 where "b = 0x0F0F0F0F0F0F0F0F"
definition c :: u16 where "c = 0x1234"

value "-0x1::u64"
value "a"
value "a<<8"

value "and a b"

value "to_be_64 a 8"
value "to_le_64 a 8"

value "(1234::u16) << 8"

value "ucast(ucast (32::i16)::u64)::u64"

value "c"

value "of_int(from_bytes (rev(to_be_16 c 4)) 4)::u16"

value "a"
value "u64_of_u8_list [0x12, 0x34]"
value "u64_of_u8_list1 [0x12, 0x34]"

value "of_int(from_bytes (rev(to_be_64 a 8)) 8)::u64" 

value "u64_of_u8_list (to_be_64 a 8)"
*)

definition eval_le :: "dst_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option" where
"eval_le dst imm rs is_v1 = (if is_v1 then (let dv = eval_reg dst rs in ((
        if imm = 16 then let x = ucast(dv)::u16; v = ucast (u16_of_u8_list (to_le_16 x 4)) in Some (rs#(BR dst) <-- v)
  else  if imm = 32 then let x = ucast(dv)::u32; v = ucast (u32_of_u8_list (to_le_32 x 6)) in  Some (rs#(BR dst) <-- v)
  else  if imm = 64 then let v = u64_of_u8_list (to_le_64 dv 8) in Some (rs#(BR dst) <-- v)
  else None)))
  else None
)"

definition eval_be :: "dst_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option" where
"eval_be dst imm rs is_v1 = (if is_v1 then (let dv = eval_reg dst rs in ((
        if imm = 16 then let x = ucast(dv)::u16; v = ucast (u16_of_u8_list (to_be_16 x 4)) in Some (rs#(BR dst) <-- v)
  else  if imm = 32 then let x = ucast(dv)::u32; v = ucast (u32_of_u8_list (to_le_32 x 6)) in  Some (rs#(BR dst) <-- v)
  else  if imm = 64 then let v = u64_of_u8_list (to_be_64 dv 8) in Some (rs#(BR dst) <-- v)
  else None)))
  else None
)"

definition eval_hor64 :: "dst_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option" where
"eval_hor64 dst imm rs is_v1 = 
(if is_v1 then (let dv::u64 = eval_reg dst rs; dv2 = or dv (((ucast imm)::u64) << 32) in 
    ( Some (rs#(BR dst) <-- dv2)))
  else None
)"

subsection  \<open> PQR \<close>

definition eval_pqr32_aux1 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option" where
"eval_pqr32_aux1 pop dst sop rs  = (
  let dv :: i32 = scast (eval_reg dst rs) in (
  let sv :: i32 = eval_snd_op_i32 sop rs in (
  case pop of
  BPF_LMUL \<Rightarrow> Some (rs#(BR dst) <-- (ucast (dv * sv))) |
  BPF_SDIV \<Rightarrow> Some (rs#(BR dst) <-- (ucast (dv div sv))) |
  BPF_SREM \<Rightarrow> Some (rs#(BR dst) <-- (ucast (dv mod sv))) |
  _ \<Rightarrow> None
)))"

definition eval_pqr32_aux2 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option" where
"eval_pqr32_aux2 pop dst sop rs = (
  let dv :: u32 = ucast (eval_reg dst rs) in (
  let sv :: u32 = eval_snd_op_u32 sop rs in (
  case pop of
  BPF_UDIV \<Rightarrow> if sv = 0 then None else Some (rs#(BR dst) <-- (ucast (dv div sv))) |
  BPF_UREM \<Rightarrow> Some (rs#(BR dst) <-- (ucast (dv mod sv))) |
  _ \<Rightarrow> None

)))"

definition eval_pqr32 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option" where
"eval_pqr32 pop dst sop rs is_v1 = (
  if is_v1 then None else(
  case pop of
  BPF_LMUL \<Rightarrow> eval_pqr32_aux1 pop dst sop rs  |
  BPF_UDIV \<Rightarrow> eval_pqr32_aux2 pop dst sop rs  | 
  BPF_UREM \<Rightarrow> eval_pqr32_aux2 pop dst sop rs  | 
  BPF_SDIV \<Rightarrow> eval_pqr32_aux1 pop dst sop rs  |
  BPF_SREM \<Rightarrow> eval_pqr32_aux1 pop dst sop rs 
))"

definition eval_pqr64_aux1 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option" where
"eval_pqr64_aux1 pop dst sop rs  = (
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u64 = eval_snd_op_u64 sop rs in (
  case pop of
  BPF_LMUL \<Rightarrow> Some (rs#(BR dst) <-- (ucast (dv * sv))) |  
  BPF_UDIV \<Rightarrow> if sv = 0 then None else Some (rs#(BR dst) <-- (ucast (dv div sv))) | 
  BPF_UREM \<Rightarrow> if sv = 0 then None else Some (rs#(BR dst) <-- (ucast (dv mod sv)))  
)))"

definition eval_pqr64_aux2 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option" where
"eval_pqr64_aux2 pop dst sop rs = (
  let dv :: i64 = scast (eval_reg dst rs) in (
  let sv :: i64 = eval_snd_op_i64 sop rs in (
  case pop of
  BPF_SDIV \<Rightarrow> if sv = 0 then None else Some (rs#(BR dst) <-- (ucast (dv div sv))) | 
  BPF_SREM \<Rightarrow> if sv = 0 then None else Some (rs#(BR dst) <-- (ucast (dv mod sv)))   
)))"

definition eval_pqr64 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option" where
"eval_pqr64 pop dst sop rs is_v1 = (
  if is_v1 then None else(
  case pop of
  BPF_LMUL \<Rightarrow> eval_pqr64_aux1 pop dst sop rs |  
  BPF_UDIV \<Rightarrow> eval_pqr64_aux1 pop dst sop rs | 
  BPF_UREM \<Rightarrow> eval_pqr64_aux1 pop dst sop rs | 
  BPF_SDIV \<Rightarrow> eval_pqr64_aux2 pop dst sop rs | 
  BPF_SREM \<Rightarrow> eval_pqr64_aux2 pop dst sop rs   
))"

definition eval_pqr64_2 :: "pqrop2 \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option" where
"eval_pqr64_2 pop2 dst sop rs is_v1 = (
  if is_v1 then None else(
  let dv_u :: u128 = ucast (eval_reg dst rs) in (
  let sv_u :: u128 = ucast (eval_snd_op_u64 sop rs) in (
  let dv_i :: u128 = ucast (scast (eval_reg dst rs)::i64) in (
  let sv_i :: u128 = ucast (scast (eval_reg dst rs)::i64) in (
  case pop2 of
  BPF_UHMUL \<Rightarrow> Some (rs#(BR dst) <-- (ucast (dv_u * sv_u)>>64)) |
  BPF_SHMUL \<Rightarrow> Some (rs#(BR dst) <-- (ucast (dv_i * sv_i)>>64)) 
))))))"

subsection  \<open> MEM \<close>

definition eval_store :: "chunk \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> off_ty \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> mem option" where
"eval_store chk dst sop off rs mem = (
  let dv :: i64 = scast (eval_reg dst rs) in (
  let vm_addr :: u64 = ucast (dv + (scast off)) in (  
  let sv :: u64 = eval_snd_op_u64 sop rs in ( \<comment> \<open> TODO: sv is signed for imm and unsigned for src reg? \<close>
  let size = case chk of Byte \<Rightarrow> M8 | HalfWord \<Rightarrow> M16 | SWord \<Rightarrow> M32 | DWord \<Rightarrow> M64 in (
  (storev size mem (Vlong vm_addr) (Vlong sv))
)))))"


definition eval_load :: "chunk \<Rightarrow> dst_ty \<Rightarrow> src_ty \<Rightarrow> off_ty \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> reg_map option" where
"eval_load chk dst sop off rs mem = (
  let sv :: u64 = eval_snd_op_u64 (SOReg sop) rs in (
  let vm_addr :: u64 = ucast (sv + (scast off)) in (  
  let size = case chk of Byte \<Rightarrow> M8 | HalfWord \<Rightarrow> M16 | SWord \<Rightarrow> M32 | DWord \<Rightarrow> M64 in (
  let v = (loadv size mem (Vlong vm_addr)) in (
     case v of None \<Rightarrow> None |
               Some Vundef \<Rightarrow>  None | 
               Some (Vlong v) \<Rightarrow>  Some (rs#(BR dst) <-- v) |
               Some (Vint v) \<Rightarrow> Some (rs#(BR dst) <-- (ucast v))
)))))"

(*definition store_mem::"mem_len \<Rightarrow> i64 \<Rightarrow> usize \<Rightarrow> mem \<Rightarrow> mem" where  
"store_mem len v vm_addr mem = mem (vm_addr := Some ((ucast v)::u64))" \<comment> \<open> should be size of u8/u16/u32/u64 \<close>

definition eval_store :: "chunk \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> off_ty \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> mem option" where
"eval_store chk dst sop off rs mem = (
  let dv :: i64 = scast (eval_reg dst rs) in (
  let vm_addr :: u64 = ucast (dv + (ucast off)) in (  \<comment> \<open> TODO: + is signed or unsigned? \<close>
  let sv :: i64 = eval_snd_op_i64 sop rs in (
  let size = case chk of Byte \<Rightarrow> u8 | HalfWord \<Rightarrow> u16 | SWord \<Rightarrow> u32 | DWord \<Rightarrow> u64 in (
  Some (store_mem size sv vm_addr mem)
)))))"

definition load_mem::"mem_len \<Rightarrow> usize \<Rightarrow> mem \<Rightarrow> u64 option" where
"load_mem len vm_addr mem = (mem vm_addr)"

definition eval_load :: "chunk \<Rightarrow> dst_ty \<Rightarrow> src_ty \<Rightarrow> off_ty \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> reg_map option" where
"eval_load chk dst sop off rs mem = (
  let sv :: i64 = eval_snd_op_i64 (SOReg sop) rs in (
  let vm_addr :: u64 = ucast (sv + (ucast off)) in (  \<comment> \<open> TODO: + is signed or unsigned? \<close>
  let size = case chk of Byte \<Rightarrow> u8 | HalfWord \<Rightarrow> u16 | SWord \<Rightarrow> u32 | DWord \<Rightarrow> u64 in (
  let v = (load_mem size vm_addr mem) in (
     case v of None \<Rightarrow> None |
                  _ \<Rightarrow>  Some (rs#(BR dst) <-- (the v))
)))))"
*)
definition eval_load_imm :: "dst_ty \<Rightarrow> imm_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> reg_map option" where
"eval_load_imm dst imm1 imm2 rs mem = (
  let sv1 :: i64 = eval_snd_op_i64 (SOImm imm1) rs in (
  let sv2 :: i64 = eval_snd_op_i64 (SOImm imm2) rs in (
  let vm_addr :: u64 = ucast (sv1+sv2) in (
  let v = (loadv M64 mem (Vlong vm_addr)) in (
     case v of None \<Rightarrow> None |
               Some Vundef \<Rightarrow>  None | 
               Some (Vlong v) \<Rightarrow>  Some (rs#(BR dst) <-- v) |
               Some (Vint v) \<Rightarrow> Some (rs#(BR dst) <-- (ucast v))
)))))"


subsection  \<open> JUMP \<close>

definition eval_pc :: "reg_map \<Rightarrow> u64" where
"eval_pc rs  = rs BPC"

definition eval_jmp_aux1 :: "condition \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> off_ty \<Rightarrow> reg_map option" where
"eval_jmp_aux1 cond dst sop rs off = (
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u64 = eval_snd_op_u64 sop rs in (
  let pc :: u64 = ucast (scast off + scast(eval_pc rs)::i64) in (  \<comment> \<open> TODO: + is signed or unsigned? \<close>
  case cond of
  Eq \<Rightarrow> (if dv = sv then Some (rs#BPC <-- (ucast (dv + sv))) else None) |
  Gt \<Rightarrow> (if dv > sv then Some (rs#BPC <-- (ucast (dv + sv))) else None) |
  Ge \<Rightarrow> (if dv \<ge> sv then Some (rs#BPC <-- (ucast (dv + sv))) else None) |
  Lt \<Rightarrow> (if dv < sv then Some (rs#BPC <-- (ucast (dv + sv))) else None) |
  Le \<Rightarrow> (if dv \<le> sv then Some (rs#BPC <-- (ucast (dv + sv))) else None) |
  SEt \<Rightarrow> (if (and dv sv\<noteq>0) then Some (rs#BPC <-- (ucast (dv + sv))) else None) |
  Ne \<Rightarrow> (if dv \<noteq> sv then Some (rs#BPC <-- (ucast (dv + sv))) else None) |
  _ \<Rightarrow> None
))))"

definition eval_jmp_aux2 :: "condition \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> off_ty \<Rightarrow> reg_map option" where
"eval_jmp_aux2 cond dst sop rs off = (
  let dv :: i64 = scast (eval_reg dst rs) in (
  let sv :: i64 = eval_snd_op_i64 sop rs in (
  let pc :: u64 = ucast (scast off + scast(eval_pc rs)::i64) in ( 
  case cond of
  SGt \<Rightarrow> (if sv <s dv then Some (rs#BPC <-- (ucast (dv + sv))) else None) |
  SGe \<Rightarrow> (if sv \<le>s dv then Some (rs#BPC <-- (ucast (dv + sv))) else None) |
  SLt \<Rightarrow> (if dv <s sv then Some (rs#BPC <-- (ucast (dv + sv))) else None) |
  SLe \<Rightarrow> (if dv \<le>s sv then Some (rs#BPC <-- (ucast (dv + sv))) else None) |
  _ \<Rightarrow> None
))))"

definition eval_jmp :: "condition \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> off_ty \<Rightarrow> reg_map option" where
"eval_jmp cond dst sop rs off = (
  case cond of
  Eq \<Rightarrow> eval_jmp_aux1 cond dst sop rs off |
  Gt \<Rightarrow> eval_jmp_aux1 cond dst sop rs off |
  Ge \<Rightarrow> eval_jmp_aux1 cond dst sop rs off |
  Lt \<Rightarrow> eval_jmp_aux1 cond dst sop rs off |
  Le \<Rightarrow> eval_jmp_aux1 cond dst sop rs off |
  SEt \<Rightarrow> eval_jmp_aux1 cond dst sop rs off |
  Ne \<Rightarrow> eval_jmp_aux1 cond dst sop rs off |
  SGt \<Rightarrow> eval_jmp_aux2 cond dst sop rs off |
  SGe \<Rightarrow> eval_jmp_aux2 cond dst sop rs off |
  SLt \<Rightarrow> eval_jmp_aux2 cond dst sop rs off |
  SLe \<Rightarrow> eval_jmp_aux2 cond dst sop rs off 
)"

subsection  \<open> CALL \<close>

definition get_function_registry ::"func_key \<Rightarrow> func_val option" where
"get_function_registry key = fm key"

definition push_frame:: "Config \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> stack_state option \<times> reg_map" where 
"push_frame conf rs ss is_v1 = (let pc = eval_pc rs +1; fp = eval_reg BR10 rs ;
  frame = \<lparr>frame_pointer = pc, target_pc = fp\<rparr> in 
  let update1 = call_depth ss +1 in (if update1 = max_call_depth conf then (None, rs) else (
  let update2 = if is_v1 then (if enable_stack_frame_gaps conf then stack_pointer ss + stack_frame_size conf*2
  else stack_pointer ss + stack_frame_size conf) else stack_pointer ss;  
  update3 = (call_frames ss)[unat(call_depth ss):= frame] in
  let stack = Some \<lparr>call_depth = update1, stack_pointer = update2, call_frames = update3\<rparr>;
  reg = rs#(BR BR10) <-- update2 in (stack,reg)
)))"

definition eval_call_reg :: "Config \<Rightarrow> src_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> (reg_map \<times> stack_state) option" where
"eval_call_reg conf src imm rs ss is_v1 = (
  let target_pc = if is_v1 then eval_reg (the (u4_to_bpf_ireg (ucast imm))) rs else eval_reg src rs in  
  let x = push_frame conf rs ss is_v1 in if fst x = None then None else(
  let ss' = the (fst x); rs' = snd x in
  if target_pc < program_vm_addr then None else (
  let next_pc = (target_pc - program_vm_addr)div INSN_SIZE in 
  if get_function_registry (ucast next_pc) = None then None  \<comment> \<open> function lookup \<close> 
  else Some (rs'#BPC <-- next_pc, ss')
)))"

definition eval_call_imm :: "Config \<Rightarrow> src_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> (reg_map \<times> stack_state) option" where
"eval_call_imm conf src imm rs ss is_v1 = ( \<comment> \<open> should add decision of internal or external call \<close> 
  let target_pc = get_function_registry (ucast imm) in if target_pc = None then None else    \<comment> \<open> function lookup \<close> 
  let target_pc = the target_pc; x = push_frame conf rs ss is_v1 in if fst x = None then None else(
  let ss' = the (fst x); rs' = snd x in 
  let next_pc = target_pc in Some (rs'#BPC <-- next_pc, ss')
))"

definition pop_frame:: "stack_state \<Rightarrow> CallFrame" where 
"pop_frame ss = (call_frames ss)!(unat (call_depth ss)) "

subsection  \<open> EXIT \<close>

definition eval_exit :: "Config \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> (reg_map \<times> stack_state) option" where
"eval_exit conf rs ss is_v1 = (
  if call_depth ss = 0 then None else 
  (let x = call_depth ss-1 ; frame = pop_frame ss; rs'= rs#(BR BR10) <-- (frame_pointer frame) in 
   let y =  if is_v1 then (stack_pointer ss - stack_frame_size conf) else stack_pointer ss; 
   z = butlast (call_frames ss) ; ss' = \<lparr>call_depth = x, stack_pointer= y, call_frames = z\<rparr> in
   let pc = target_pc frame; rs' = rs'#BPC <-- pc in 
   Some (rs',ss')
))"

subsection  \<open> step \<close>

fun step :: "Config \<Rightarrow> bpf_instruction \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> stack_state \<Rightarrow> Location \<Rightarrow> bool \<Rightarrow> rbpf_state option" where
"step conf ins rs m ss l is_v1 =
 (let next_pc = l+1 in (
  case ins of
  BPF_ALU bop d sop \<Rightarrow> (
    case eval_alu32 bop d sop rs is_v1 of
      None \<Rightarrow> None |
      Some rs' \<Rightarrow> Some \<lparr> registers = rs', memory_mapping = m, stack = ss, location = next_pc\<rparr> ) |
  BPF_ALU64 bop d sop \<Rightarrow> (
    case eval_alu64 bop d sop rs ss is_v1 of
      None \<Rightarrow> None |
      Some x \<Rightarrow> Some \<lparr> registers = fst x, memory_mapping = m, stack = snd x, location = next_pc \<rparr> ) |
  BPF_LE dst imm \<Rightarrow> (
    case eval_le dst imm rs is_v1 of
      None \<Rightarrow> None |
      Some rs' \<Rightarrow> Some \<lparr> registers = rs', memory_mapping = m, stack = ss, location = next_pc\<rparr> ) |
  BPF_BE dst_ty imm_ty \<Rightarrow> (
    case eval_be dst_ty imm_ty rs is_v1 of
      None \<Rightarrow> None |
      Some rs' \<Rightarrow> Some \<lparr> registers = rs', memory_mapping = m, stack = ss, location = next_pc \<rparr> ) |
  BPF_NEG32_REG dst \<Rightarrow> (
    case eval_neg32 dst rs is_v1 of
      None \<Rightarrow> None |
      Some rs' \<Rightarrow> Some \<lparr> registers = rs', memory_mapping = m, stack = ss, location = next_pc\<rparr> ) |
  BPF_NEG64_REG dst \<Rightarrow> (
    case eval_neg64 dst rs is_v1 of
      None \<Rightarrow> None |
      Some rs' \<Rightarrow> Some \<lparr> registers = rs', memory_mapping = m, stack = ss, location = next_pc\<rparr> ) |
  BPF_LDX chk dst sop off \<Rightarrow> (
    case eval_load chk dst sop off rs m of
      None \<Rightarrow> None |
      Some rs' \<Rightarrow> Some \<lparr> registers = rs', memory_mapping = m, stack = ss, location = next_pc \<rparr> ) |
  BPF_ST chk dst sop off \<Rightarrow> (
    case eval_store chk dst sop off rs m of
      None \<Rightarrow> None |
      Some m' \<Rightarrow> Some \<lparr> registers = rs, memory_mapping = m', stack = ss, location = next_pc\<rparr> ) |
  BPF_LD_IMM dst imm1 imm2  \<Rightarrow> (
    case eval_load_imm dst imm1 imm2 rs m of
      None \<Rightarrow> None |
      Some rs' \<Rightarrow> Some \<lparr> registers = rs', memory_mapping = m, stack = ss, location = next_pc\<rparr> ) |
  BPF_PQR pop dst sop \<Rightarrow> (
    case eval_pqr32 pop dst sop rs is_v1 of
      None \<Rightarrow> None |
      Some rs' \<Rightarrow> Some \<lparr> registers = rs', memory_mapping = m,stack = ss, location = next_pc\<rparr> ) |
  BPF_PQR64 pop dst sop \<Rightarrow> (
    case eval_pqr64 pop dst sop rs is_v1 of
      None \<Rightarrow> None |
      Some rs' \<Rightarrow> Some \<lparr> registers = rs', memory_mapping = m, stack = ss, location = next_pc\<rparr> ) |
  BPF_PQR2 pop2 dst sop \<Rightarrow> (
    case eval_pqr64_2 pop2 dst sop rs is_v1 of
      None \<Rightarrow> None |
      Some rs' \<Rightarrow> Some \<lparr> registers = rs', memory_mapping = m, stack = ss, location = next_pc \<rparr> ) |
  BPF_HOR64_IMM dst imm \<Rightarrow> (
    case eval_hor64 dst imm rs is_v1 of
      None \<Rightarrow> None |
      Some rs' \<Rightarrow> Some \<lparr> registers = rs', memory_mapping = m, stack = ss, location = next_pc\<rparr> ) |
  BPF_JA off_ty  \<Rightarrow> (
      let rs'= rs (BPC := eval_pc rs + ucast off_ty) in
      Some \<lparr> registers = rs', memory_mapping = m, stack = ss, location = eval_pc rs'\<rparr> ) |
  BPF_JUMP cond bpf_ireg snd_op off_ty  \<Rightarrow> (
    case eval_jmp cond bpf_ireg snd_op rs off_ty of
      None \<Rightarrow> None |
      Some rs' \<Rightarrow> Some \<lparr> registers = rs', memory_mapping = m, stack = ss, location = eval_pc rs'\<rparr> ) |
  BPF_CALL_IMM src imm \<Rightarrow> (
    case eval_call_imm conf src imm rs ss is_v1  of
      None \<Rightarrow> None |
      Some x \<Rightarrow> Some \<lparr> registers = fst x, memory_mapping = m, stack = snd x, location = eval_pc (fst x)\<rparr> ) |
  BPF_CALL_REG src imm \<Rightarrow> (
    case eval_call_reg conf src imm rs ss is_v1  of
      None \<Rightarrow> None |
      Some x \<Rightarrow> Some \<lparr> registers = fst x, memory_mapping = m, stack = snd x, location = eval_pc (fst x)\<rparr> ) |
  BPF_EXIT \<Rightarrow> (
    case eval_exit conf rs ss is_v1  of
      None \<Rightarrow> None |
      Some x \<Rightarrow> Some \<lparr> registers = fst x, memory_mapping = m, stack = snd x, location = eval_pc (fst x)\<rparr> ) 
  ))
"

fun steps :: "Config \<Rightarrow> ebpf_asm \<Rightarrow> nat \<Rightarrow> rbpf_state \<Rightarrow> rbpf_state option" where
"steps conf _ 0 sm = Some sm " | 
"steps conf prog max_steps sm = (
  (if unat (location sm) < length prog then
   let temp = step conf (prog!unat (location sm)) (registers sm) (memory_mapping sm) (stack sm) (location sm) (enable_sbpf_v2 conf) in 
     if temp \<noteq> None then steps conf prog (max_steps-1) (the temp) else None
   else None))"


lemma "((ucast ((ucast (i::i32))::u64)) :: u32) = ((ucast (i::i32))::u32)"
proof-

   have n:"take_bit LENGTH(32)  (uint i) = take_bit 32 (uint i)" by auto
   have m:"take_bit LENGTH(64)  (uint i) = take_bit 64 (uint i)" by auto

  have "((ucast ((word_of_int (uint i))::u64)) :: u32)  = ((ucast ((word_of_int (uint i))::u32)) :: u32)"
    using n m 
    by (smt (verit, best) bintr_uint len_signed nat_le_linear numeral_Bit0_eq_double numeral_le_iff
         of_int_uint semiring_norm(69) take_bit_tightened_less_eq_int unsigned_ucast_eq)
   then show ?thesis by auto
qed

lemma "((ucast ((ucast (i::i32))::u64)) :: u32) = ((ucast (i::i32))::u32)"
proof-
  
  
  have "((ucast ((ucast (i::i32))::u64)) :: u32) = ((ucast ((word_of_int (uint i))::u64)) :: u32) " 
    by auto
  also have "((ucast ((word_of_int (uint i))::u64)) :: u32)  = ((ucast ((word_of_int (uint i))::u32)) :: u32)"
  proof- 
    have n:"take_bit LENGTH(32)  (uint i) = take_bit 32 (uint i)" by auto
    moreover  have m:"take_bit LENGTH(64)  (uint i) = take_bit 64 (uint i)" by auto
    have "of_nat (nat (take_bit 32 (uint i))) = ((ucast ((word_of_int (uint i))::u32)))"
      using unsigned_of_int n  by metis
    moreover have "of_nat (nat (take_bit 64 (uint i))) = ((ucast ((word_of_int (uint i))::u64)))"
      using unsigned_of_int m  by metis 
    
    moreover have "take_bit 32 (uint i) = take_bit 64 (uint i)"
      by (smt (verit) Suc_1 bintr_uint len_bit0 len_signed m mult_le_mono mult_numeral_left_semiring_numeral n not_less_eq_eq numeral_Bit0_eq_double numeral_le_one_iff numeral_times_numeral semiring_norm(69) verit_comp_simplify1(2))
 
    then have "of_nat (nat (take_bit 32 (uint i))) = of_nat (nat (take_bit 64 (uint i)))"
      by auto
    ultimately show ?thesis by metis
  qed
  finally show ?thesis by auto
qed


end