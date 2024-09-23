section \<open> Interpreter of Solana rBPF \<close>

theory Interpreter
imports
  Main
  rBPFCommType rBPFSyntax vm_state vm Mem
  ebpf rBPFDecoder
begin

subsubsection  \<open> Interpreter State \<close>

type_synonym reg_map = "bpf_preg \<Rightarrow> u64"

record stack_state = 
call_depth :: u64
stack_pointer :: u64
call_frames :: "CallFrame list"

(*
record rbpf_state =
registers :: reg_map
memory_mapping :: mem
stack :: stack_state *)

datatype bpf_state =
  BPF_OK reg_map mem stack_state SBPFV u64 u64 | (**r normal state *)
  BPF_Success u64 |
  BPF_EFlag | (**r find bugs at runtime *)
  BPF_Err (**r bad thing *)

datatype 'a option2 =
  NOK |
  OKS (the: 'a) |
  OKN  

definition eval_reg :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> u64" where
"eval_reg dst rs = rs (BR dst)"

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

definition eval_alu32_aux1 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_alu32_aux1 bop dst sop rs is_v1 = (
  let dv :: i32 = scast (eval_reg dst rs) in (
  let sv :: i32 = eval_snd_op_i32 sop rs in (
  case bop of
  BPF_ADD \<Rightarrow> OKS (rs#(BR dst) <-- (ucast (dv + sv))) |
  BPF_SUB \<Rightarrow> (case sop of (SOReg i) \<Rightarrow> OKS (rs#(BR dst) <-- (ucast (dv - sv))) |
                           _ \<Rightarrow> (if is_v1 then OKS (rs#(BR dst) <-- (ucast (dv - sv))) 
                                else OKS (rs#(BR dst) <-- (ucast (sv - dv))))) |
  BPF_MUL \<Rightarrow> OKS (rs#(BR dst) <-- (ucast (dv * sv))) |
  _ \<Rightarrow> OKN
)))"

definition eval_alu32_aux2 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_alu32_aux2 bop dst sop rs = (
  let dv :: u32 = ucast (eval_reg dst rs) in (
  let sv :: u32 = eval_snd_op_u32 sop rs in (
  case bop of
  BPF_DIV \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                       else OKS (rs#(BR dst) <-- (ucast (dv div sv))) |
  BPF_OR  \<Rightarrow> OKS (rs#(BR dst) <-- (ucast (or dv sv))) |
  BPF_AND \<Rightarrow> OKS (rs#(BR dst) <-- (ucast (and dv sv))) |
  BPF_MOD \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                       else OKS (rs#(BR dst) <-- (ucast (dv mod sv))) |
  BPF_XOR \<Rightarrow> OKS (rs#(BR dst) <-- (ucast (xor dv sv))) |
  BPF_MOV \<Rightarrow> OKS (rs#(BR dst) <-- (ucast sv)) |
  BPF_LSH \<Rightarrow> OKS (rs#(BR dst) <-- (ucast (dv << unat sv))) |
  BPF_RSH \<Rightarrow> OKS (rs#(BR dst) <-- (ucast (dv >> unat sv))) |
  _ \<Rightarrow> OKN
)))"

definition eval_alu32_aux3 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_alu32_aux3 bop dst sop rs  = (
  let dv :: i32 = scast (eval_reg dst rs) in (
  let sv :: u32 = eval_snd_op_u32 sop rs in (
  case bop of
  BPF_ARSH \<Rightarrow> OKS (rs#(BR dst) <-- (and (ucast (dv << unat sv)::u64) (ucast u32_MAX)) ) | 
  _ \<Rightarrow> OKN
)))"

definition eval_alu32 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_alu32 bop dst sop rs is_v1 = (
  case bop of
  BPF_ADD   \<Rightarrow> eval_alu32_aux1 bop dst sop rs is_v1 |
  BPF_SUB   \<Rightarrow> eval_alu32_aux1 bop dst sop rs is_v1 |
  BPF_MUL   \<Rightarrow> if is_v1 then eval_alu32_aux1 bop dst sop rs is_v1 else OKN  |
  BPF_DIV   \<Rightarrow> if is_v1 then eval_alu32_aux2 bop dst sop rs else OKN  |
  BPF_OR    \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_AND   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_MOD   \<Rightarrow> if is_v1 then eval_alu32_aux2 bop dst sop rs else OKN  |
  BPF_XOR   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_MOV   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_LSH   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_RSH   \<Rightarrow> eval_alu32_aux2 bop dst sop rs  |
  BPF_ARSH  \<Rightarrow> eval_alu32_aux3 bop dst sop rs 
)"

definition eval_alu64_aux1 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_alu64_aux1 bop dst sop rs is_v1 = (
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u64 = eval_snd_op_u64 sop rs in (
  case bop of
  BPF_ADD \<Rightarrow> OKS (rs#(BR dst) <-- (dv+sv)) |
  BPF_SUB \<Rightarrow> (case sop of (SOReg i) \<Rightarrow> OKS (rs#(BR dst) <-- (dv - sv)) |
                           _ \<Rightarrow> (if is_v1 then OKS (rs#(BR dst) <-- (dv - sv)) 
                                else OKS (rs#(BR dst) <-- (sv - dv)))) |
  BPF_MUL \<Rightarrow> OKS (rs#(BR dst) <-- (dv * sv)) |
  BPF_DIV \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                       else OKS (rs#(BR dst) <-- (dv div sv)) |
  BPF_OR  \<Rightarrow> OKS (rs#(BR dst) <-- (or dv sv)) |
  BPF_AND \<Rightarrow> OKS (rs#(BR dst) <-- (and dv sv)) |
  BPF_MOD \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                       else OKS (rs#(BR dst) <-- (dv mod sv)) |
  BPF_XOR \<Rightarrow> OKS (rs#(BR dst) <-- (xor dv sv)) |
  BPF_MOV \<Rightarrow> OKS (rs#(BR dst) <-- sv) |
  _ \<Rightarrow> OKN
)))"


definition eval_alu64_aux2 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_alu64_aux2 bop dst sop rs = (
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u32 = eval_snd_op_u32 sop rs in (
  case bop of
  BPF_LSH \<Rightarrow> OKS (rs#(BR dst) <-- (dv << unat sv)) |  \<comment> \<open> to unat \<close>
  BPF_RSH \<Rightarrow> OKS (rs#(BR dst) <-- (dv >> unat sv)) |  \<comment> \<open> to unat \<close>
  _ \<Rightarrow> OKN
)))" 

definition eval_alu64_aux3 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_alu64_aux3 bop dst sop rs = (
  let dv :: i64 = scast (eval_reg dst rs) in (
  let sv :: u32 = eval_snd_op_u32 sop rs in (
  case bop of
  BPF_ARSH \<Rightarrow> OKS (rs#(BR dst) <-- (ucast (dv >> unat sv)::u64)) |
  _ \<Rightarrow> OKN
)))"

definition eval_add64_imm_R10 :: "imm_ty \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> stack_state option" where
"eval_add64_imm_R10 i ss is_v1 = (
  let sp = stack_pointer ss in 
    if \<not>is_v1 then
      Some (ss\<lparr>stack_pointer := sp+(ucast i)\<rparr>)
    else
      None
)"

definition eval_alu64 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_alu64 bop dst sop rs is_v1 = (
  case bop of
  BPF_ADD   \<Rightarrow> eval_alu64_aux1 bop dst sop rs is_v1 |
  BPF_SUB   \<Rightarrow> eval_alu64_aux1 bop dst sop rs is_v1 |
  BPF_MUL   \<Rightarrow> if is_v1 then eval_alu64_aux1 bop dst sop rs is_v1 else OKN |
  BPF_DIV   \<Rightarrow> if is_v1 then eval_alu64_aux1 bop dst sop rs is_v1 else OKN |
  BPF_OR    \<Rightarrow> eval_alu64_aux1 bop dst sop rs is_v1 |
  BPF_AND   \<Rightarrow> eval_alu64_aux1 bop dst sop rs is_v1 |
  BPF_MOD   \<Rightarrow> if is_v1 then eval_alu64_aux1 bop dst sop rs is_v1 else OKN |
  BPF_XOR   \<Rightarrow> eval_alu64_aux1 bop dst sop rs is_v1 |
  BPF_MOV   \<Rightarrow> eval_alu64_aux1 bop dst sop rs is_v1 |
  BPF_LSH   \<Rightarrow> eval_alu64_aux2 bop dst sop rs |
  BPF_RSH   \<Rightarrow> eval_alu64_aux2 bop dst sop rs |
  BPF_ARSH  \<Rightarrow> eval_alu64_aux3 bop dst sop rs
)"

definition eval_neg32 :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_neg32 dst rs is_v1 = (if is_v1 then (let dv::i32 = scast (eval_reg dst rs) in 
    OKS ( rs#(BR dst) <-- (and (ucast(-dv)::u64) (ucast u32_MAX))) )
  else OKN
)"

definition eval_neg64 :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_neg64 dst rs is_v1 = (if is_v1 then (let dv::i64 = scast (eval_reg dst rs) in 
    OKS ( rs#(BR dst) <-- (ucast(-dv)::u64)) )
  else OKN
)"

definition eval_le :: "dst_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_le dst imm rs is_v1 = (
  if is_v1 then (
    let dv = eval_reg dst rs in ((
      if imm = 16 then
        case (u16_of_u8_list (u8_list_of_u16 (ucast dv))) of
        None \<Rightarrow> OKN |
        Some v \<Rightarrow> OKS (rs#(BR dst) <-- (ucast v))
      else if imm = 32 then
        case u32_of_u8_list (u8_list_of_u32 (ucast dv)) of
        None \<Rightarrow> OKN |
        Some v \<Rightarrow> OKS (rs#(BR dst) <-- (ucast v))
      else if imm = 64 then
        case u64_of_u8_list (u8_list_of_u64 dv) of
        None \<Rightarrow> OKN |
        Some v \<Rightarrow> OKS (rs#(BR dst) <-- v)
      else OKN )))
  else OKN
)"

definition eval_be :: "dst_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_be dst imm rs is_v1 = (
  if is_v1 then (
    let dv = eval_reg dst rs in ((
      if imm = 16 then
        case (u16_of_u8_list (rev (u8_list_of_u16 (ucast dv)))) of
        None \<Rightarrow> OKN |
        Some v \<Rightarrow> OKS (rs#(BR dst) <-- (ucast v))
      else if imm = 32 then
        case (u32_of_u8_list (rev (u8_list_of_u32 (ucast dv)))) of
        None \<Rightarrow> OKN |
        Some v \<Rightarrow> OKS (rs#(BR dst) <-- (ucast v))
      else if imm = 64 then
        case u64_of_u8_list (rev (u8_list_of_u64 (ucast dv))) of
        None \<Rightarrow> OKN |
        Some v \<Rightarrow> OKS (rs#(BR dst) <-- v)
      else OKN)))
  else OKN
)"

definition eval_hor64 :: "dst_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_hor64 dst imm rs is_v1 = (
  if is_v1 then (
    let dv::u64 = eval_reg dst rs; dv2 = or dv (((ucast imm)::u64) << 32) in 
      OKS (rs#(BR dst) <-- dv2))
  else OKN
)"

subsection  \<open> PQR \<close>

definition eval_pqr32_aux1 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_pqr32_aux1 pop dst sop rs  = (
  let dv :: i32 = scast (eval_reg dst rs) in (
  let sv :: i32 = eval_snd_op_i32 sop rs in (
  case pop of
  BPF_LMUL \<Rightarrow> OKS (rs#(BR dst) <-- (ucast (dv * sv))) |
  BPF_SDIV \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#(BR dst) <-- (ucast (dv div sv))) |
  BPF_SREM \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#(BR dst) <-- (ucast (dv mod sv))) |
  _ \<Rightarrow> OKN
)))"

definition eval_pqr32_aux2 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_pqr32_aux2 pop dst sop rs = (
  let dv :: u32 = ucast (eval_reg dst rs) in (
  let sv :: u32 = eval_snd_op_u32 sop rs in (
  case pop of
  BPF_UDIV \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#(BR dst) <-- (ucast (dv div sv))) |
  BPF_UREM \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#(BR dst) <-- (ucast (dv mod sv))) |
  _ \<Rightarrow> OKN
)))"

definition eval_pqr32 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_pqr32 pop dst sop rs is_v1 = (
  if is_v1 then OKN else(
  case pop of
  BPF_LMUL \<Rightarrow> eval_pqr32_aux1 pop dst sop rs  |
  BPF_UDIV \<Rightarrow> eval_pqr32_aux2 pop dst sop rs  | 
  BPF_UREM \<Rightarrow> eval_pqr32_aux2 pop dst sop rs  | 
  BPF_SDIV \<Rightarrow> eval_pqr32_aux1 pop dst sop rs  |
  BPF_SREM \<Rightarrow> eval_pqr32_aux1 pop dst sop rs 
))"

definition eval_pqr64_aux1 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_pqr64_aux1 pop dst sop rs  = (
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u64 = eval_snd_op_u64 sop rs in (
  case pop of
  BPF_LMUL \<Rightarrow> OKS (rs#(BR dst) <-- (ucast (dv * sv))) |  
  BPF_UDIV \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#(BR dst) <-- (ucast (dv div sv))) | 
  BPF_UREM \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#(BR dst) <-- (ucast (dv mod sv)))  
)))"

definition eval_pqr64_aux2 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option2" where
"eval_pqr64_aux2 pop dst sop rs = (
  let dv :: i64 = scast (eval_reg dst rs) in (
  let sv :: i64 = eval_snd_op_i64 sop rs in (
  case pop of
  BPF_SDIV \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#(BR dst) <-- (ucast (dv div sv))) | 
  BPF_SREM \<Rightarrow> if sv = 0 then (case sop of SOImm _ \<Rightarrow> NOK | _ \<Rightarrow> OKN)
                        else OKS (rs#(BR dst) <-- (ucast (dv mod sv)))   
)))"

definition eval_pqr64 :: "pqrop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_pqr64 pop dst sop rs is_v1 = (
  if is_v1 then OKN else(
  case pop of
  BPF_LMUL \<Rightarrow> eval_pqr64_aux1 pop dst sop rs |  
  BPF_UDIV \<Rightarrow> eval_pqr64_aux1 pop dst sop rs | 
  BPF_UREM \<Rightarrow> eval_pqr64_aux1 pop dst sop rs | 
  BPF_SDIV \<Rightarrow> eval_pqr64_aux2 pop dst sop rs | 
  BPF_SREM \<Rightarrow> eval_pqr64_aux2 pop dst sop rs   
))"

definition eval_pqr64_2 :: "pqrop2 \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option2" where
"eval_pqr64_2 pop2 dst sop rs is_v1 = (
  if is_v1 then OKN else(
  let dv_u :: u128 = ucast (eval_reg dst rs) in (
  let sv_u :: u128 = ucast (eval_snd_op_u64 sop rs) in (
  let dv_i :: u128 = ucast (scast (eval_reg dst rs)::i64) in (
  let sv_i :: u128 = ucast (scast (eval_reg dst rs)::i64) in (
  case pop2 of
  BPF_UHMUL \<Rightarrow> OKS (rs#(BR dst) <-- (ucast (dv_u * sv_u)>>64)) |
  BPF_SHMUL \<Rightarrow> OKS (rs#(BR dst) <-- (ucast (dv_i * sv_i)>>64)) 
))))))"

subsection  \<open> MEM \<close>

definition eval_store :: "memory_chunk \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> off_ty \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> mem option" where
"eval_store chk dst sop off rs mem = (
  let dv :: i64 = scast (eval_reg dst rs) in (
  let vm_addr :: u64 = ucast (dv + (scast off)) in (  
  let sv :: u64 = eval_snd_op_u64 sop rs in ( \<comment> \<open> TODO: sv is signed for imm and unsigned for src reg? \<close>
  (storev chk mem (Vlong vm_addr) (Vlong sv))
))))"


definition eval_load :: "memory_chunk \<Rightarrow> dst_ty \<Rightarrow> src_ty \<Rightarrow> off_ty \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> reg_map option" where
"eval_load chk dst sop off rs mem = (
  let sv :: u64 = eval_snd_op_u64 (SOReg sop) rs in (
  let vm_addr :: u64 = sv + (scast off) in (  
  let v = (loadv chk mem (Vlong vm_addr)) in (
     case v of None \<Rightarrow> None |
               Some Vundef \<Rightarrow>  None | 
               Some (Vlong v) \<Rightarrow>  Some (rs#(BR dst) <-- v) |
               Some (Vint v) \<Rightarrow> Some (rs#(BR dst) <-- (ucast v))|
               _ \<Rightarrow> None
))))"

(*definition store_mem::"mem_len \<Rightarrow> i64 \<Rightarrow> usize \<Rightarrow> mem \<Rightarrow> mem" where  
"store_mem len v vm_addr mem = mem (vm_addr := Some ((ucast v)::u64))" 

definition eval_store :: "chunk \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> off_ty \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> mem option" where
"eval_store chk dst sop off rs mem = (
  let dv :: i64 = scast (eval_reg dst rs) in (
  let vm_addr :: u64 = ucast (dv + (ucast off)) in (  
  let sv :: i64 = eval_snd_op_i64 sop rs in (
  let size = case chk of Byte \<Rightarrow> u8 | HalfWord \<Rightarrow> u16 | SWord \<Rightarrow> u32 | DWord \<Rightarrow> u64 in (
  Some (store_mem size sv vm_addr mem)
)))))"

definition load_mem::"mem_len \<Rightarrow> usize \<Rightarrow> mem \<Rightarrow> u64 option" where
"load_mem len vm_addr mem = (mem vm_addr)"

definition eval_load :: "chunk \<Rightarrow> dst_ty \<Rightarrow> src_ty \<Rightarrow> off_ty \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> reg_map option" where
"eval_load chk dst sop off rs mem = (
  let sv :: i64 = eval_snd_op_i64 (SOReg sop) rs in (
  let vm_addr :: u64 = ucast (sv + (ucast off)) in ( 
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

definition push_frame:: "reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> stack_state option \<times> reg_map" where 
"push_frame rs ss is_v1 = (let pc = eval_pc rs +1; fp = eval_reg BR10 rs ;
  frame = \<lparr>frame_pointer = pc, target_pc = fp\<rparr> in 
  let update1 = call_depth ss +1 in (if update1 = max_call_depth then (None, rs) else (
  let update2 = if is_v1 then (if enable_stack_frame_gaps then stack_pointer ss + stack_frame_size *2
  else stack_pointer ss + stack_frame_size) else stack_pointer ss;  
  update3 = (call_frames ss)[unat(call_depth ss):= frame] in
  let stack = Some \<lparr>call_depth = update1, stack_pointer = update2, call_frames = update3\<rparr>;
  reg = rs#(BR BR10) <-- update2 in (stack,reg)
)))"

definition eval_call_reg :: "src_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> (reg_map \<times> stack_state) option" where
"eval_call_reg src imm rs ss is_v1 = (
  case u4_to_bpf_ireg (ucast imm) of
  None \<Rightarrow> None |
  Some iv \<Rightarrow> (
    let pc = if is_v1 then eval_reg iv rs else eval_reg src rs in  
    let (x, rs') = push_frame rs ss is_v1 in
      case x of
      None \<Rightarrow> None |
      Some ss' \<Rightarrow> 
        if pc < program_vm_addr then None else (
          let next_pc = (pc - program_vm_addr)div (of_nat INSN_SIZE) in 
            case get_function_registry (ucast next_pc) of
            None \<Rightarrow> None | 
            Some _ => Some (rs'#BPC <-- next_pc, ss')
          ))
)"

definition eval_call_imm :: "imm_ty \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> (reg_map \<times> stack_state) option" where
"eval_call_imm imm rs ss is_v1 = (
  case get_function_registry (ucast imm) of
  None \<Rightarrow> None |
  Some pc \<Rightarrow> (
    let (x, rs') = push_frame rs ss is_v1 in (
      case x of
      None \<Rightarrow> None |
      Some ss' \<Rightarrow> Some (rs'#BPC <-- pc, ss')
    ))
)"

definition pop_frame:: "stack_state \<Rightarrow> CallFrame" where 
"pop_frame ss = (call_frames ss)!(unat (call_depth ss)) "

subsection  \<open> EXIT \<close>
                                       
definition eval_exit :: "reg_map \<Rightarrow> stack_state \<Rightarrow> bool \<Rightarrow> (reg_map \<times> stack_state)" where
"eval_exit rs ss is_v1 = (
    let x = call_depth ss-1 ; frame = pop_frame ss; rs'= rs#(BR BR10) <-- (frame_pointer frame) in 
    let y =  if is_v1 then (stack_pointer ss - (2 * stack_frame_size)) else stack_pointer ss; 
     z = butlast (call_frames ss) ; ss' = \<lparr>call_depth = x, stack_pointer= y, call_frames = z\<rparr> in
     let pc = target_pc frame; rs' = rs'#BPC <-- pc in 
      (rs',ss')
)"

subsection  \<open> step \<close>

fun step :: "bpf_instruction \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> stack_state \<Rightarrow> SBPFV \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> bpf_state" where
"step ins rs m ss sv cur_cu remain_cu = ( let is_v1 = (case sv of V1 \<Rightarrow> True | _ \<Rightarrow> False) in
  case ins of
  BPF_ALU bop d sop \<Rightarrow> (
    case eval_alu32 bop d sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (rs'#BPC <-- (1 + (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_ALU64 bop d sop \<Rightarrow> (
    case eval_alu64 bop d sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_ADD_STK i \<Rightarrow> (
    case eval_add64_imm_R10 i ss is_v1 of
    None \<Rightarrow> BPF_Err |
    Some ss' \<Rightarrow> BPF_OK (rs#BPC <-- (1+ (rs BPC))) m ss' sv cur_cu remain_cu) |

  BPF_LE dst imm \<Rightarrow> (
    case eval_le dst imm rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_BE dst imm \<Rightarrow> (
    case eval_be dst imm rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_NEG32_REG dst \<Rightarrow> (
    case eval_neg32 dst rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_NEG64_REG dst \<Rightarrow> (
    case eval_neg64 dst rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_LDX chk dst sop off \<Rightarrow> (
    case eval_load chk dst sop off rs m of
    None \<Rightarrow> BPF_EFlag |
    Some rs' \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_ST chk dst sop off \<Rightarrow> (
    case eval_store chk dst sop off rs m of
    None \<Rightarrow> BPF_EFlag |
    Some m' \<Rightarrow> BPF_OK (rs#BPC <-- (1+ (rs BPC))) m' ss sv cur_cu remain_cu) |

  BPF_LD_IMM dst imm1 imm2  \<Rightarrow> (
    case eval_load_imm dst imm1 imm2 rs m of
    None \<Rightarrow> BPF_EFlag |
    Some rs' \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_PQR pop dst sop \<Rightarrow> (
    case eval_pqr32 pop dst sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_PQR64 pop dst sop \<Rightarrow> (
    case eval_pqr64 pop dst sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_PQR2 pop dst sop \<Rightarrow> (
    case eval_pqr64_2 pop dst sop rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_HOR64_IMM dst imm \<Rightarrow> (
    case eval_hor64 dst imm rs is_v1 of
    NOK \<Rightarrow> BPF_Err |
    OKN \<Rightarrow> BPF_EFlag |
    OKS rs' \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_JA off_ty  \<Rightarrow> (
    let rs'= rs (BPC := eval_pc rs + ucast off_ty) in
      BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_JUMP cond bpf_ireg snd_op off_ty  \<Rightarrow> (
    case eval_jmp cond bpf_ireg snd_op rs off_ty of
    None \<Rightarrow> BPF_EFlag |
    Some rs' \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss sv cur_cu remain_cu) |

  BPF_CALL_IMM src imm \<Rightarrow> (
    case eval_call_imm imm rs ss is_v1  of
    None \<Rightarrow> BPF_EFlag |
    Some (rs', ss') \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss' sv cur_cu remain_cu) | \<comment> \<open> TODO \<close>

  BPF_CALL_REG src imm \<Rightarrow> (
    case eval_call_reg src imm rs ss is_v1  of
    None \<Rightarrow> BPF_EFlag |
    Some (rs', ss') \<Rightarrow> BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss' sv (cur_cu+1) remain_cu) |
  BPF_EXIT \<Rightarrow> (
    if call_depth ss = 0 then
      BPF_Success (rs (BR BR1))
    else (
      let (rs', ss') = eval_exit rs ss is_v1 in
        BPF_OK (rs'#BPC <-- (1+ (rs' BPC))) m ss' sv cur_cu remain_cu))
)"

fun bpf_interp :: "nat \<Rightarrow> bpf_bin \<Rightarrow> bpf_state \<Rightarrow> bpf_state" where
"bpf_interp 0 _ _ = BPF_EFlag" | 
"bpf_interp (Suc n) prog st = (
  case st of
  BPF_EFlag \<Rightarrow> BPF_EFlag |
  BPF_Err \<Rightarrow> BPF_Err |
  BPF_Success v \<Rightarrow> BPF_Success v |
  BPF_OK rs m ss sv cur_cu remain_cu \<Rightarrow> (
    if unat (rs BPC) < length prog then
      if cur_cu \<ge> remain_cu then
        BPF_EFlag
      else
        case bpf_find_instr (unat (rs BPC)) prog of
        None \<Rightarrow> BPF_Err |
        Some ins \<Rightarrow> bpf_interp n prog (step ins rs m ss sv (cur_cu+1) remain_cu)
    else BPF_Err))"


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



value "ucast (-1::i8)::u8"
value "-1::u8"
value "-1::i8"
value "scast(-1::u8)::i8"
lemma "\<exists> x y. ((scast(x::u8))::i8) + ((scast(y::u8))::i8) = (scast(x+y)::i8)"
  by (metis (no_types, lifting) of_int_add scast_nop1)

lemma "\<forall> x y. ((scast(x::u8))::i8) + ((scast(y::u8))::i8) = (scast(x+y)::i8)"
  by (metis (mono_tags, opaque_lifting) of_int_add of_int_sint scast_id scast_nop2 scast_scast_id(2))

lemma "\<exists> x y. ((ucast(x::i8))::u8) + ((ucast(y::i8))::u8) = (ucast(x+y)::u8)"
  by (metis add_0 unsigned_0)

value "((ucast(-1::i8))::u64) + ((ucast(-2::i8))::u64) "
value "(ucast(-3::i8)::u8)"

(*
lemma "((ucast(-1::i8))::u8) + ((ucast(-2::i8))::u8) \<noteq> (ucast(-3::i8)::u8)"
  try

lemma "\<exists> x y. ((ucast(x::i8))::u8) + ((ucast(y::i8))::u8) \<noteq> (ucast(x+y)::u8)"
  try *)

value "of_nat 101::nat"

value "take_bit 64 (uint (1111111111111111111111111111111111111111::u32)) "
value "take_bit 32 (uint (1111111111111111111111111111111111111111::u32))"
value "signed_take_bit 32 3::u32"

value "(ucast(-1::u32)::u64) + ucast(-2::u32)::u64"
value "(ucast(-3::u32)::u64)"

value "(ucast(-1::i32)::u64) + ucast(-2::i32)::u64"
value "(ucast(-3::i32)::u64)"

value "(ucast(-1::i32)::u32) + ucast(-2::i32)::u32"
value "(ucast(-3::i32)::u32)"

value "(scast(-1::u32)::i64) + scast(-2::u32)::i64"
value "(scast(-3::u32)::i64)"



value "(scast(-1::i32)::i8) + scast(-2::i32)::i8"

value "(scast(-3::u32)::i8)"

value "(scast(-1::u32)::u64)"


lemma cast_lemma1_1:"(uint((scast((ucast (n1::u32))::u64))::i32)) = uint((ucast (n1::u32))::u64)"
  sorry

lemma cast_lemma1:"(n3::u32)=(n1::u32) +(n2::u32)\<Longrightarrow> ((ucast n3)::u64) = ((ucast ((scast((ucast n1)::u64)::i32) +scast((ucast n2)::u64)::i32))::u64)"
  sorry


lemma cast_lemma2:"n3 = n1 + ucast (n2) \<Longrightarrow> ucast n3 = ucast (scast(ucast n1 )+ n2)"
  sorry

lemma cast_lemma3:"(x::u32) = (ucast(x::u32)::u32)"
  by simp

lemma cast_lemma4:"ucast off = scast (ucast off)"
  sorry


lemma cast_lemma5:"scast const = scast (scast const)"
  sorry


(*lemma cast_lemma6:"Vlong  = Vint const "*)
  

end