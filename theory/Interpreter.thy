section \<open> Interpreter of Solana rBPF \<close>

theory Interpreter
imports
  Main
  rBPFCommType rBPFSyntax
begin

text \<open> TBC \<close>


subsection  \<open> Interpreter State \<close>
text \<open> the state is a record including
- a list of rBPF instructions (maybe as global varaible of `step`)
- registers
- memory_model
- VM configuration
- ... \<close>

type_synonym reg_map = "bpf_preg \<Rightarrow> u64"

type_synonym mem = "(u64, u64) map"

record rbpf_state =
registers :: reg_map
memory_mapping :: mem

subsection  \<open> ALU \<close>
text \<open> ALU32 semantics \<close>

definition eval_reg :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> u64" where
"eval_reg dst rs = rs (BR dst)"

definition upd_reg :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> u64 \<Rightarrow> reg_map" where
"upd_reg dst rs v =  rs (BR dst := v)"

fun eval_snd_op :: "snd_op \<Rightarrow> reg_map \<Rightarrow> u64" where
"eval_snd_op (SOImm i) _ = (ucast) i" |
"eval_snd_op (SOReg r) rs = rs (BR r)"

definition eval_alu :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool \<Rightarrow> reg_map option" where
"eval_alu bop dst sop rs is_v1 = (
  let dv :: u32 = ucast (eval_reg dst rs) in (
  let sv :: u32 = ucast (eval_snd_op sop rs) in (
  case bop of
  BPF_ADD \<Rightarrow> Some (upd_reg dst rs (ucast (dv + sv))) |
  _ \<Rightarrow> None

)))"

(**r  | BPF_SUB | BPF_MUL | BPF_DIV | BPF_OR | BPF_AND |
  BPF_LSH | BPF_RSH | BPF_MOD | BPF_XOR | BPF_MOV | BPF_ARSH  *)

fun step :: "bpf_instruction \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> bool \<Rightarrow> rbpf_state option" where
"step ins rs m is_v1 = (
  case ins of
  BPF_ALU bop d sop \<Rightarrow> (
    case eval_alu bop d sop rs is_v1 of
      None \<Rightarrow> None |
      Some rs' \<Rightarrow> Some \<lparr> registers = rs', memory_mapping = m  \<rparr> ) |
  _ \<Rightarrow> None
  )
"

subsection  \<open> JUMP \<close>
subsection  \<open> MEM \<close>
subsection  \<open> CALL \<close>
subsection  \<open> EXIT \<close>
subsection  \<open> step \<close>

(*
value "((ucast ((ucast (-1::i32))::u64)) :: u32)"
value "((ucast (-1::i32))::u32)" *)

thm ucast_eq
declare [[show_types]]



lemma "((ucast ((ucast (i::i32))::u64)) :: u32) = ((ucast (i::i32))::u32)"
proof-
  
  have "((ucast ((ucast (i::i32))::u64)) :: u32) = ((ucast ((word_of_int (uint i))::u64)) :: u32) " 
    by auto
  also have "...  = ((ucast ((word_of_int (uint i))::u32)) :: u32)"
    (* sledgehammer gives this solution but reconstruction fails
        by (metis bintr_uint of_nat_nat_take_bit_eq ucast_id unsigned_of_int verit_comp_simplify1(2) *)
    using bintr_uint of_nat_nat_take_bit_eq order.refl ucast_id unsigned_of_int apply auto
    sorry
  finally show ?thesis by auto
qed


end