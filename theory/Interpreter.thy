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