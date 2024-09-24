theory bpfConsistency
  imports bpfConsistencyAux
begin
(*
fun interp :: "nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
"interp 0 _ _ = Stuck" |
"interp (Suc n) l st = (
  case st of
  Stuck \<Rightarrow> Stuck |
  Next rs m \<Rightarrow> (
    case rs PC of
    Vlong v \<Rightarrow> (
      case x64_decode (unat v) l of
      None \<Rightarrow> Stuck |
      Some (sz, ins) \<Rightarrow>
        interp n l (exec_instr ins (of_nat sz) rs m)
      ) |
    _ \<Rightarrow> Stuck)
)"


fun bpf_interp :: "nat \<Rightarrow> bpf_bin \<Rightarrow> bpf_state \<Rightarrow> bpf_state" where
"bpf_interp 0 _ _ = BPF_EFlag" | 
"bpf_interp (Suc n) prog st = (
  case st of
  BPF_EFlag \<Rightarrow> BPF_EFlag |
  BPF_Err \<Rightarrow> BPF_Err |
  BPF_OK rs m ss conf sv \<Rightarrow> (
    if unat (rs BPC) < length prog then
      case bpf_find_instr (unat (rs BPC)) prog of
      None \<Rightarrow> BPF_Err |
      Some ins \<Rightarrow> bpf_interp n prog (step conf ins rs m ss sv)
    else BPF_Err))"


*)

(*datatype binop = BPF_ADD | BPF_SUB | BPF_MUL | BPF_DIV | BPF_OR | BPF_AND |
  BPF_LSH | BPF_RSH | BPF_MOD | BPF_XOR | BPF_MOV | BPF_ARSH *)



definition per_jit_ja :: "off_ty\<Rightarrow> x64_bin option" where
"per_jit_ja off = (
  let ins = Pjmp (ucast off) in
    x64_encode ins
)"



(*(the ()) *)

definition is_refined_state :: "bpf_state \<Rightarrow> outcome \<Rightarrow> bool" where
"is_refined_state bst xst = (case bst of BPF_OK rs m ss conf sv \<Rightarrow> 
                                case xst of Next reg mem \<Rightarrow> (\<forall> r. Vlong (rs (BR r)) = reg (IR (bpf_to_x64_reg r))) \<and> 
                                              m = mem |
                                      _ \<Rightarrow> False |
                             BPF_EFlag  \<Rightarrow> case xst of Stuck \<Rightarrow> True | _ \<Rightarrow> False |
                             _ \<Rightarrow> False)"

lemma consistency_proof_aux:
  assumes a0:"is_refined_state bst xst" and
    a1:"bst' = bpf_interp pc xbin bst" and
    a2:"per_jit_ins pc xbin = Some bl" and
    a3:"list_in_list bl pc l_bin" and
    a4:"x64_decode pc l_bin = Some (length l_bin, xins)" and
    a5:"xst' = interp pc bbin xst" 
  shows "is_refined_state bst' xst'"
  sorry






end