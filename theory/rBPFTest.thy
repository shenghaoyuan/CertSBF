theory rBPFTest
imports
  Main
  rBPFCommType
begin

lemma [simp]: "and 15 (rex >> 4) = (4::u8) \<Longrightarrow> n < 8 \<Longrightarrow> bit 64 n \<Longrightarrow> bit rex n"
(*
proof -
  assume H: "and 15 (rex >> 4) = (4::u8)"
  show "n < 8 \<Longrightarrow> bit 64 n \<Longrightarrow> bit rex n"
  proof -
    have "\<forall>n. possible_bit TYPE(8 word) n \<longrightarrow> bit (and 15 (rex >> 4)) n \<longleftrightarrow> bit 4 n"
      using H bit_eq_iff by can not solver *)

(*
  apply (simp add: bit_eq_iff) (**r I get this dependent type? `\<forall>n<8.` *)
  apply (auto simp add: bit_simps)
*)
  sorry

end