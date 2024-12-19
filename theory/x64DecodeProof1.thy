theory x64DecodeProof1
imports
  Main (*"HOL-Eisbach.Eisbach" *)
  rBPFCommType x86CommType
  x64Assembler x64Disassembler
begin

lemma list_nth_right: "v = l!n \<Longrightarrow> l!n = v" using HOL.sym by simp

lemma if_false_eq: "a \<noteq> b \<Longrightarrow> (if a = b then c else d) = d" using HOL.if_not_P
  by argo 

lemma construct_rex_to_u8_eq_64:
  " construct_rex_to_u8 b0 b1 b2 b3 = 64 \<Longrightarrow>
      b0 = False \<and> b1 = False \<and> b2 = False \<and> b3 = False"
  apply (unfold construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_of_bool_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_neq_64:
  "construct_rex_to_u8 b0 b1 b2 b3 \<noteq> 64 \<Longrightarrow>
    bitfield_extract_u8 0 4 (construct_rex_to_u8 b0 b1 b2 b3) \<noteq> 0"
  apply (unfold construct_rex_to_u8_def bitfield_insert_u8_def bitfield_extract_u8_def Let_def u8_of_bool_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_neq_64_1:
  "construct_rex_to_u8 b0 b1 b2 b3 \<noteq> 64 \<Longrightarrow>
    b0 = True \<or> b1 = True \<or> b2 = True \<or> b3 = True"
  apply (unfold construct_rex_to_u8_def bitfield_insert_u8_def bitfield_extract_u8_def Let_def u8_of_bool_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_range:
  "0x40 \<le> construct_rex_to_u8 b0 b1 b2 b3 \<and> construct_rex_to_u8 b0 b1 b2 b3 \<le> 0x4f"
  apply (unfold construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_of_bool_def)
  apply (cases b0; cases b1; cases b2; cases b3; simp)
  done

lemma construct_rex_to_u8_range_outside [simp]:
  "v < 0x40 \<or> v > 0x4f \<Longrightarrow> construct_rex_to_u8 b0 b1 b2 b3 \<noteq> v"
  using construct_rex_to_u8_range
  using linorder_not_less by blast

lemma bitfield_extract_u8_construct_rex_to_u8_4 [simp]:
  " v = construct_rex_to_u8 b0 b1 b2 b3 \<Longrightarrow>
    bitfield_extract_u8 4 4 v = 4"
  apply (unfold construct_rex_to_u8_def, simp add: bitfield_simps)
  apply (simp add: bitfield_extract_u8_def)
  done

lemma ireg_of_u8_bitfield_extract_u8_u8_of_ireg_same [bitfield_simps]:
  "ireg_of_u8 (bitfield_extract_u8 0 4 (u8_of_ireg r)) = Some r"
  by (cases r; simp add: bitfield_extract_u8_def ireg_of_u8_def)

lemma nat_3_plus_1: "3 + 1 = (4::nat)" by simp

lemma ireg_of_u8_extract_3_some [bitfield_simps]:
  " (bitfield_extract_u8 3 1 (u8_of_ireg r) \<noteq> 0) = False \<Longrightarrow>
      ireg_of_u8 (bitfield_extract_u8 0 3 (u8_of_ireg r)) = Some r"
  by (cases r; simp add: bitfield_extract_u8_def ireg_of_u8_def)

lemma x64_encode_decode_consistency:
  "list_in_list l_bin pc l \<Longrightarrow> Some l_bin = x64_encode ins \<Longrightarrow>
    x64_decode pc l = Some (length l_bin, ins)"
  apply (cases ins; simp add: Let_def)

  subgoal for rd rs
    apply (simp add: split: if_split_asm; erule conjE)
    subgoal
      apply (drule construct_rex_to_u8_eq_64; erule conjE; erule conjE; erule conjE)
      apply (drule HOL.sym [of _ "l ! Suc pc"])
      apply (simp only: x64_decode_def Let_def)
      apply (subst if_not_P, simp)
      apply (subst if_not_P, simp)
      apply (subst if_not_P, simp)
      apply (subst if_not_P [of "137 = 102"], simp)
      apply (subst if_P [of "bitfield_extract_u8 4 4 137 \<noteq> 4"], simp add: bitfield_extract_u8_def)
      apply (subst if_not_P [of "bitfield_extract_u8 3 5 137 = 10"], simp add: bitfield_extract_u8_def)
      apply (subst if_not_P [of "bitfield_extract_u8 3 5 137 = 11"], simp add: bitfield_extract_u8_def)
      apply (subst if_not_P [of "137 = 15"], simp)
      apply (subst if_not_P, simp)
      apply (subst if_not_P, simp)
      apply (subst if_P [of "137 = 137"], simp)
      apply (simp only: Nat.One_nat_def[symmetric])
      apply (simp only: Nat.Suc_eq_plus1 construct_modsib_to_u8_def bitfield_simps)
      apply (subst if_P [of "bitfield_extract_u8 0 2 3 = 3"], simp add: bitfield_extract_u8_def)
      apply (simp add: case_optionE bitfield_simps)
      done
    subgoal
      apply (erule conjE)
      apply (drule HOL.sym [of _ "l ! Suc (Suc pc)"])
      apply (simp only: x64_decode_def Let_def)
      apply (subst if_not_P [of "l ! pc = 144"], drule HOL.sym [of _ "l ! pc"], simp)
      apply (subst if_not_P [of "l ! pc = 153"], drule HOL.sym [of _ "l ! pc"], simp)
      apply (subst if_not_P [of "l ! pc = 195"], drule HOL.sym [of _ "l ! pc"], simp)
      apply (subst if_not_P [of "l ! pc = 102"], drule HOL.sym [of _ "l ! pc"], simp)
      apply (subst if_not_P [of "l ! pc = 15"], drule HOL.sym [of _ "l ! pc"], simp)
      apply (subst if_not_P [of "bitfield_extract_u8 4 4 (l ! pc) \<noteq> 4"], drule HOL.sym [of _ "l ! pc"], simp)
      apply (subst if_not_P [of "bitfield_extract_u8 0 4 (l ! pc) = 0"], metis construct_rex_to_u8_neq_64)
      apply (subst if_not_P [of "l ! (pc + 1) = 153"], simp)
      apply (subst if_not_P [of "bitfield_extract_u8 3 5 (l ! (pc + 1)) = 10"], simp add: bitfield_extract_u8_def)
      apply (subst if_not_P [of "bitfield_extract_u8 3 5 (l ! (pc + 1)) = 11"], simp add: bitfield_extract_u8_def)
      apply (subst if_not_P [of "bitfield_extract_u8 3 5 (l ! (pc + 1)) = 23"], simp add: bitfield_extract_u8_def)
      apply (subst if_not_P [of "l ! (pc + 1) = 104"], simp)
      apply (subst if_not_P [of "l ! (pc + 1) = 15"], simp)
      apply (subst if_P [of "l ! (pc + 1) = 137"], simp)
      apply (simp only: construct_modsib_to_u8_def)
      apply (subst if_P [of "bitfield_extract_u8 6 2 (l ! (pc + 2)) = 3"], simp add: bitfield_simps, simp add: bitfield_extract_u8_def)
      apply (drule HOL.sym [of _ "l ! pc"])
      apply (insert construct_rex_to_u8_neq_64_1)
      apply (simp only: construct_rex_to_u8_def Num.add_2_eq_Suc'[symmetric] bitfield_simps nat_3_plus_1)
      apply (subst if_not_P, simp)
      apply (subst if_P [of "bitfield_extract_u8 0 1 (u8_of_bool False) = 0 \<and> bitfield_extract_u8 0 1 (u8_of_bool False) = 0"], simp add: bitfield_extract_u8_def u8_of_bool_def)
      apply (subst if_not_P [of "bitfield_extract_u8 3 1 (u8_of_ireg rs) = 0 \<and> bitfield_extract_u8 3 1 (u8_of_ireg rd) = 0"], simp)
      apply (metis u8_of_bool_false)
      apply (simp add: case_optionE)
      done
    done


      value "bitfield_extract_u8 0 1 (u8_of_bool False) = 0 \<and> bitfield_extract_u8 0 1 (u8_of_bool False) = 0"
      find_theorems "Suc (Suc ?a)"
      value "bitfield_extract_u8 0 2 3 = 3"

(*
    apply (cases ins; simp add: Let_def construct_rex_to_u8_neq_144) *)
(*
  apply (subst if_false_eq, simp) *)



end