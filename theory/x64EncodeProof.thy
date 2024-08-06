theory x64EncodeProof
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler
  x64_encode_movl_rr_1 x64_encode_movl_rr_2 x64_encode_movl_rr_3
  x64_encode_movl_rr_4 x64_encode_movl_rr_5 x64_encode_movl_rr_6
begin

declare if_split_asm [split]

lemma x64_decode_encode_consistency:
  "list_in_list l_bin pc l \<Longrightarrow> x64_decode pc l = Some (length l_bin, ins) \<Longrightarrow> Some l_bin = x64_encode ins"
  apply (cases ins; simp_all)

  subgoal for dst src
  \<comment> \<open> Pmovl_rr \<close> 
    apply (unfold Let_def)
    apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (unfold x64_decode_def Let_def, auto simp add: split: option.splits)
    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for t l_bin2
          using encode_movl_rr_1 by blast
        done
      done

    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for t l_bin2
          using encode_movl_rr_2 by blast
        done
      done

      \<comment> \<open> prove False from context:
      - rex = 0: `bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg dst) 8 \<noteq> 0)) 0) (u8_of_bool (and (u8_of_ireg src) 8 \<noteq> 0))) 0 = 0`
      - but src > 8: `and 1 (l ! pc >> 2) \<noteq> 0` \<close> 
    subgoal
      using encode_movl_rr_3 by blast

    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for t l_bin3
            using encode_movl_rr_4 by blast
          done
        done
      done

    subgoal
      using encode_movl_rr_5 by blast

    subgoal
      apply (cases l_bin, simp_all)
      subgoal for l_bin1
        apply (cases l_bin1, simp_all)
        subgoal for l_bin2
          apply (cases l_bin2, simp_all)
          subgoal for t l_bin3
            using encode_movl_rr_6 by blast
          done
        done
      done

    done

  sorry

declare if_split_asm [split del]

end