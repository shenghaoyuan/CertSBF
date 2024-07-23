theory x64ConsistencyProof2Aux0
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler
begin
declare if_split_asm [split]

lemma x64_disassemble_nil [simp]: "x64_disassemble l_bin = Some [] \<Longrightarrow> l_bin = []"
  apply (induction l_bin)
  subgoal by simp   \<comment> \<open> l_bin = [] \<close>
  subgoal for a l_bin  \<comment> \<open> l_bin = a#l_bin \<close>
    apply simp
    subgoal \<comment> \<open> Pnop \<close>
      apply (cases l_bin)
      subgoal by simp
      subgoal for b lb
        by (metis list.distinct(1) not_Some_eq option.simps(4) option.simps(5))
      done
    subgoal
      apply (unfold Let_def)
      apply (cases l_bin, simp_all)
      subgoal for b lb
        apply (cases lb, simp_all)
        subgoal for c lc
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)


          apply (cases "x64_disassemble lc", simp_all)
          done

        subgoal for c lc
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))"; cases "x64_disassemble lc", simp_all)
          done

        subgoal for c lc
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))"; cases "x64_disassemble lc", simp_all)
          done

        subgoal for c lc
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))"; cases "x64_disassemble lc", simp_all)
          done

        subgoal for c lc
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))"; cases "x64_disassemble lc", simp_all)
          done

        subgoal for c lc
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))"; cases "x64_disassemble lc", simp_all)
          done

        subgoal for c lc
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))"; cases "x64_disassemble lc", simp_all)
          done

        subgoal for c lc
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))"; cases "x64_disassemble lc", simp_all)
          done

        subgoal for c lc
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))"; cases "x64_disassemble lc", simp_all)
          done

        subgoal for c lc
          apply (cases lc)
          subgoal by simp
          subgoal for d ld by (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))"; cases "x64_disassemble ld", simp_all)
          done

        subgoal for c lc
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))"; cases "x64_disassemble lc", simp_all)
          done

        subgoal for c lc
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))"; cases "x64_disassemble lc", simp_all)
          done

        subgoal for c lc
          apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))"; cases "x64_disassemble lc", simp_all)
          done
        done
      done
    done
  done

(*
lemma ireg_of_u8_0_simp [simp]: "ireg_of_u8 v = Some ireg.RAX \<Longrightarrow> v = 0" by (unfold ireg_of_u8_def, auto simp add: if_split_asm)
*)
lemma ireg_of_u8_u8_of_ireg_simp [simp]: "ireg_of_u8 v = Some r \<Longrightarrow> u8_of_ireg r = v" by (unfold ireg_of_u8_def, auto simp add: if_split_asm)


declare if_split_asm [split del]
end