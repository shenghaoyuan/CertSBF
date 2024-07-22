theory x64ConsistencyProof2
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

lemma ireg_of_u8_0_simp [simp]: "ireg_of_u8 v = Some ireg.RAX \<Longrightarrow> v = 0" by (unfold ireg_of_u8_def, auto simp add: if_split_asm)
lemma ireg_of_u8_u8_of_ireg_simp [simp]: "ireg_of_u8 v = Some r \<Longrightarrow> u8_of_ireg r = v" by (unfold ireg_of_u8_def, auto simp add: if_split_asm)

lemma try_tesst_1: "
    b \<noteq> 144 \<Longrightarrow>
    b \<noteq> 102 \<Longrightarrow>
    and 3 (d >> 6) = 3 \<Longrightarrow>
    or 64 (construct_rex_to_u8 True (and (bitfield_insert_u8 3 (Suc 0) (and 7 (d >> 3)) (and 1 (b >> 2))) 8 \<noteq> 0) False (and (bitfield_insert_u8 3 (Suc 0) (and 7 d) (and 1 b)) 8 \<noteq> 0)) = b \<and>
    construct_modsib_to_u8 3 (bitfield_insert_u8 3 (Suc 0) (and 7 (d >> 3)) (and 1 (b >> 2))) (bitfield_insert_u8 3 (Suc 0) (and 7 d) (and 1 b)) = d"
  apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
  apply simp
  apply (unfold bitfield_insert_u8_def u8_of_bool_def)
  apply simp
  using bit_eqI
  
      sorry
    sorry
  sorry

(*
      apply (unfold bitfield_insert_u8_def Let_def ireg_of_u8_def) *)


lemma x64disassemble_assemble_consistency:
  "x64_disassemble l_bin = Some l_asm \<Longrightarrow> x64_assemble l_asm = Some l_bin"
  apply (induction l_asm arbitrary: l_bin)

(**r l_asm = [] *)
  subgoal for l_bin
    using x64_disassemble_nil
    using x64_assemble.simps(1) by blast
    

(**r l_asm = x1 + l_asm *)
  subgoal for a l_bin l_asm
    apply simp
    apply (cases a)
    subgoal for rd r1  \<comment> \<open> Pmov_rr \<close>
      apply simp
      apply (cases "l_asm", simp_all)
      subgoal for b lb
        subgoal by (cases "x64_disassemble lb", simp_all)
        done
      subgoal for b lb
        apply (cases "lb", simp_all)
        subgoal for c lc
          apply (cases "lc", simp_all)
          subgoal for d ld
            apply (unfold Let_def)
            apply (cases "c = 137")
            subgoal
              apply simp
              apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (d >> 3)) (and 1 (b >> 2)))", simp_all)
              subgoal for src
                apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 d) (and 1 b))", simp_all)
                subgoal for dst
                  apply (cases "x64_disassemble ld", simp_all)
                  using try_tesst_1 by blast
                  done
  done

end