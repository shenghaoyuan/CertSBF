theory x64ConsistencyProof2
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler
  x64ConsistencyProof2Aux0
  x64ConsistencyProof2Pmov0
  x64ConsistencyProof2Pmov1
begin

declare if_split_asm [split]


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
      subgoal for rex lb
        apply (cases "lb", simp_all)
        subgoal for c lc
          apply (cases "lc", simp_all)
          subgoal for rop ld
            apply (unfold Let_def)
            apply (cases "c = 137", simp)
            subgoal
              apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (rop >> 3)) (and 1 (rex >> 2)))", simp_all)
              subgoal for src
                apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 rop) (and 1 rex))", simp_all)
                subgoal for dst
                  apply (cases "x64_disassemble ld", simp_all)
                  apply (rule conjI)
                  subgoal using mov_goal_0 by blast
                  subgoal using mov_goal_1 by blast
                  done
                subgoal sorry
                done
              done
            sorry
          done
        done
      done
    sorry
  done

declare if_split_asm [split del]
end