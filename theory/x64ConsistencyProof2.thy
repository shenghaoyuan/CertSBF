theory x64ConsistencyProof2
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler
  x64ConsistencyProof2Aux0 (*
  x64ConsistencyProof2Pmov0
  x64ConsistencyProof2Pmov1 *)
  x64Pmovl_rr0
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
  subgoal for a l_asm l_bin_b apply (cases a, simp_all add: Let_def)

    \<comment> \<open> Pmovl_rr \<close>
    subgoal for rd r1 apply (cases "l_bin_b", simp_all)
      subgoal for b lb by (cases "x64_disassemble lb", simp_all)

      subgoal for rex lb apply (cases "lb", simp_all)
        subgoal for c lc apply (cases "lc", simp_all)
          subgoal for rop ld apply (cases "ld", simp_all)
            subgoal for e le apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 rop) 0)", simp)
              subgoal for src apply (cases "x64_disassemble ld", simp_all)
                done
              done
            done
          done
        subgoal for c lc apply (cases "lc", simp_all)
          subgoal for rop ld apply (cases "ld", simp_all add: Let_def)
            subgoal for e le apply (cases "x64_disassemble le", simp_all)
              done
            done
          done
        done

      subgoal for rex lb apply (cases "lb", simp_all)
        subgoal for c lc apply (cases "x64_disassemble lc", simp_all)
          done
        done

      subgoal for rex lb apply (cases "lb", simp_all add: Let_def)
        subgoal for rop lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (rop >> 3)) 0)", simp_all)
          subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 rop) 0)", simp_all)
            subgoal for dst apply (cases "x64_disassemble lc", simp_all)
              apply (rule conjI)
              subgoal using pmovl_rr_lemma0 by blast
              subgoal sorry
(*
              subgoal using mov_goal_0 by blast
              subgoal using mov_goal_1 by blast *)
              done
            done
          done
        subgoal for rop lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (rop >> 3)) 0)", simp_all)
          subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 rop) 0)", simp_all)
            subgoal for dst apply (cases "x64_disassemble lc", simp_all)
              done
            done
          done
        done

      subgoal for rex lb apply (cases "lb", simp_all add: Let_def)
        subgoal for rop lc apply (cases "lc", simp)
          subgoal for d ld apply simp
          subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 rop) 0)", simp_all)
            subgoal for dst apply (cases "x64_disassemble lc", simp_all)
      sorry

    \<comment> \<open> Other ins \<close>
    sorry
  done

declare if_split_asm [split del]
end