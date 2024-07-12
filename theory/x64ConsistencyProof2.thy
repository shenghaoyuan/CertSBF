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
    subgoal  \<comment> \<open> Pmov_rr \<close>
      apply (cases l_bin)
      subgoal by simp
      subgoal for b lb
        apply simp
        apply (cases lb)
        subgoal by simp
        subgoal for c lc
          apply simp
          apply (cases lc)
          subgoal by simp
          subgoal for d ld
            apply simp
            apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and x86CommType.RDI (d >> 3)) (and x86CommType.RCX (b >> 2)))")
            subgoal by simp
            subgoal for src
              apply simp
              apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and x86CommType.RDI d) (and x86CommType.RCX b))")
              subgoal by simp
              subgoal for dst
                apply simp
                apply (cases "x64_disassemble ld", simp_all)
                done
              done
            done
          done
        done
      done
    done
  done


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


  done

end