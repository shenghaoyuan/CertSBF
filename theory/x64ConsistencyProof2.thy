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
            subgoal  \<comment> \<open> Pmov_rr \<close>
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

            subgoal  \<comment> \<open> Paddq_rr \<close>
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
  done

lemma ireg_of_u8_0_simp [simp]: "ireg_of_u8 v = Some ireg.RAX \<Longrightarrow> v = 0" by (unfold ireg_of_u8_def, auto simp add: if_split_asm)
lemma ireg_of_u8_u8_of_ireg_simp [simp]: "ireg_of_u8 v = Some r \<Longrightarrow> u8_of_ireg r = v" by (unfold ireg_of_u8_def, auto simp add: if_split_asm)

lemma [simp]: "and x86CommType.RBX (e >> 6) = x86CommType.RBX \<Longrightarrow> ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and x86CommType.RDI (e >> 3)) (and x86CommType.RCX (c >> 2))) = Some r1 \<Longrightarrow>
    ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and x86CommType.RDI e) (and x86CommType.RCX c)) = Some rd \<Longrightarrow>
    or 64 (construct_rex_to_u8 False (and (u8_of_ireg r1) x86CommType.R8 \<noteq> x86CommType.RAX) False (and (u8_of_ireg rd) x86CommType.R8 \<noteq> x86CommType.RAX)) = c \<and> construct_modsib_to_u8 x86CommType.RBX (u8_of_ireg r1) (u8_of_ireg rd) = e"
  (*
  apply (unfold ireg_of_u8_def) *)

  apply (cases "r1")
  subgoal
    apply simp
    apply (cases "rd")
    subgoal
      apply simp
      apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
      apply simp
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
      apply (cases "l_asm", simp)
      subgoal for b lb
        apply simp
        subgoal by (cases "x64_disassemble lb", simp_all)
        apply (cases "lb", simp)
        subgoal for c lc
          apply simp
          apply (cases "lc", simp)
          subgoal for d ld
            apply simp
            apply (cases "ld", simp)
            subgoal for e le
              apply simp
              subgoal
                apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and x86CommType.RDI (e >> 3)) (and x86CommType.RCX (c >> 2)))", simp)
                subgoal for src
                  apply simp
                  apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and x86CommType.RDI e) (and x86CommType.RCX c))", simp)
                  subgoal for dst
                    apply simp
                    apply (cases "x64_disassemble le", simp)
                    subgoal for p_mov
                      apply simp

                      apply (cases "r1")
                      subgoal
                        apply (cases "rd")
                          subgoal
                            apply simp
  done

end