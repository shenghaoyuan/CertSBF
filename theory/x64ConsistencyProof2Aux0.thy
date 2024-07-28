theory x64ConsistencyProof2Aux0
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler
begin
declare if_split_asm [split]

lemma x64_disassemble_nil [simp]: "x64_disassemble l_bin = Some [] \<Longrightarrow> l_bin = []"
  apply (induction l_bin, simp_all)
  \<comment> \<open> l_bin = a#l_bin \<close>
  subgoal for a l_bin  \<comment> \<open> Pnop \<close>
    apply (cases "x64_disassemble l_bin", simp_all)
    done

  subgoal for a l_bin  \<comment> \<open> Prolw_ri + Pmov_rm \<close>
    apply (cases l_bin, simp_all)
    subgoal for b lb apply (cases lb, simp_all) \<comment> \<open> Prolw_ri \<close>
      subgoal for c lc apply (cases lc, simp_all)
        subgoal for d ld apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) 0)", simp)
          subgoal for e by (cases "x64_disassemble lc", simp_all)
          done
        done
      done

    subgoal for b lb apply (cases lb, simp_all add: Let_def)
      subgoal for c lc apply (cases lc, simp_all)
        subgoal for d ld by (cases "x64_disassemble ld", simp_all)
        done
      done
    done

    subgoal for a l_bin \<comment> \<open> Prdtsc \<close>
      apply (cases l_bin, simp_all)
      subgoal for d ld by (cases "x64_disassemble ld", simp_all)
      done

    subgoal for a l_bin  \<comment> \<open> Pmovl_rr + Paddl_rr \<close>
      apply (cases l_bin, simp_all add: Let_def)
      subgoal for b lb apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (b >> 3)) 0)", simp_all)
        subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 b) 0)", simp_all)
          subgoal for dst by (cases "x64_disassemble lb", simp_all)
          done
        done

      subgoal for b lb apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (b >> 3)) 0)", simp_all)
        subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 b) 0)", simp_all)
          subgoal for dst by (cases "x64_disassemble lb", simp_all)
          done
        done
      done

    subgoal for a l_bin apply (cases l_bin, simp_all add: Let_def)
      subgoal for b lb apply (cases lb, simp_all)

        \<comment> \<open> Pmovq_rr + Pmovl_rr \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
            subgoal for dst by (cases "x64_disassemble lc", simp_all)
            subgoal for dst by (cases "x64_disassemble lc", simp_all)
            done
          done

        \<comment> \<open> Pmov_rm M64 \<close>
        subgoal for c lc by (cases "x64_disassemble lc", simp_all)

        \<comment> \<open> Pmov_rm M32 \<close>
        subgoal for c lc by (cases "x64_disassemble lc", simp_all)

        \<comment> \<open> Pmov_mr M64 + M32 \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          subgoal for src by (cases "x64_disassemble lc", simp_all)
          subgoal for src by (cases "x64_disassemble lc", simp_all)
          done

        \<comment> \<open> Pmovq_rr \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
            subgoal for dst by (cases "x64_disassemble lc", simp_all)
            done
          done

        \<comment> \<open> Paddq_rr + Paddl_rr \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
            subgoal for dst by (cases "x64_disassemble lc", simp_all)
            subgoal for dst by (cases "x64_disassemble lc", simp_all)
            done
          done

        \<comment> \<open> Psubq_rr + Psubl_rr \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
            subgoal for dst by (cases "x64_disassemble lc", simp_all)
            subgoal for dst by (cases "x64_disassemble lc", simp_all)
            done
          done

        \<comment> \<open> Pnegq + Pnegl \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          done

        \<comment> \<open> Pmulq_r + Pmull_r \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          done

        \<comment> \<open> Pimulq_r + Pimull_r \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          done

        \<comment> \<open> Pdivq_r + Pdivl_r \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          done

        \<comment> \<open> Pidivq_r + Pidivl_r \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          done

        \<comment> \<open> Porq_rr + Porl_rr \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
            subgoal for dst by (cases "x64_disassemble lc", simp_all)
            subgoal for dst by (cases "x64_disassemble lc", simp_all)
            done
          done

        \<comment> \<open> Pandq_rr + Pandl_rr \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
            subgoal for dst by (cases "x64_disassemble lc", simp_all)
            subgoal for dst by (cases "x64_disassemble lc", simp_all)
            done
          done

        \<comment> \<open> Pxorq_rr + Pxorl_rr \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (c >> 3)) (and 1 (a >> 2)))", simp_all)
          subgoal for src apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
            subgoal for dst by (cases "x64_disassemble lc", simp_all)
            subgoal for dst by (cases "x64_disassemble lc", simp_all)
            done
          done

        \<comment> \<open> Pshlq_ri + Pshll_ri + ... \<close>
        subgoal for c lc apply (cases lc, simp_all)
          subgoal for d ld apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
            subgoal for dst by (cases "x64_disassemble ld", simp_all)
            subgoal for dst by (cases "x64_disassemble ld", simp_all)
            done
          subgoal for d ld apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
            subgoal for dst by (cases "x64_disassemble ld", simp_all)
            subgoal for dst by (cases "x64_disassemble ld", simp_all)
            done
          subgoal for d ld apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
            subgoal for dst by (cases "x64_disassemble ld", simp_all)
            subgoal for dst by (cases "x64_disassemble ld", simp_all)
            done
          done

        \<comment> \<open> Pshlq_r + Pshll_r \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          done

        \<comment> \<open> Pshrq_r + Pshrl_r \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          done

        \<comment> \<open> Psarq_r + Psarl_r \<close>
        subgoal for c lc apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 c) (and 1 a))", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          subgoal for dst by (cases "x64_disassemble lc", simp_all)
          done
        done
      done
    done

lemma ireg_of_u8_u8_of_ireg_simp [simp]: "ireg_of_u8 v = Some r \<Longrightarrow> u8_of_ireg r = v" by (unfold ireg_of_u8_def, auto simp add: if_split_asm)


declare if_split_asm [split del]
end