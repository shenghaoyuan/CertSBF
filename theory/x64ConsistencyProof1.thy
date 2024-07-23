theory x64ConsistencyProof1
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler x64ConsistencyProof1Ins
begin


lemma x64assemble_disassemble_consistency:
  "x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm"
  apply (induction l_asm arbitrary: l_bin)
   apply simp

  subgoal for a l_asm l_bin
    apply simp
    apply (cases a, auto)

      \<comment> \<open> Pmovq_rr \<close>
    subgoal for rd r1 using x64assemble_disassemble_consistency_pmovq_rr
      by blast
      \<comment> \<open> Pmovl_rr \<close>
    subgoal for rd r1 using x64assemble_disassemble_consistency_pmovl_rr
      by blast
      \<comment> \<open> Pnegl \<close>
    subgoal for rd using x64assemble_disassemble_consistency_pnegl
      by blast
      \<comment> \<open> Pnegq \<close>
    subgoal for rd using x64assemble_disassemble_consistency_pnegq
      by blast
      \<comment> \<open> Paddq_rr \<close>
    subgoal for rd r1 using x64assemble_disassemble_consistency_paddq_rr
      by blast
      \<comment> \<open> Paddl_rr \<close>
    subgoal for rd r1 using x64assemble_disassemble_consistency_paddl_rr
      by blast
      \<comment> \<open> Psubl_rr \<close>
    subgoal for rd r1 using x64assemble_disassemble_consistency_psubl_rr
      by blast
      \<comment> \<open> Psubq_rr \<close>
    subgoal for rd r1 using x64assemble_disassemble_consistency_psubq_rr
      by blast 

      \<comment> \<open> Pmull_r \<close>
    subgoal for r1 using x64assemble_disassemble_consistency_pmull_r
      by blast
      \<comment> \<open> Pmulq_r \<close>
    subgoal for r1 using x64assemble_disassemble_consistency_pmulq_r
      by blast
      \<comment> \<open> Pimull_r \<close>
    subgoal for r1 using x64assemble_disassemble_consistency_pimull_r
      by blast
      \<comment> \<open> Pimulq_r \<close>
    subgoal for r1 using x64assemble_disassemble_consistency_pimulq_r
      by blast
      \<comment> \<open> Pdivl_r \<close>
    subgoal for r1 using x64assemble_disassemble_consistency_pdivl_r
      by blast
      \<comment> \<open> Pdivq_r \<close>
    subgoal for r1 using x64assemble_disassemble_consistency_pdivq_r
      by blast
      \<comment> \<open> Pidivl_r \<close>
    subgoal for r1 using x64assemble_disassemble_consistency_pidivl_r
      by blast
      \<comment> \<open> Pidivq_r \<close>
    subgoal for r1 using x64assemble_disassemble_consistency_pidivq_r
      by blast

      \<comment> \<open> Pandl_rr \<close>
    subgoal for rd r1 using x64assemble_disassemble_consistency_pandl_rr
      by blast
      \<comment> \<open> Pandq_rr \<close>
    subgoal for rd r1 using x64assemble_disassemble_consistency_pandq_rr
      by blast
      \<comment> \<open> Porl_rr \<close>
    subgoal for rd r1 using x64assemble_disassemble_consistency_porl_rr
      by blast
      \<comment> \<open> Porq_rr \<close>
    subgoal for rd r1 using x64assemble_disassemble_consistency_porq_rr
      by blast
      \<comment> \<open> Pxorl_rr \<close>
    subgoal for rd r1 using x64assemble_disassemble_consistency_pxorl_rr
      by blast
      \<comment> \<open> Pxorq_rr \<close>
    subgoal for rd r1 using x64assemble_disassemble_consistency_pxorq_rr
      by blast
      \<comment> \<open> Pshll_ri \<close>
    subgoal for rd n using x64assemble_disassemble_consistency_pshll_ri
      by blast
      \<comment> \<open> Pshlq_ri \<close>
    subgoal for rd n using x64assemble_disassemble_consistency_pshlq_ri
      by blast
      \<comment> \<open> Pshll_r \<close>
    subgoal for rd using x64assemble_disassemble_consistency_pshll_r
      by blast
      \<comment> \<open> Pshlq_r \<close>
    subgoal for rd  using x64assemble_disassemble_consistency_pshlq_r
      by blast
      \<comment> \<open> Pshrl_ri \<close>
    subgoal for rd n using x64assemble_disassemble_consistency_pshrl_ri
      by blast
      \<comment> \<open> Pshrq_ri \<close>
    subgoal for rd n using x64assemble_disassemble_consistency_pshrq_ri
      by blast
      \<comment> \<open> Pshrl_r \<close>
    subgoal for rd using x64assemble_disassemble_consistency_pshrl_r
      by blast
      \<comment> \<open> Pshrq_r \<close>
    subgoal for rd  using x64assemble_disassemble_consistency_pshrq_r
      by blast
      \<comment> \<open> Psarl_ri \<close>
    subgoal for rd n using x64assemble_disassemble_consistency_psarl_ri
      by blast
      \<comment> \<open> Psarq_ri \<close>
    subgoal for rd n using x64assemble_disassemble_consistency_psarq_ri
      by blast
      \<comment> \<open> Psarl_r \<close>
    subgoal for rd  using x64assemble_disassemble_consistency_psarl_r
      by blast
      \<comment> \<open> Psarq_r \<close>
    subgoal for rd  using x64assemble_disassemble_consistency_psarq_r
      by blast
      \<comment> \<open> pnop \<close>
      apply (cases "x64_assemble l_asm")
      subgoal by simp
      subgoal for l1
        apply simp
        apply (cases l_bin)
        subgoal by fastforce
        subgoal for prefix l1
          apply simp
          done
        done
      done
    done

end

\<comment> \<open> 
                apply (frule conjunct2)
                apply (frule conjunct2)
                apply(frule pmov_src[of prefix r1 rd rex op rop])
              apply (subgoal_tac "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and x86CommType.RDI (rop >> 3))
                  (and x86CommType.RCX (rex >> 2)))
                = Some r1")
                 prefer 2
                 apply (auto simp add:  pmov_src[of r1 rd])[1]
              proof -
                assume r1:"or (or 192 (and 56 (u8_of_ireg r1 << 3))) (and x86CommType.RDI (u8_of_ireg rd)) = rop"
                assume r2:"or 64
   (or (u8_of_bool (and (u8_of_ireg r1) x86CommType.R8 \<noteq> x86CommType.RAX) << 2)
     (u8_of_bool (and (u8_of_ireg rd) x86CommType.R8 \<noteq> x86CommType.RAX))) =
  rex"
                show "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and x86CommType.RDI (rop >> 3))
                  (and x86CommType.RCX (rex >> 2)))
                = Some r1" using r2 r1 pmov_src[OF] by auto
   

                apply (auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def split: ireg.split)\<close>


(*
lemma rbx_simp [simp]: "or (or 192 (and 56 (u8_of_ireg r1 << 3))) (and x86CommType.RDI (u8_of_ireg rd)) = rop
  \<Longrightarrow> and x86CommType.RBX (rop >> 6) = x86CommType.RBX"
  apply (cases r1; cases rd, auto)
  done

lemma pmov_src [simp]: "
     prefix = 102 \<and>
     or 64
     (or (u8_of_bool (and (u8_of_ireg r1) x86CommType.R8 \<noteq> x86CommType.RAX) << 2)
       (u8_of_bool (and (u8_of_ireg rd) x86CommType.R8 \<noteq> x86CommType.RAX))) =
    rex \<and>
    op = 137 \<and>
    or (or 192 (and 56 (u8_of_ireg r1 << 3))) (and x86CommType.RDI (u8_of_ireg rd)) = rop \<and>
    l2 = l1 \<Longrightarrow>
    ireg_of_u8
            (bitfield_insert_u8 3 (Suc 0) (and x86CommType.RDI (rop >> 3)) (and x86CommType.RCX (rex >> 2)))
       = Some r1"
  apply (unfold u8_of_bool_def bitfield_insert_u8_def Let_def)
  apply (cases r1; cases rd, auto simp add: ireg_of_u8_def)
  done *)

(*(*
declare if_split_asm [split] *)

(*
lemma list_eq_rewrite: "x#y = l \<Longrightarrow> f l = f (x#y)" by auto *)


value "x64_assemble [Pmov_rr ireg.R8 ireg.RAX]"
(**r Some [102, 65, 137, 192] *)
value "x64_disassemble [102, 65, 137, 192]"

value "or (or 192 (u8_of_ireg ireg.RAX << 3)) x86CommType.RBX"
(** 195 *)
value "ireg_of_u8
     (or (and x86CommType.RDI (and x86CommType.RCX (0 >> 2)))
       (and (and x86CommType.RDI (195 >> 3)) (- x86CommType.R8)))"
(**r Some ireg.RAX *)

value "and x86CommType.RBX (195 >> 6) = x86CommType.RBX"
*)