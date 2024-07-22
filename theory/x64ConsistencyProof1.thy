theory x64ConsistencyProof1
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler
begin
(*
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

lemma x64assemble_disassemble_consistency_pmovq_rr: "\<And>x11 x12.
       (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
       (case x64_assemble l_asm of None \<Rightarrow> None
        | Some l \<Rightarrow>
            Some
             ([or 64 (construct_rex_to_u8 True (and (u8_of_ireg x12) 8 \<noteq> 0) False (and (u8_of_ireg x11) 8 \<noteq> 0)),
               137, construct_modsib_to_u8 3 (u8_of_ireg x12) (u8_of_ireg x11)] @
              l)) =
       Some l_bin \<Longrightarrow>
       a = Pmovq_rr x11 x12 \<Longrightarrow> x64_disassemble l_bin = Some (Pmovq_rr x11 x12 # l_asm)"
  subgoal for rd r1
    apply (cases "x64_assemble l_asm", simp_all)
    subgoal for l1
      apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
      apply simp
      apply (cases l_bin)
      subgoal by fastforce
      subgoal for rex l1
        apply simp
        apply (cases l1)
        subgoal by fastforce
        subgoal for op l1
          apply simp
          apply (cases l1)
          subgoal by fastforce
          subgoal for reg l1
            apply simp
            apply (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done
          done
        done
      done
    done
  done

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


lemma x64assemble_disassemble_consistency_pneg: "\<And>x21a.
       (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
       (case x64_assemble l_asm of None \<Rightarrow> None
        | Some l \<Rightarrow>
            Some
             ([or 64 (construct_rex_to_u8 True False False (and (u8_of_ireg x21a) 8 \<noteq> 0)), 247,
               construct_modsib_to_u8 3 3 (u8_of_ireg x21a)] @
              l)) =
       Some l_bin \<Longrightarrow>
       a = Pnegq x21a \<Longrightarrow> x64_disassemble l_bin = Some (Pnegq x21a # l_asm)"
  subgoal for rd
    apply (cases "x64_assemble l_asm")
    subgoal by simp
    subgoal for l1
      apply simp
      apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
      apply simp
      apply (cases l_bin)
      subgoal by fastforce
      subgoal for rex l1
        apply (cases l1)
        subgoal by fastforce
        subgoal for op l1
          apply simp
          apply (cases l1)
          subgoal by fastforce
          subgoal for reg l1
            apply simp
            apply (cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_paddq_rr :"\<And>x221 x222.
       (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
       (case x64_assemble l_asm of None \<Rightarrow> None
        | Some l \<Rightarrow>
            Some
             ([or 64 (construct_rex_to_u8 True (and (u8_of_ireg x222) 8 \<noteq> 0) False (and (u8_of_ireg x221) 8 \<noteq> 0)),
               1, construct_modsib_to_u8 3 (u8_of_ireg x222) (u8_of_ireg x221)] @
              l)) =
       Some l_bin \<Longrightarrow>
       a = Paddq_rr x221 x222 \<Longrightarrow> x64_disassemble l_bin = Some (Paddq_rr x221 x222 # l_asm)"
  subgoal for rd r1
    apply (cases "x64_assemble l_asm")
    subgoal by simp
    subgoal for l1
      apply simp
      apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
      apply simp
      apply (cases l_bin)
      subgoal by fastforce
      subgoal for rex l1
        apply (cases l1)
        subgoal by fastforce
        subgoal for op l1
          apply simp
          apply (cases l1)
          subgoal by fastforce
          subgoal for reg l1
            apply simp
            apply (cases r1; cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_psubq_rr: "\<And>x251 x252.
       (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
       (case x64_assemble l_asm of None \<Rightarrow> None
        | Some l \<Rightarrow>
            Some
             ([or 64 (construct_rex_to_u8 True (and (u8_of_ireg x252) 8 \<noteq> 0) False (and (u8_of_ireg x251) 8 \<noteq> 0)),
               41, construct_modsib_to_u8 3 (u8_of_ireg x252) (u8_of_ireg x251)] @
              l)) =
       Some l_bin \<Longrightarrow>
       a = Psubq_rr x251 x252 \<Longrightarrow> x64_disassemble l_bin = Some (Psubq_rr x251 x252 # l_asm)"
  subgoal for rd r1
    apply (cases "x64_assemble l_asm")
    subgoal by simp
    subgoal for l1
      apply simp
      apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def)
      apply simp
      apply (cases l_bin)
      subgoal by fastforce
      subgoal for rex l1
        apply (cases l1)
        subgoal by fastforce
        subgoal for op l1
          apply simp
          apply (cases l1)
          subgoal by fastforce
          subgoal for reg l1
            apply simp
            apply (cases r1; cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done
          done
        done
      done
    done
  done

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

      \<comment> \<open> Pnegq \<close>
    subgoal for rd using x64assemble_disassemble_consistency_pneg
      by blast


      \<comment> \<open> Paddq_rr \<close>
    subgoal for rd using x64assemble_disassemble_consistency_paddq_rr
      by blast
      \<comment> \<open> Psubq_rr \<close>
    subgoal for rd using x64assemble_disassemble_consistency_psubq_rr
      by blast
      \<comment> \<open> Pmull_r \<close>
    subgoal  sorry
      \<comment> \<open> Pmulq_r \<close>
    subgoal  sorry
      \<comment> \<open> Pimull_r \<close>
    subgoal  sorry
      \<comment> \<open> Pmulq_r \<close>
    subgoal  sorry
      \<comment> \<open> Pmulq_r \<close>
    subgoal  sorry
    subgoal  sorry
      \<comment> \<open> Pmulq_r \<close>
    subgoal  sorry
      \<comment> \<open> Pmulq_r \<close>
    subgoal  sorry
    subgoal  sorry
      \<comment> \<open> Pmulq_r \<close>
    subgoal  sorry
      \<comment> \<open> Pmulq_r \<close>
    subgoal  sorry
    subgoal  sorry
      \<comment> \<open> Pmulq_r \<close>
    subgoal  sorry
      \<comment> \<open> Pmulq_r \<close>
    subgoal  sorry
    subgoal  sorry
      \<comment> \<open> Pmulq_r \<close>
    subgoal  sorry
      \<comment> \<open> Pmulq_r \<close>
    subgoal  sorry
    subgoal  sorry
      \<comment> \<open> Pmulq_r \<close>
    subgoal  sorry
      \<comment> \<open> Pmulq_r \<close>
    subgoal  sorry

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