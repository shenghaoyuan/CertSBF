theory x64ConsistencyProof1Ins
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler
begin

lemma [simp]: " bitfield_insert_u8 3 (Suc 0) 1 0 = 1 " 
  apply(unfold bitfield_insert_u8_def Let_def)
  apply simp
  done

lemma x64assemble_disassemble_consistency_pmovq_rr: "\<And>x11 x12.
       (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
       (case x64_assemble l_asm of None \<Rightarrow> None
        | Some l \<Rightarrow>
            Some
             ([construct_rex_to_u8 True (and (u8_of_ireg x12) 8 \<noteq> 0) False (and (u8_of_ireg x11) 8 \<noteq> 0), 137,
               construct_modsib_to_u8 3 (u8_of_ireg x12) (u8_of_ireg x11)] @
              l)) =
       Some l_bin \<Longrightarrow>
       a = Pmovq_rr x11 x12 \<Longrightarrow> x64_disassemble l_bin = Some (Pmovq_rr x11 x12 # l_asm)"  
  subgoal for rd r1
    apply (cases "x64_assemble l_asm", simp_all)
    subgoal premises aaa for l1
      apply (simp add: aaa(2)[symmetric])
      apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def Let_def)
      apply (cases "ireg_of_u8
                       (bitfield_insert_u8 3 (Suc 0) (and 7 (bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg rd)) (and 7 (u8_of_ireg r1))) 3 >> 3)) 0)", simp_all)
      subgoal
        apply (cases "ireg_of_u8
              (bitfield_insert_u8 3 (Suc 0) (and 7 (bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg rd)) (and 7 (u8_of_ireg r1))) 3 >> 3))
                (and 1
                  (bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg rd) 8 \<noteq> 0)) 0) (u8_of_bool (and (u8_of_ireg r1) 8 \<noteq> 0)))
                    1 >>
                   2)))", simp_all)
        subgoal by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
        subgoal for src
          apply (cases "ireg_of_u8
                  (bitfield_insert_u8 3 (Suc 0) (and 7 (bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg rd)) (and 7 (u8_of_ireg r1))) 3))
                    (and 1
                      (bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg rd) 8 \<noteq> 0)) 0) (u8_of_bool (and (u8_of_ireg r1) 8 \<noteq> 0)))
                        1)))", simp_all)
        subgoal by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
        subgoal for dst
          apply (cases "x64_disassemble l1", simp_all)
          subgoal by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
          subgoal for l1 by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
          done
        done
      done
    subgoal for t1
      apply (cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 (bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg rd)) (and 7 (u8_of_ireg r1))) 3)) 0)", simp_all)
      subgoal
        apply (cases "ireg_of_u8
                  (bitfield_insert_u8 3 (Suc 0) (and 7 (bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg rd)) (and 7 (u8_of_ireg r1))) 3 >> 3))
                    (and 1
                      (bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg rd) 8 \<noteq> 0)) 0) (u8_of_bool (and (u8_of_ireg r1) 8 \<noteq> 0)))
                        1 >>
                       2)))", simp_all)
        subgoal by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
        subgoal for src
          apply (cases "ireg_of_u8
                  (bitfield_insert_u8 3 (Suc 0) (and 7 (bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg rd)) (and 7 (u8_of_ireg r1))) 3))
                    (and 1
                      (bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg rd) 8 \<noteq> 0)) 0) (u8_of_bool (and (u8_of_ireg r1) 8 \<noteq> 0)))
                        1)))", simp_all)
          subgoal by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
          subgoal for dst
            apply (cases "x64_disassemble l1", simp_all)
              subgoal by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
              subgoal for l1 by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
              done
            done
          done
        subgoal for op
          apply (cases "ireg_of_u8
                  (bitfield_insert_u8 3 (Suc 0) (and 7 (bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg rd)) (and 7 (u8_of_ireg r1))) 3 >> 3))
                    (and 1
                      (bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg rd) 8 \<noteq> 0)) 0) (u8_of_bool (and (u8_of_ireg r1) 8 \<noteq> 0)))
                        1 >>
                       2)))", simp_all)
          subgoal
            apply (cases "x64_disassemble l1", simp_all)
            subgoal by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            subgoal for l1 by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done
          subgoal for src
            apply (cases "ireg_of_u8
                  (bitfield_insert_u8 3 (Suc 0) (and 7 (bitfield_insert_u8 6 2 (bitfield_insert_u8 3 3 (and 7 (u8_of_ireg rd)) (and 7 (u8_of_ireg r1))) 3))
                    (and 1
                      (bitfield_insert_u8 3 (Suc 0) (bitfield_insert_u8 2 (Suc 0) (bitfield_insert_u8 (Suc 0) (Suc 0) (u8_of_bool (and (u8_of_ireg rd) 8 \<noteq> 0)) 0) (u8_of_bool (and (u8_of_ireg r1) 8 \<noteq> 0)))
                        1)))", simp_all)
            subgoal
              apply (cases "x64_disassemble l1", simp_all)
              subgoal by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
              subgoal for l1 by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
              done
            subgoal for dst
              apply (cases "x64_disassemble l1", simp_all)
              subgoal by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
              subgoal for l1 by (cases r1; cases rd,auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
              done
            done
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pmovl_rr: "\<And>x21 x22.
       (\<And>l_bin.
           x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
       (case x64_assemble l_asm of None \<Rightarrow> None
        | Some l \<Rightarrow>
            Some
             ([or 64
                (construct_rex_to_u8 False (and (u8_of_ireg x22) 8 \<noteq> 0) False
                  (and (u8_of_ireg x21) 8 \<noteq> 0)),
               137, construct_modsib_to_u8 3 (u8_of_ireg x22) (u8_of_ireg x21)] @
              l)) =
       Some l_bin \<Longrightarrow>
       a = Pmovl_rr x21 x22 \<Longrightarrow> x64_disassemble l_bin = Some (Pmovl_rr x21 x22 # l_asm)"
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

lemma x64assemble_disassemble_consistency_pnegl: "\<And>x20. (\<And>l_bin.
               x64_assemble l_asm = Some l_bin \<Longrightarrow>
               x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
           (case x64_assemble l_asm of None \<Rightarrow> None
            | Some l \<Rightarrow>
                Some
                 ([or 64
                    (construct_rex_to_u8 False False False
                      (and (u8_of_ireg x20) 8 \<noteq> 0)),
                   247, construct_modsib_to_u8 3 3 (u8_of_ireg x20)] @
                  l)) =
           Some l_bin \<Longrightarrow>
           a = Pnegl x20 \<Longrightarrow> x64_disassemble l_bin = Some (Pnegl x20 # l_asm)"
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

lemma x64assemble_disassemble_consistency_pnegq: "\<And>x21a.
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

lemma x64assemble_disassemble_consistency_paddl_rr :"\<And>x231 x232.
       (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
       (case x64_assemble l_asm of None \<Rightarrow> None
        | Some l \<Rightarrow>
            Some
             ([or 64
                (construct_rex_to_u8 False (and (u8_of_ireg x232) 8 \<noteq> 0) False
                  (and (u8_of_ireg x231) 8 \<noteq> 0)),
               1, construct_modsib_to_u8 3 (u8_of_ireg x232) (u8_of_ireg x231)] @
              l)) =
       Some l_bin \<Longrightarrow>
       a = Paddl_rr x231 x232 \<Longrightarrow> x64_disassemble l_bin = Some (Paddl_rr x231 x232 # l_asm)"
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


lemma x64assemble_disassemble_consistency_psubl_rr: " \<And>x241 x242.
       (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
       (case x64_assemble l_asm of None \<Rightarrow> None
        | Some l \<Rightarrow>
            Some
             ([or 64
                (construct_rex_to_u8 False (and (u8_of_ireg x242) 8 \<noteq> 0) False
                  (and (u8_of_ireg x241) 8 \<noteq> 0)),
               41, construct_modsib_to_u8 3 (u8_of_ireg x242) (u8_of_ireg x241)] @
              l)) =
       Some l_bin \<Longrightarrow>
       a = Psubl_rr x241 x242 \<Longrightarrow> x64_disassemble l_bin = Some (Psubl_rr x241 x242 # l_asm)"
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

lemma x64assemble_disassemble_consistency_pmull_r: "\<And>x26. 
          (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
           (case x64_assemble l_asm of None \<Rightarrow> None
            | Some l \<Rightarrow>
                Some
                 ([or 64 (construct_rex_to_u8 False False False (and (u8_of_ireg x26) 8 \<noteq> 0)), 247,
                   construct_modsib_to_u8 3 4 (u8_of_ireg x26)] @
                  l)) =
           Some l_bin \<Longrightarrow>
           a = Pmull_r x26 \<Longrightarrow> x64_disassemble l_bin = Some (Pmull_r x26 # l_asm)"
  subgoal for r1 
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
            apply (cases r1, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pmulq_r: "\<And>x27. 
          (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
           (case x64_assemble l_asm of None \<Rightarrow> None
            | Some l \<Rightarrow>
                Some
                 ([or 64 (construct_rex_to_u8 True False False (and (u8_of_ireg x27) 8 \<noteq> 0)), 247,
                   construct_modsib_to_u8 3 4 (u8_of_ireg x27)] @
                  l)) =
           Some l_bin \<Longrightarrow>
           a = Pmulq_r x27 \<Longrightarrow> x64_disassemble l_bin = Some (Pmulq_r x27 # l_asm)"
  subgoal for r1
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
            apply (cases r1, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pimull_r: "\<And>x28. 
          (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
           (case x64_assemble l_asm of None \<Rightarrow> None
            | Some l \<Rightarrow>
                Some
                 ([or 64 (construct_rex_to_u8 False False False (and (u8_of_ireg x28) 8 \<noteq> 0)), 247,
                   construct_modsib_to_u8 3 5 (u8_of_ireg x28)] @
                  l)) =
           Some l_bin \<Longrightarrow>
           a = Pimull_r x28 \<Longrightarrow> x64_disassemble l_bin = Some (Pimull_r x28 # l_asm)"
  subgoal for r1
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
            apply (cases r1, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pimulq_r: "\<And>x29.
           (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
           (case x64_assemble l_asm of None \<Rightarrow> None
            | Some l \<Rightarrow>
                Some
                 ([or 64 (construct_rex_to_u8 True False False (and (u8_of_ireg x29) 8 \<noteq> 0)), 247,
                   construct_modsib_to_u8 3 5 (u8_of_ireg x29)] @
                  l)) =
           Some l_bin \<Longrightarrow>
           a = Pimulq_r x29 \<Longrightarrow> x64_disassemble l_bin = Some (Pimulq_r x29 # l_asm)"
  subgoal for r1 
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
            apply (cases r1, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pdivl_r: "\<And>x30.
     (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64 (construct_rex_to_u8 False False False (and (u8_of_ireg x30) 8 \<noteq> 0)), 247,
              construct_modsib_to_u8 3 6 (u8_of_ireg x30)] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Pdivl_r x30 \<Longrightarrow> x64_disassemble l_bin = Some (Pdivl_r x30 # l_asm)"
  subgoal for r1 
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
            apply (cases r1, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pdivq_r: "\<And>x31a.
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64 (construct_rex_to_u8 True False False (and (u8_of_ireg x31a) 8 \<noteq> 0)), 247,
              construct_modsib_to_u8 3 6 (u8_of_ireg x31a)] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Pdivq_r x31a \<Longrightarrow> x64_disassemble l_bin = Some (Pdivq_r x31a # l_asm)"
  subgoal for r1
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
            apply (cases r1, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pidivl_r: "\<And>x32a.
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64 (construct_rex_to_u8 False False False (and (u8_of_ireg x32a) 8 \<noteq> 0)), 247,
              construct_modsib_to_u8 3 7 (u8_of_ireg x32a)] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Pidivl_r x32a \<Longrightarrow> x64_disassemble l_bin = Some (Pidivl_r x32a # l_asm)"
  subgoal for r1
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
            apply (cases r1, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pidivq_r: "\<And>x33. 
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64 (construct_rex_to_u8 True False False (and (u8_of_ireg x33) 8 \<noteq> 0)), 247,
              construct_modsib_to_u8 3 7 (u8_of_ireg x33)] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Pidivq_r x33 \<Longrightarrow> x64_disassemble l_bin = Some (Pidivq_r x33 # l_asm)"
  subgoal for r1 
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
            apply (cases r1, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pandl_rr :"\<And>x341 x342.
       (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
       (case x64_assemble l_asm of None \<Rightarrow> None
        | Some l \<Rightarrow>
            Some
             ([or 64
                (construct_rex_to_u8 False (and (u8_of_ireg x342) 8 \<noteq> 0) False
                  (and (u8_of_ireg x341) 8 \<noteq> 0)),
               33, construct_modsib_to_u8 3 (u8_of_ireg x342) (u8_of_ireg x341)] @
              l)) =
       Some l_bin \<Longrightarrow>
       a = Pandl_rr x341 x342 \<Longrightarrow> x64_disassemble l_bin = Some (Pandl_rr x341 x342 # l_asm)"
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

lemma x64assemble_disassemble_consistency_pandq_rr :"\<And>x351 x352.
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64
               (construct_rex_to_u8 True (and (u8_of_ireg x352) 8 \<noteq> 0) False
                 (and (u8_of_ireg x351) 8 \<noteq> 0)),
              33, construct_modsib_to_u8 3 (u8_of_ireg x352) (u8_of_ireg x351)] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Pandq_rr x351 x352 \<Longrightarrow> x64_disassemble l_bin = Some (Pandq_rr x351 x352 # l_asm)"
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

lemma x64assemble_disassemble_consistency_porl_rr :"\<And>x361 x362.
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64
               (construct_rex_to_u8 False (and (u8_of_ireg x362) 8 \<noteq> 0) False
                 (and (u8_of_ireg x361) 8 \<noteq> 0)),
              9, construct_modsib_to_u8 3 (u8_of_ireg x362) (u8_of_ireg x361)] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Porl_rr x361 x362 \<Longrightarrow> x64_disassemble l_bin = Some (Porl_rr x361 x362 # l_asm)"
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

lemma x64assemble_disassemble_consistency_porq_rr :"\<And>x371 x372.
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64
               (construct_rex_to_u8 True (and (u8_of_ireg x372) 8 \<noteq> 0) False
                 (and (u8_of_ireg x371) 8 \<noteq> 0)),
              9, construct_modsib_to_u8 3 (u8_of_ireg x372) (u8_of_ireg x371)] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Porq_rr x371 x372 \<Longrightarrow> x64_disassemble l_bin = Some (Porq_rr x371 x372 # l_asm)"
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

lemma x64assemble_disassemble_consistency_pxorl_rr :"\<And>x381 x382.
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64
               (construct_rex_to_u8 False (and (u8_of_ireg x382) 8 \<noteq> 0) False
                 (and (u8_of_ireg x381) 8 \<noteq> 0)),
              49, construct_modsib_to_u8 3 (u8_of_ireg x382) (u8_of_ireg x381)] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Pxorl_rr x381 x382 \<Longrightarrow> x64_disassemble l_bin = Some (Pxorl_rr x381 x382 # l_asm)"
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

lemma x64assemble_disassemble_consistency_pxorq_rr :"\<And>x391 x392.
    (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
    (case x64_assemble l_asm of None \<Rightarrow> None
     | Some l \<Rightarrow>
         Some
          ([or 64
             (construct_rex_to_u8 True (and (u8_of_ireg x392) 8 \<noteq> 0) False
               (and (u8_of_ireg x391) 8 \<noteq> 0)),
            49, construct_modsib_to_u8 3 (u8_of_ireg x392) (u8_of_ireg x391)] @
           l)) =
    Some l_bin \<Longrightarrow>
    a = Pxorq_rr x391 x392 \<Longrightarrow> x64_disassemble l_bin = Some (Pxorq_rr x391 x392 # l_asm)"
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

lemma x64assemble_disassemble_consistency_pshll_ri :"\<And>x401 x402.
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64 (construct_rex_to_u8 False False False (and (u8_of_ireg x401) 8 \<noteq> 0)), 193,
              construct_modsib_to_u8 3 4 (u8_of_ireg x401), x402] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Pshll_ri x401 x402 \<Longrightarrow> x64_disassemble l_bin = Some (Pshll_ri x401 x402 # l_asm)"
  subgoal for rd n
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
            apply (cases n; cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done                               
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pshlq_ri :"\<And>x411 x412.
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64 (construct_rex_to_u8 True False False (and (u8_of_ireg x411) 8 \<noteq> 0)), 193,
              construct_modsib_to_u8 3 4 (u8_of_ireg x411), x412] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Pshlq_ri x411 x412 \<Longrightarrow> x64_disassemble l_bin = Some (Pshlq_ri x411 x412 # l_asm)"
  subgoal for rd n
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
            apply (cases n; cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done                               
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pshll_r :"\<And>x42a.
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64 (construct_rex_to_u8 False False False (and (u8_of_ireg x42a) 8 \<noteq> 0)), 211,
              construct_modsib_to_u8 3 4 (u8_of_ireg x42a)] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Pshll_r x42a \<Longrightarrow> x64_disassemble l_bin = Some (Pshll_r x42a # l_asm)"
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
            apply ( cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done                               
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pshlq_r :"\<And>x43. 
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64 (construct_rex_to_u8 True False False (and (u8_of_ireg x43) 8 \<noteq> 0)), 211,
              construct_modsib_to_u8 3 4 (u8_of_ireg x43)] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Pshlq_r x43 \<Longrightarrow> x64_disassemble l_bin = Some (Pshlq_r x43 # l_asm)"
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
            apply ( cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done                               
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pshrl_ri :"\<And>x441 x442.
     (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
     (case x64_assemble l_asm of None \<Rightarrow> None
      | Some l \<Rightarrow>
          Some
           ([or 64 (construct_rex_to_u8 False False False (and (u8_of_ireg x441) 8 \<noteq> 0)), 193,
             construct_modsib_to_u8 3 5 (u8_of_ireg x441), x442] @
            l)) =
     Some l_bin \<Longrightarrow>
     a = Pshrl_ri x441 x442 \<Longrightarrow> x64_disassemble l_bin = Some (Pshrl_ri x441 x442 # l_asm)"
  subgoal for rd n
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
            apply (cases n; cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done                               
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pshrq_ri :"\<And>x451 x452.
     (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
     (case x64_assemble l_asm of None \<Rightarrow> None
      | Some l \<Rightarrow>
          Some
           ([or 64 (construct_rex_to_u8 True False False (and (u8_of_ireg x451) 8 \<noteq> 0)), 193,
             construct_modsib_to_u8 3 5 (u8_of_ireg x451), x452] @
            l)) =
     Some l_bin \<Longrightarrow>
     a = Pshrq_ri x451 x452 \<Longrightarrow> x64_disassemble l_bin = Some (Pshrq_ri x451 x452 # l_asm)"
  subgoal for rd n
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
            apply (cases n; cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done                               
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pshrl_r :"\<And>x46. 
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64 (construct_rex_to_u8 False False False (and (u8_of_ireg x46) 8 \<noteq> 0)), 211,
              construct_modsib_to_u8 3 5 (u8_of_ireg x46)] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Pshrl_r x46 \<Longrightarrow> x64_disassemble l_bin = Some (Pshrl_r x46 # l_asm)"
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
            apply ( cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done                               
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_pshrq_r :"\<And>x47. 
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64 (construct_rex_to_u8 True False False (and (u8_of_ireg x47) 8 \<noteq> 0)), 211,
              construct_modsib_to_u8 3 5 (u8_of_ireg x47)] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Pshrq_r x47 \<Longrightarrow> x64_disassemble l_bin = Some (Pshrq_r x47 # l_asm)"
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
            apply ( cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done                               
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_psarl_ri :"\<And>x481 x482.
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64 (construct_rex_to_u8 False False False (and (u8_of_ireg x481) 8 \<noteq> 0)), 193,
              construct_modsib_to_u8 3 7 (u8_of_ireg x481), x482] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Psarl_ri x481 x482 \<Longrightarrow> x64_disassemble l_bin = Some (Psarl_ri x481 x482 # l_asm)"
  subgoal for rd n
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
            apply (cases n; cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done                               
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_psarq_ri :"\<And>x491 x492.
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64 (construct_rex_to_u8 True False False (and (u8_of_ireg x491) 8 \<noteq> 0)), 193,
              construct_modsib_to_u8 3 7 (u8_of_ireg x491), x492] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Psarq_ri x491 x492 \<Longrightarrow> x64_disassemble l_bin = Some (Psarq_ri x491 x492 # l_asm)"
  subgoal for rd n
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
            apply (cases n; cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done                               
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_psarl_r :"\<And>x50. 
    (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
    (case x64_assemble l_asm of None \<Rightarrow> None
     | Some l \<Rightarrow>
         Some
          ([or 64 (construct_rex_to_u8 False False False (and (u8_of_ireg x50) 8 \<noteq> 0)), 211,
            construct_modsib_to_u8 3 7 (u8_of_ireg x50)] @
           l)) =
    Some l_bin \<Longrightarrow>
    a = Psarl_r x50 \<Longrightarrow> x64_disassemble l_bin = Some (Psarl_r x50 # l_asm)"
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
            apply ( cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done                               
          done
        done
      done
    done
  done

lemma x64assemble_disassemble_consistency_psarq_r :"\<And>x51a.
      (\<And>l_bin. x64_assemble l_asm = Some l_bin \<Longrightarrow> x64_disassemble l_bin = Some l_asm) \<Longrightarrow>
      (case x64_assemble l_asm of None \<Rightarrow> None
       | Some l \<Rightarrow>
           Some
            ([or 64 (construct_rex_to_u8 True False False (and (u8_of_ireg x51a) 8 \<noteq> 0)), 211,
              construct_modsib_to_u8 3 7 (u8_of_ireg x51a)] @
             l)) =
      Some l_bin \<Longrightarrow>
      a = Psarq_r x51a \<Longrightarrow> x64_disassemble l_bin = Some (Psarq_r x51a # l_asm)"
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
            apply ( cases rd, auto simp add: bitfield_insert_u8_def Let_def ireg_of_u8_def)
            done                               
          done
        done
      done
    done
  done

end