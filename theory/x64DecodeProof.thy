theory x64DecodeProof
imports
  Main
  rBPFCommType
  x64Assembler x64Disassembler BitsOpMore BitsOpMore2 BitsOpMore3 BitsOpMore4
  x64DecodeProofAux
begin
(* It may take more than one hour to run this proof *)
declare if_split_asm [split]

(*fun x64_encode :: "instruction \<Rightarrow> x64_bin option" where
"x64_encode ins = (
  case ins of
  \<comment> \<open> P518 `Operand-size override prefix is encoded using 66H` \<close> 
  \<comment> \<open> P2887 `ROL : register by immediate count` -> `0x66 1100 000w : 11 000 reg : imm8` \<close>
  Prolw_ri rd n \<Rightarrow>
    let (prefix:: u8) = 0x66 in
    let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> `0R0B` \<close>
        False \<comment> \<open> W \<close>
        False \<comment> \<open> R \<close>
        False \<comment> \<open> X \<close>
        (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
        ) in
    let (op:: u8) = 0xc1 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b000 (u8_of_ireg rd) in
    let (imm::u8) = ucast n in
    if rex = 0x40 then
      Some [prefix, op, rop, imm]
    else*)

(*definition x64_decode :: "nat \<Rightarrow> x64_bin \<Rightarrow> (nat * instruction) option" where
"x64_decode pc l_bin = (
  let h = l_bin!pc in
    \<comment> \<open> R1 [opcode] \<close>
    if h = 0x90 then 
      \<comment> \<open> P2884 `NOP – No Operation` -> `1001 0000` \<close> 
      Some (1, Pnop)
    else if h = 0x99 then
      Some (1, Pcdq)
    else if h = 0xc3 then
      \<comment> \<open> P2887 ` RET near` -> ` 1100 0011` \<close>
      Some (1, Pret)
    else if h = 0x99 then
      Some (1, Pcdq)
    \<comment> \<open> R7 legacy \<close>
    else if h = 0x66 then  \<comment> \<open> 16*)

(*lemma "ins = Pmov_mr (Addrmode (Some dst) None dis) src M8 \<Longrightarrow> x64_decode x (the (x64_encode ins )) = Some (y,ins)"
  apply (cases ins; simp_all)
  apply(unfold x64_decode_def Let_def)
  apply(simp add: construct_rex_to_u8_def construct_modsib_to_u8_def)
  apply(simp split del:if_split)
*)

lemma x64_encode_decode_consistency:
  "list_in_list l_bin pc l \<Longrightarrow> Some l_bin = x64_encode ins \<Longrightarrow>
    x64_decode pc l = Some (length l_bin, ins)"
  sorry

lemma x64_encodes_decodes_consistency:
  "list_in_list l_bin pc l \<Longrightarrow> Some l_bin = x64_encodes_suffix insns \<Longrightarrow>
    x64_decodes pc l = Some v \<Longrightarrow> insns = map snd v"
  apply(induct insns,simp_all)
  subgoal
    apply(unfold x64_encodes_suffix_def x64_encodes_def x64_decodes_def Let_def, simp_all) 
    done
  subgoal for a insns1 apply(unfold x64_encodes_suffix_def x64_encodes_def x64_decodes_def Let_def) 
  (*using  x64_encode_decode_consistency x64_decodes_def x64_encodes_suffix_def x64_encodes_def *)
 (* 
 apply (cases ins; simp_all)
                                                                                                  
  subgoal for dst src
  \<comment> \<open> Pmovl_rr \<close> 
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False (and (u8_of_ireg src) 8 \<noteq> 0) False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64"; simp_all add: construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src
  \<comment> \<open> Pmovq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm
  \<comment> \<open> Pmovl_ri  \<close>
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64";
        simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal \<comment> \<open> rex = 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done

    subgoal \<comment> \<open> rex <> 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(pc+3)" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst imm
 \<comment> \<open> Pmovq_ri\<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    using list_in_list_u8_list_of_u64_simp_sym [of imm "(Suc (Suc pc))" l]
    using length_u8_list_of_u64_eq_8
    apply (cases dst; simp_all add: bitfield_insert_u8_def x64_decode_def ireg_of_u8_def Suc3_eq_add_3 add.commute)
    done

  subgoal for dst addr chunk
  \<comment> \<open> Pmov_rm \<close>
    apply (cases addr, simp)
    subgoal for base index2 ofs
      apply (cases base; simp)
      subgoal for base_reg
        apply (cases index2; simp add: Let_def)
        subgoal \<comment> \<open> ofs < u8 /\ index2 = None  /\ not rex \<close>
          apply (cases chunk; simp)
          apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def
              bitfield_insert_u8_def Let_def)
          using scast_u32_scast_u8_eq
          apply (cases dst; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def)
          done

        subgoal \<comment> \<open> ofs < u8 /\ index2 = None  /\ has rex \<close>

          using scast_u32_scast_u8_eq
          apply (cases chunk; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
            bitfield_insert_u8_def Let_def)
          subgoal \<comment> \<open> index2 = None  /\ has rex  /\ M32 \<close>
            apply (cases dst; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                  bitfield_insert_u8_def  Suc3_eq_add_3 add.commute)
            done
          subgoal \<comment> \<open> index2 = None  /\ has rex  /\ M64 \<close>
            apply (cases dst; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                  bitfield_insert_u8_def  Suc3_eq_add_3 add.commute)
            done
          done 

        subgoal \<comment> \<open> ofs > u8 /\ index2 = None  /\ not rex \<close>
          apply (cases chunk; simp; erule conjE)
          apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def
              bitfield_insert_u8_def Let_def)

          using list_in_list_u8_list_of_u32_simp_sym [of ofs "(Suc (Suc pc))" l]
          using length_u8_list_of_u32_eq_4

          apply (cases dst; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                    bitfield_insert_u8_def Suc3_eq_add_3 add.commute)
          done 

        subgoal \<comment> \<open> ofs > u8 /\ index2 = None  /\ has rex \<close>
          apply (cases chunk; simp; erule conjE; erule conjE; erule conjE)
          apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def
              bitfield_insert_u8_def Let_def)
          subgoal  \<comment> \<open> M32 \<close>
            using list_in_list_u8_list_of_u32_simp_sym [of ofs "(Suc (Suc (Suc pc)))" l]
            using length_u8_list_of_u32_eq_4
            apply (cases dst; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                    bitfield_insert_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
            done
          subgoal  \<comment> \<open> M64 \<close>
            using list_in_list_u8_list_of_u32_simp_sym [of ofs "(Suc (Suc (Suc pc)))" l]
            using length_u8_list_of_u32_eq_4
            apply (cases dst; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                    bitfield_insert_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
            done
          done

        subgoal for index22\<comment> \<open> index2 = Some \<close>
          apply(cases chunk; cases index22;simp_all)
          subgoal for index_reg scale
            apply (erule conjE; erule conjE; erule conjE; erule conjE)
            using list_in_list_u8_list_of_u32_simp_sym [of "ofs" " (Suc (Suc (Suc (Suc pc))))" l]
            using length_u8_list_of_u32_eq_4
            using construct_modsib_to_u8_imply_index_reg [of " (and (u8_of_ireg dst) 8 \<noteq> 0)" index_reg base_reg "l ! pc" scale "l ! (Suc (Suc (Suc pc)))"]
            using construct_modsib_to_u8_imply_base_reg  [of " (and (u8_of_ireg dst) 8 \<noteq> 0)" index_reg base_reg "l ! pc" scale "l ! (Suc (Suc (Suc pc)))"]
            using construct_modsib_to_u8_imply_scale [of scale index_reg base_reg "l !  Suc (Suc (Suc pc))"]
              apply (cases dst; simp add: construct_rex_to_u8_def  construct_modsib_to_u8_def)
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
            done
          done
        done
      done
    done


  subgoal for addr r1 chunk
    \<comment> \<open> Pmov_mr \<close> 
      \<comment> \<open> Pmov_rm \<close>
    apply (cases addr ;simp_all)
    subgoal for base index2 ofs
      apply (cases base; simp_all)
      subgoal for base_reg
        apply (cases index2; simp add: Let_def)

        subgoal \<comment> \<open> ofs < u8 \<and> index2 = None \<and>  not rex \<close>
        using scast_u32_scast_u8_eq
          apply (cases chunk; simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def
              bitfield_insert_u8_def Let_def)
          apply (erule conjE; erule conjE)
          subgoal by(cases r1; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def )
          subgoal by(cases r1; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def  Suc3_eq_add_3 add.commute)
          subgoal by(cases r1; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def )
          done


        subgoal \<comment> \<open> ofs < u8 \<and> index2 = None \<and> has rex \<close>
          using scast_u32_scast_u8_eq
          apply (cases chunk; simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def
              bitfield_insert_u8_def Let_def)
               apply (erule conjE; erule conjE;erule conjE)
          subgoal
            by (cases r1; simp; cases base_reg;simp_all add: x64_decode_def Let_def ireg_of_u8_def
                  bitfield_insert_u8_def Suc3_eq_add_3 add.commute )
          subgoal
            by (cases r1; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def  Suc3_eq_add_3 add.commute)
          subgoal
            by (cases r1; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def  Suc3_eq_add_3 add.commute)
          subgoal
            by (cases r1; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def  Suc3_eq_add_3 add.commute)
            done



        subgoal \<comment> \<open> ofs > u8 /\ index2 = None  /\ not rex \<close>
          apply (cases chunk; simp; erule conjE)
          apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)

          using list_in_list_u8_list_of_u32_simp_sym [of ofs "(Suc (Suc pc))" l]
          using length_u8_list_of_u32_eq_4

          apply (cases r1; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                    bitfield_insert_u8_def Suc3_eq_add_3 add.commute)
          done 

        subgoal \<comment> \<open> ofs > u8 /\ index2 = None  /\ has rex \<close>
          apply (cases chunk; simp; erule conjE; erule conjE; erule conjE)
          apply (unfold construct_rex_to_u8_def construct_modsib_to_u8_def
              bitfield_insert_u8_def Let_def)
          subgoal  \<comment> \<open> M32 \<close>
            using list_in_list_u8_list_of_u32_simp_sym [of ofs "(Suc (Suc (Suc pc)))" l]
            using length_u8_list_of_u32_eq_4
            apply (cases r1; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                    bitfield_insert_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
            done
          subgoal  \<comment> \<open> M64 \<close>
            using list_in_list_u8_list_of_u32_simp_sym [of ofs "(Suc (Suc (Suc pc)))" l]
            using length_u8_list_of_u32_eq_4
            apply (cases r1; simp; cases base_reg; simp add: x64_decode_def Let_def ireg_of_u8_def
                    bitfield_insert_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
            done
          done

        subgoal for index22\<comment> \<open> index2 = Some \<close>
          apply(cases chunk; cases index22;simp_all)
          subgoal for index_reg scale
            apply (erule conjE; erule conjE; erule conjE; erule conjE)
            using list_in_list_u8_list_of_u32_simp_sym [of "ofs" " (Suc (Suc (Suc (Suc pc))))" l]
            using length_u8_list_of_u32_eq_4
            using construct_modsib_to_u8_imply_index_reg [of " (and (u8_of_ireg r1) 8 \<noteq> 0)" index_reg base_reg "l ! pc" scale "l ! (Suc (Suc (Suc pc)))"]
            using construct_modsib_to_u8_imply_base_reg  [of " (and (u8_of_ireg r1) 8 \<noteq> 0)" index_reg base_reg "l ! pc" scale "l ! (Suc (Suc (Suc pc)))"]
            using construct_modsib_to_u8_imply_scale [of scale index_reg base_reg "l !  Suc (Suc (Suc pc))"]
              apply (cases r1; simp add: construct_rex_to_u8_def  construct_modsib_to_u8_def)
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
              subgoal by (cases base_reg; simp; cases index_reg; simp add: x64_decode_def
                     bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) 
            done
          done
        done
      done
    done

  subgoal for addr imm chunk
    \<comment> \<open> Pmov_mi \<close> 
    apply(cases chunk, simp_all)
    apply (cases addr, simp)
    subgoal for base index2 ofs
      apply (cases base, simp_all)
      subgoal for base_reg
        apply (cases index2; simp add: Let_def; erule conjE; erule conjE; erule conjE; erule conjE)
        subgoal
          apply (auto simp add: construct_rex_to_u8_def construct_modsib_to_u8_def)
          subgoal
            using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc (Suc (Suc pc))))" l]
            using length_u8_list_of_u32_eq_4 
            using scast_u32_scast_u8_eq
              by (cases base_reg;auto simp add: x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
            subgoal
            using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc (Suc (Suc pc))))" l]
            using length_u8_list_of_u32_eq_4 
            using scast_u32_scast_u8_eq
            by (cases base_reg;auto simp add: x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
          done
        subgoal
          apply (simp add: list_in_list_concat length_u8_list_of_u32_eq_4)
          using list_in_list_u8_list_of_u32_simp_sym [of "ofs" "(Suc (Suc (Suc pc)))" l]
          using list_in_list_u8_list_of_u32_simp_sym [of imm "(7 + pc)" l]
          apply (cases base_reg; simp add: x64_decode_def  construct_rex_to_u8_def bitfield_insert_u8_def 
              Let_def construct_modsib_to_u8_def ireg_of_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
          done
        done
      done
    done

  subgoal for test dst src
    \<comment> \<open> Pcmovl \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases test; simp; cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    done


  subgoal for test dst src
    \<comment> \<open> Pcmovq \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases test; simp; cases dst; simp; cases src, simp_all add: x64_decode_def bitfield_insert_u8_def
          Let_def ireg_of_u8_def cond_of_u8_def  Suc3_eq_add_3 add.commute)
    done


  subgoal for dst src
    \<comment> \<open> Pxchgq_rr \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst addr chunk
    \<comment> \<open> Pxchgq_rm \<close> 
    apply (cases chunk; simp_all)
    apply (cases addr, simp)
    subgoal for base index2 ofs
      apply (cases base;simp)
      subgoal for base_reg
        apply (cases index2; simp add: Let_def)
        subgoal for index22
          apply (cases index22, simp_all)
          subgoal for index_reg scale
            apply (erule conjE;erule conjE;erule conjE;erule conjE)

            using list_in_list_u8_list_of_u32_simp_sym [of ofs "(Suc (Suc (Suc (Suc pc))))" l]
            using length_u8_list_of_u32_eq_4
            using construct_modsib_to_u8_imply_index_reg [of "(and (u8_of_ireg dst) 8 \<noteq> 0)" index_reg base_reg "l ! pc" scale "l ! Suc (Suc (Suc pc))"]
            using construct_modsib_to_u8_imply_base_reg [of "(and (u8_of_ireg dst) 8 \<noteq> 0)" index_reg base_reg "l ! pc" scale "l ! Suc (Suc (Suc pc))"]
            using construct_modsib_to_u8_imply_scale [of scale index_reg base_reg "l ! Suc (Suc (Suc pc))"]
                       (*      apply (simp_all add: construct_rex_to_u8_def construct_modsib_to_u8_def)*)
              apply (cases dst; simp add: construct_rex_to_u8_def  construct_modsib_to_u8_def)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)

              subgoal by (cases index_reg; simp; cases base_reg; simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                      Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
              done 
            done
        done
      done
    done
  

  subgoal for dst src
    \<comment> \<open> Pmovsq_rr \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal 
    \<comment> \<open> Pcdq \<close>
    apply(unfold Let_def x64_decode_def; simp)
    done

  subgoal 
    \<comment> \<open> Pcqo \<close>
    apply(unfold Let_def x64_decode_def; simp)
    done

  subgoal for dst addr
    \<comment> \<open> Pleaq \<close>
    apply (cases addr, simp)
    subgoal for base index2 ofs
      apply (cases base;simp)
      subgoal for base_reg
        apply (cases index2; simp add: Let_def)
        subgoal
          apply (erule conjE;erule conjE;erule conjE)
          using scast_u32_scast_u8_eq
          subgoal by (cases dst; simp;cases base_reg; simp add: construct_rex_to_u8_def  construct_modsib_to_u8_def 
                x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
          done
        subgoal
          apply (erule conjE;erule conjE;erule conjE;erule conjE)
          using list_in_list_u8_list_of_u32_simp_sym [of ofs "(Suc (Suc (Suc pc)))" l]
          using length_u8_list_of_u32_eq_4
          apply (cases dst; simp;cases base_reg; simp add: construct_rex_to_u8_def  construct_modsib_to_u8_def 
                x64_decode_def Let_def ireg_of_u8_def
                bitfield_insert_u8_def Suc3_eq_add_3 Suc4_eq_add_4 add.commute)
          done
        done
      done
    done

  subgoal for dst
    \<comment> \<open> Pnegl \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst
    \<comment> \<open> Pnegq \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done 

  subgoal for dst src 
    \<comment> \<open> Paddq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; simp;cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          Suc3_eq_add_3 add.commute)
    done

  subgoal for dst src 
    \<comment> \<open> Paddl_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm 
    \<comment> \<open> Paddl_ri \<close> 
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64";
        simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal \<comment> \<open> rex = 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
e
    subgoal \<comment> \<open> rex <> 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(pc+3)" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done


  subgoal for dst imm 
    \<comment> \<open> Paddw_ri \<close> 
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64";
        simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal \<comment> \<open> rex = 0x40  \<close>
      using list_in_list_u8_list_of_u16_simp_sym [of imm " (Suc (Suc (Suc pc)))" l]
      using length_u8_list_of_u16_eq_2
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done

    subgoal \<comment> \<open> rex <> 0x40  \<close>
      using list_in_list_u8_list_of_u16_simp_sym [of imm "(Suc (Suc (Suc (Suc pc))))" l]
      using length_u8_list_of_u16_eq_2
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done



  subgoal for addr imm chunk
  \<comment> \<open> Paddq_mi \<close> 
    apply (cases chunk, simp_all)
    apply (cases addr)
    subgoal for base index2 ofs
      apply simp
      apply (cases base, simp_all)
      subgoal for base_reg
        apply (cases index2, simp_all)
        subgoal for index22
          apply (cases index22, simp_all)
          subgoal for index_reg scale
            apply (erule conjE; erule conjE; erule conjE; erule conjE)
            apply (simp add: list_in_list_concat; erule conjE)

            using construct_modsib_to_u8_imply_index_reg [of "False" index_reg base_reg "l ! pc" scale "l ! Suc (Suc (Suc pc))"]
            using construct_modsib_to_u8_imply_base_reg [of "False" index_reg base_reg "l ! pc" scale "l ! Suc (Suc (Suc pc))"]
            using construct_modsib_to_u8_imply_scale [of scale index_reg base_reg "l ! (pc+3)"]
            using list_in_list_u8_list_of_u32_simp_sym [of "ofs" "(pc+4)" l]
            using length_u8_list_of_u32_eq_4
            using list_in_list_u8_list_of_u32_simp_sym [of imm "(pc+8)" l]
(*
            apply (cases base_reg; simp; cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4) *)
            apply (cases base_reg; simp)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            subgoal by (cases index_reg; simp add: construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            done
          done
        done
      done
    done

  subgoal for dst src 
    \<comment> \<open> Psubl_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src 
    \<comment> \<open> Psubq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm 
    \<comment> \<open> Psubl_ri \<close> 
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64";
        simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal \<comment> \<open> rex = 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done

    subgoal \<comment> \<open> rex <> 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(pc+3)" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst 
    \<comment> \<open> Pmull_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pmulq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pimull_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pimulq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pdivl_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pdivq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pidivl_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst 
    \<comment> \<open> Pidivq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src 
    \<comment> \<open> Pandl_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm 
    \<comment> \<open> Pandl_ri\<close> 
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64";
        simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal \<comment> \<open> rex = 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done

    subgoal \<comment> \<open> rex <> 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(pc+3)" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst src
    \<comment> \<open> Pandq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src 
    \<comment> \<open> Porl_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm 
    \<comment> \<open> Porl_ri\<close> 
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64";
        simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal \<comment> \<open> rex = 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done

    subgoal \<comment> \<open> rex <> 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(pc+3)" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done


  subgoal for dst src
    \<comment> \<open> Porq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src 
    \<comment> \<open> Pxorl_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src
    \<comment> \<open> Pxorq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm 
    \<comment> \<open> Pxorl_ri\<close> 
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64";
        simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal \<comment> \<open> rex = 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done

    subgoal \<comment> \<open> rex <> 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(pc+3)" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  
  subgoal for dst imm
    \<comment> \<open> Pshll_ri \<close>
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64",
        simp_all)

    subgoal \<comment> \<open> rex = 0x40 \<close>
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          construct_rex_to_u8_def construct_modsib_to_u8_def)
      done

    subgoal  \<comment> \<open> rex <> 0x40 \<close>
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          construct_rex_to_u8_def construct_modsib_to_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst
    \<comment> \<open> Pshlq_ri \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def  Suc3_eq_add_3 add.commute)
    done

  subgoal for dst
  \<comment> \<open> Pshll_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst
  \<comment> \<open> Pshlq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm
    \<comment> \<open> Pshrl_ri \<close>
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64",
        simp_all)

    subgoal \<comment> \<open> rex = 0x40 \<close>
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          construct_rex_to_u8_def construct_modsib_to_u8_def)
      done

    subgoal  \<comment> \<open> rex <> 0x40 \<close>
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          construct_rex_to_u8_def construct_modsib_to_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst
    \<comment> \<open> Pshrq_ri \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def  Suc3_eq_add_3 add.commute)
    done


  subgoal for dst
  \<comment> \<open> Pshrl_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done     

  subgoal for dst
  \<comment> \<open> Pshrq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm
    \<comment> \<open> Psarl_ri \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def  Suc3_eq_add_3 add.commute)
    done

  subgoal for dst
  \<comment> \<open> Psarq_ri \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def  Suc3_eq_add_3 add.commute)
    done

  subgoal for dst
  \<comment> \<open> Psarl_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done  

  subgoal for dst
  \<comment> \<open> Psarq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done  

  subgoal for dst imm
    \<comment> \<open> Prolw_ri \<close>
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64",
        simp_all)

    subgoal \<comment> \<open> rex = 0x40 \<close>
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          construct_rex_to_u8_def construct_modsib_to_u8_def Suc3_eq_add_3 add.commute)
      done

    subgoal  \<comment> \<open> rex <> 0x40 \<close>
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          construct_rex_to_u8_def construct_modsib_to_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst
    \<comment> \<open> Pbswapl \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst
    \<comment> \<open> Pbswapq \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst
    \<comment> \<open> Ppushl_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for imm
    \<comment> \<open> Ppushl_i \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal 
      using list_in_list_u8_list_of_u32_simp_sym [of imm  "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply(auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for addr chunk 
    \<comment> \<open> Ppushq_m \<close> 
    apply (cases chunk,simp_all)
    apply (cases addr, simp_all)
    subgoal for base index2 ofs
      apply (cases base;simp)
      subgoal for base_reg
        apply (cases index2; simp add: Let_def)
        subgoal for index22
          apply (cases index22, simp_all)
          subgoal for index_reg scale
            apply (erule conjE;erule conjE;erule conjE;erule conjE)
            using list_in_list_u8_list_of_u32_simp_sym [of ofs "(Suc (Suc (Suc (Suc pc))))" l]
            using length_u8_list_of_u32_eq_4
            using construct_modsib_to_u8_imply_index_reg [of "False" index_reg base_reg "l ! pc" scale "l ! Suc (Suc (Suc pc))"]
            using construct_modsib_to_u8_imply_base_reg [of "False" index_reg base_reg "l ! pc" scale "l ! Suc (Suc (Suc pc))"]
            using construct_modsib_to_u8_imply_scale [of scale index_reg base_reg "l ! Suc (Suc (Suc pc))"]
            subgoal by(cases base_reg; simp; cases index_reg; simp add: 
                  construct_rex_to_u8_def construct_modsib_to_u8_def
                    x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
                    add.commute Suc3_eq_add_3 Suc4_eq_add_4)
            done
          done
        done
      done
    done

  subgoal for dst
    \<comment> \<open> Ppopl_i \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src
    \<comment> \<open> Ptestl_rr \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src
    \<comment> \<open> Ptestq_rr \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm
  \<comment> \<open> Ptestl_ri  \<close>
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64";
        simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal \<comment> \<open> rex = 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done

    subgoal \<comment> \<open> rex <> 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(pc+3)" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst imm
  \<comment> \<open> Ptestq_ri  \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc (Suc pc)))" l]
    using length_u8_list_of_u32_eq_4
    apply (cases dst; simp_all add: bitfield_insert_u8_def x64_decode_def ireg_of_u8_def Suc3_eq_add_3 add.commute)
    done

  subgoal for dst src
    \<comment> \<open> Pcmpl_rr \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst src
    \<comment> \<open> Pcmpq_rr \<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def;  erule conjE; erule conjE)
    subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for dst imm
  \<comment> \<open> Pcmpl_ri  \<close>
    apply (unfold Let_def)
    apply (cases "construct_rex_to_u8 False False False (and (u8_of_ireg dst) 8 \<noteq> 0) = 64";
        simp_all add:construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE)
    subgoal \<comment> \<open> rex = 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done

    subgoal \<comment> \<open> rex <> 0x40  \<close>
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(pc+3)" l]
      using length_u8_list_of_u32_eq_4
      apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def
          ireg_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst imm
  \<comment> \<open> Pcmpq_ri\<close>
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def; erule conjE; erule conjE; erule conjE)
    using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc (Suc pc)))" l]
    using length_u8_list_of_u32_eq_4
    apply (cases dst; simp_all add: bitfield_insert_u8_def x64_decode_def ireg_of_u8_def Suc3_eq_add_3 add.commute)
    done

  subgoal for test imm
    \<comment> \<open> Pjcc \<close>
    subgoal 
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc (Suc pc))" l]
      using length_u8_list_of_u32_eq_4
      apply (cases test; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
             cond_of_u8_def Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for imm
    \<comment> \<open> Pjmp \<close>
    subgoal 
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc pc)" l]
      using length_u8_list_of_u32_eq_4
      apply (auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
            Suc3_eq_add_3 add.commute)
      done
    done

  subgoal for dst 
    \<comment> \<open> Pcall_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done

  subgoal for imm 
    \<comment> \<open> Pcall_i \<close> 
    subgoal 
      using list_in_list_u8_list_of_u32_simp_sym [of imm "(Suc pc)" l]
      using length_u8_list_of_u32_eq_4
      apply (auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
            Suc3_eq_add_3 add.commute)
      done
    done

  subgoal 
    \<comment> \<open> Pret \<close>
    apply(unfold Let_def x64_decode_def; simp)
    done

  subgoal 
    \<comment> \<open> Prdtsc \<close>
    apply(unfold Let_def x64_decode_def; simp)
    done

  subgoal 
    \<comment> \<open> Pnop \<close>
    apply(unfold Let_def x64_decode_def; simp)
    done
  done*)

declare if_split_asm [split del]
end