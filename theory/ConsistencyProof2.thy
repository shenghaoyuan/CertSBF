theory ConsistencyProof2
imports
  Main
  rBPFCommType rBPFSyntax Assembler Disassembler ConsistencyCommProof
begin
(*
declare if_split_asm [split] *)

lemma "(if (0::u64) < 0 \<or> (10::u64) < 0 then None else Some True) = Some True" 
  by fastforce

(** WHY ?

value "(0::64 sword) < - 0x8000"
value "(0::64 sword) <s - 0x8000" *)

(*
value "- (0x8000:: i64)"
value "(0:: i64)"
value "(0::64 sword) <s ((- 0x8000) :: i64)" *)

lemma u4_breg_src_i64 [simp]: "u4_to_bpf_ireg (bpf_src x1) = Some aa \<Longrightarrow> (bpf_ireg2u4 aa) = (ucast (bpf_src x1))"
  by (unfold u4_to_bpf_ireg_def, auto simp add: split: if_split_asm)

(*
lemma disassemble_lddw_assemble_one_instruction[simp]:
  "bpf_opc a = 0x18 \<Longrightarrow> disassemble_lddw (bpf_dst a) (bpf_imm a) aa = Some x1 \<Longrightarrow>
  assemble_one_instruction x1 = Some a"
  apply (unfold disassemble_lddw_def)
  apply (cases "bpf_opc aa = 0 \<and> bpf_dst aa = 0 \<and> bpf_src aa = 0 \<and> bpf_off aa = 0", auto)
  apply (cases "u4_to_bpf_ireg (bpf_dst a)", auto)
  apply (unfold insn_def, auto)
  subgoal for ab  
    apply (cases ab, auto simp add: u4_to_bpf_ireg_def)
    done
  subgoal for ab
    
    done

  done *)

lemma disassemble_lddw_some[simp]:
  "bpf_opc a = 0x18 \<Longrightarrow>
  u4_to_bpf_ireg (bpf_dst a) = Some d \<Longrightarrow>
  disassemble_lddw a aa = Some x \<Longrightarrow>
  x = BPF_LD_IMM d (bpf_imm a) (bpf_imm aa)"
  apply (unfold disassemble_lddw_def)
  apply (cases "bpf_src a = 0 \<and> bpf_off a = 0 \<and> bpf_opc aa = 0 \<and> bpf_dst aa = 0 \<and> bpf_src aa = 0 \<and> bpf_off aa = 0")
  apply auto
  done

lemma disassemble_assemble_consistency: "disassemble l_bin = Some l_asm \<Longrightarrow> assemble l_asm = Some l_bin"
  apply (induction l_asm arbitrary: l_bin)

(**r l_asm = [] *)
  subgoal for l_bin
    apply (cases l_bin, auto simp add: split: if_split_asm)

    subgoal for a l_a
      apply (cases "bpf_opc a = 0x18", auto)

      subgoal
        apply (cases l_a, auto)

        subgoal for aa l_aa
          apply (cases "disassemble_lddw a aa", auto)
          apply (cases "disassemble l_aa", auto)
          done
        done
      done

    subgoal for a l_a
      apply (cases "disassemble_one_instruction a", auto)
      apply (cases "disassemble l_a", auto)
      done
    done

(**r l_asm = x1 + l_asm *)
  subgoal for x1 l_asm l_bin
    apply (cases l_bin, auto simp add: split: if_split_asm)

    subgoal for a l_a
      apply (cases "bpf_opc a = 0x18", auto)

(**r + LD_IMM  *)
      subgoal
        apply (cases l_a, auto)

        subgoal for aa l_aa
          apply (cases "disassemble_lddw a aa", auto)
          apply (cases "disassemble l_aa", auto)
          apply (unfold disassemble_lddw_def)
          apply (cases "bpf_src a = 0 \<and> bpf_off a = 0 \<and> bpf_opc aa = 0 \<and> bpf_dst aa = 0 \<and> bpf_src aa = 0 \<and> bpf_off aa = 0", auto)
          apply (cases "u4_to_bpf_ireg (bpf_dst a)", auto)
          subgoal for ab
            apply (unfold insn_def, auto)
            using u4_to_bpf_ireg_dst_some_range by blast
            done
          done
        done

(**r - LD_IMM *)
      subgoal for a l_a
        apply (cases "disassemble l_a")
        subgoal
          apply (cases "disassemble_one_instruction a", auto)
          done

        subgoal for b
          apply (unfold disassemble_one_instruction_def)
          apply (cases "10 < bpf_dst a \<or> 10 < bpf_src a", auto)
          apply (cases "u4_to_bpf_ireg (bpf_dst a)", auto)
          subgoal for c
            apply (cases "u4_to_bpf_ireg (bpf_src a)", auto)
            subgoal for d
              apply (cases "bpf_opc a = 113", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 105", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 97", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 121", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 114", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 106", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 98", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 122", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 115", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 107", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 99", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 123", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)

              apply (cases "bpf_opc a = 0x04", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x0c", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x14", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x1c", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x24", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x2c", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x34", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x3c", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x44", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x4c", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x54", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x5c", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x64", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x6c", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x74", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x7c", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x84", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x94", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x9c", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xa4", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xac", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xb4", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xbc", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xc4", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xcc", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xd4", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xdc", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)

              apply (cases "bpf_opc a = 0x07", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x0f", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x17", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x1f", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x27", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x2f", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x37", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x3f", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x47", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x4f", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x57", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x5f", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x67", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x6f", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x77", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x7f", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x87", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x97", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x9f", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xa7", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xaf", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xb7", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xbf", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xc7", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xcf", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)

              apply (cases "bpf_opc a = 0xf7", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)

              apply (cases "bpf_opc a = 0x86", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x8e", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x96", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x9e", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x36", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x3e", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xb6", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xbe", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)

              apply (cases "bpf_opc a = 0x46", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x4e", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x56", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x5e", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x66", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x6e", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x76", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x7e", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)

              apply (cases "bpf_opc a = 0xc6", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xce", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xd6", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xde", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)

              apply (cases "bpf_opc a = 0xe6", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xee", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xf6", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xfe", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)

              apply (cases "bpf_opc a = 0x05", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)

              apply (cases "bpf_opc a = 0x15", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x1d", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x25", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x2d", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x35", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x3d", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xa5", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xad", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xb5", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xbd", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x45", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x4d", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x55", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x5d", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x65", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x6d", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x75", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x7d", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xc5", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xcd", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xd5", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0xdd", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)

              apply (cases "bpf_opc a = 0x8d", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (cases "bpf_opc a = 0x85", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)

              apply (cases "bpf_opc a = 0x95", auto)
              subgoal by (auto simp add: insn_def split: if_split_asm)


              done
            done
          done
        done
      done
    done

(*
declare if_split_asm [split del] *)
end