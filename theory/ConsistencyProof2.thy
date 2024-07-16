theory ConsistencyProof2
imports
  Main
  rBPFCommType rBPFSyntax Mem Assembler Disassembler ConsistencyCommProof
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
(**r wait for 4 min because there are 100+ if-cases *)
              apply (split if_split_asm, auto simp add: insn_def split: if_split_asm)+
              (*
              apply (split if_split_asm)
              subgoal by (auto simp add: insn_def split: if_split_asm)
              apply (split if_split_asm, auto)
              subgoal by (auto simp add: insn_def split: if_split_asm) *)

              done
            done
          done
        done
      done
    done

(*
declare if_split_asm [split del] *)
end