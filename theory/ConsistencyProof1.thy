theory ConsistencyProof1
imports
  Main
  rBPFCommType rBPFSyntax Mem Assembler Disassembler ConsistencyCommProof
begin

declare if_split_asm [split]

lemma assemble_disassemble_consistency: "assemble l_asm = Some l_bin \<Longrightarrow> disassemble l_bin = Some l_asm"
(*
proof (induction l_asm arbitrary: l_bin)
case Nil
then show ?case by force
next
case (Cons x1 l_asm)
then show ?case
proof -

assume IH: "(\<And>l_bin. assemble l_asm = Some l_bin \<Longrightarrow> disassemble l_bin = Some l_asm)"
assume Hx1: "assemble (x1 # l_asm) = Some l_bin"

from Hx1 have "(
    case (assemble_one_instruction x1) of
      None \<Rightarrow> None |
      Some h_i \<Rightarrow> (
        case (assemble l_asm) of
        None \<Rightarrow> None |
        Some tl_i \<Rightarrow> (
          case x1 of
          BPF_LD_IMM dst i1 i2 \<Rightarrow> (
            case (insn 0 0 0 0 (scast i2)) of
            None \<Rightarrow> None |
            Some h_i2 \<Rightarrow> Some (h_i#h_i2#tl_i))|
           _ \<Rightarrow> Some (h_i#tl_i) )) ) = Some l_bin" by simp

thm Hx1 *)

  apply (induction l_asm arbitrary: l_bin)
(**r l_asm = [] *)
  subgoal
    apply simp
    done
(**r l_asm = hd # tl *)
  subgoal for x1 l_asm
    apply simp 
    apply (cases "assemble_one_instruction x1", auto)
    apply (cases "assemble l_asm", auto)
    subgoal for a aa
      apply (cases "x1", auto simp add: insn_def) (**r , auto split: option.split *)
        (**r LD_IMM *)
      subgoal for x11 x12 x13
        apply (unfold disassemble_lddw_def, auto)   
        done

        (**r LDX + LD_IMM *)
      subgoal for x21 x22 x23 x24
        apply (cases x21, auto)
        done

        (**r LDX - LD_IMM *)
      subgoal for x1 x2 x3 x4
        apply (unfold disassemble_one_instruction_def)
        apply (cases x1, auto)
        done

(**r ST + LD_IMM *)
      subgoal for x31 x32 x33 x34
        apply (cases x33, auto)
        apply (unfold insn_def, cases x31, auto)
        apply (cases x31, auto)
        done

(**r ST - LD_IMM *)
      subgoal for x31 x32 x33 x34

        apply (cases x33, auto)
        subgoal  
          apply (unfold insn_def, cases x31, auto, unfold disassemble_one_instruction_def, auto)
          done
        subgoal for x1
          apply (unfold insn_def, cases x31, auto, unfold disassemble_one_instruction_def, auto)
          done
        done

(**r ALU + LD_IMM *)
      subgoal for x1 x2 x3
        apply (cases x3; auto)
         apply (unfold insn_def, cases x1; auto)
        apply (unfold insn_def, cases x1; auto)
        done

(**r ALU - LD_IMM *)
      subgoal for x1 x2 x3
        apply (cases x3, auto)
        subgoal  
          apply (unfold insn_def, cases x1, auto, unfold disassemble_one_instruction_def, auto)                                       
          done
        subgoal  
          apply (unfold insn_def, cases x1, auto, unfold disassemble_one_instruction_def, auto)                                        
          done
        done  

(**r NEG32 *)
      subgoal for x1
        apply (unfold disassemble_one_instruction_def, auto)
        done  

(**r LE *)
      subgoal for x1 x2
        apply (unfold disassemble_one_instruction_def, auto)
        done  

(**r BE *)
      subgoal for x1 x2
        apply (unfold disassemble_one_instruction_def, auto)
        done  
(**r ALU64 + LD_IMM *)
      subgoal for x1 x2 x3
        apply (cases x3; auto)
        apply (unfold insn_def, cases x1; auto)
        apply (unfold insn_def, cases x1; auto)
        done

(**r ALU64 - LD_IMM  *)
      subgoal for x1 x2 x3
        apply (cases x3, auto)
        subgoal  
          apply (unfold insn_def, cases x1, auto, unfold disassemble_one_instruction_def, auto)                                        
          done
        subgoal  
          apply (unfold insn_def, cases x1, auto, unfold disassemble_one_instruction_def, auto)                                        
          done
        done
   
(**r NEG64 *)
      subgoal for x1
        apply (unfold disassemble_one_instruction_def, auto)
        done  

(**r HOR64_IMM *)
      subgoal for x1 x2
        apply (unfold disassemble_one_instruction_def, auto)
        done

(**r PRQ + LD_IMM *)
      subgoal for x1 x2 x3
        apply (cases x3, auto)
        apply (unfold insn_def, cases x1, auto)
        apply (cases x1, auto)
        done

(**r PQR - LD_IMM *)
      subgoal for x1 x2 x3
        apply (cases x3, auto)
        subgoal for x1'
          apply (unfold insn_def, cases x1, auto, unfold disassemble_one_instruction_def, auto)
          done
        subgoal for xa
          apply (unfold insn_def, cases x1, auto, unfold disassemble_one_instruction_def, auto)
          done
        done

(**r PQR64 + LD_IMM *)
      subgoal for x1 x2 x3
        apply (cases x3, auto)
        apply (unfold insn_def, cases x1, auto)
        apply (cases x1, auto)
        done  

(**r PQR64 - LD_IMM *)
      subgoal for x1 x2 x3
        apply (cases x3, auto)
        subgoal for x1'
          apply (unfold insn_def, cases x1, auto, unfold disassemble_one_instruction_def, auto)
          done
        subgoal for xa
          apply (unfold insn_def, cases x1, auto, unfold disassemble_one_instruction_def, auto)
          done
        done  

(**r PQR2 + LD_IMM *)  
      subgoal for x1 x2 x3
        apply (cases x3, auto)
        apply (unfold insn_def, cases x1, auto)
        apply (cases x1, auto)
        done  

(**r PQR2 - LD_IMM *)
      subgoal for x1 x2 x3
        apply (cases x3, auto)
        subgoal for x1'
          apply (unfold insn_def, cases x1, auto, unfold disassemble_one_instruction_def, auto)
          done
        subgoal for xa
          apply (unfold insn_def, cases x1, auto, unfold disassemble_one_instruction_def, auto)
          done
        done
 
(**r JA *)
      subgoal for x1
        apply (unfold insn_def disassemble_one_instruction_def, auto)
        done

(**r JUMP + LD_IMM  *)
      subgoal for x1 x2 x3 x4
        apply (cases x3, auto)
        apply (unfold insn_def, cases x1, auto)
        apply (cases x1, auto)
        done

(**r JUMP - LD_IMM *)
      subgoal for x1 x2 x3 x4
        apply (cases x3, auto)
        subgoal for x1'
          apply (unfold insn_def, cases x1, auto, unfold disassemble_one_instruction_def, auto)
          done
        subgoal for x1'
          apply (unfold insn_def, cases x1, auto, unfold disassemble_one_instruction_def, auto)
          done
        done

(**r CALL_REG  *)
      subgoal for x1 x2
        apply (unfold insn_def disassemble_one_instruction_def, auto)
        done

(**r CALL_IMM  *)
      subgoal for x1 x2
        apply (unfold insn_def disassemble_one_instruction_def, auto)
        done

(**r EXIT *)
      apply (unfold disassemble_one_instruction_def, auto)
      done  
    done
  done

(**
apply (induction l_asm arbitrary: l_bin)



lemma assemble_disassemble_consistency: "assemble l_asm = Some l_bin \<Longrightarrow> disassemble l_bin = Some l_asm"
proof (induction l_asm arbitrary: l_bin)
case Nil
then show ?case by force
next
case (Cons x1 l_asm)
then show ?case
proof -

fix l_bin
assume IH: "(\<And>l_bin. assemble l_asm = Some l_bin \<Longrightarrow> disassemble l_bin = Some l_asm)"
assume Hx1: "assemble (x1 # l_asm) = Some l_bin"
from Hx1 have Hx2: "(
    case (assemble_one_instruction x1) of
      None \<Rightarrow> None |
      Some h_i \<Rightarrow> (
        case (assemble l_asm) of
        None \<Rightarrow> None |
        Some tl_i \<Rightarrow> (
          case x1 of
          BPF_LD_IMM dst i1 i2 \<Rightarrow> (
            case (insn 0 0 0 0 (scast i2)) of
            None \<Rightarrow> None |
            Some h_i2 \<Rightarrow> Some (h_i#h_i2#tl_i))|
           _ \<Rightarrow> Some (h_i#tl_i) )) ) = Some l_bin" by simp

           have a1:"\<exists> h_i. assemble_one_instruction x1 = Some h_i \<and> (case (assemble l_asm) of
        None \<Rightarrow> None |
        Some tl_i \<Rightarrow> (
          case x1 of
          BPF_LD_IMM dst i1 i2 \<Rightarrow> (
            case (insn 0 0 0 0 (scast i2)) of
            None \<Rightarrow> None |
            Some h_i2 \<Rightarrow> Some (h_i#h_i2#tl_i))|
           _ \<Rightarrow> Some (h_i#tl_i) )) = Some l_bin" using Hx2
           by (smt (z3) not_Some_eq option.simps(4) option.simps(5)) 
           then obtain h_i where " assemble_one_instruction x1 = Some h_i \<and> (case (assemble l_asm) of
        None \<Rightarrow> None |
        Some tl_i \<Rightarrow> (
          case x1 of
          BPF_LD_IMM dst i1 i2 \<Rightarrow> (
            case (insn 0 0 0 0 (scast i2)) of
            None \<Rightarrow> None |
            Some h_i2 \<Rightarrow> Some (h_i#h_i2#tl_i))|
           _ \<Rightarrow> Some (h_i#tl_i) )) = Some l_bin" by auto
           have a2: "\<exists> tl_i. assemble l_asm = Some tl_i \<and> (case x1 of BPF_LD_IMM dst i1 i2 \<Rightarrow> (
            case (insn 0 0 0 0 (scast i2)) of
            None \<Rightarrow> None |
            Some h_i2 \<Rightarrow> Some (h_i#h_i2#tl_i))|
           _ \<Rightarrow> Some (h_i#tl_i) ) = Some l_bin" using a1
           by (smt (z3) not_Some_eq option.simps(4) option.simps(5)) 

           
           proof(cases )
have "disassemble l_bin = Some (x1 # l_asm)" 
proof -


  
           
           from Hx2 proof (cases "assemble_one_instruction x1")
           case None
           then show ?case auto
           next
           
           
qed
qed


*)

(*
apply (auto split: option.split) *)

(*
subgoal premises aaa for ab
apply (auto simp add: aaa(2)[symmetric])

thm aaa

apply (insert aaa)

apply (auto simp add: insn_def)

. .

subgoal premises aaa for a aa x21 x22 x23 x24
apply (auto simp add: aaa(5))

thm aaa


apply (auto split: option.split)

apply (auto simp add: insn_def)


apply (subst aaa(2)[symmetric]) *)

declare if_split_asm [split del]
end