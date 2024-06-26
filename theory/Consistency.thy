theory Consistency
imports
  Main (*
  "HOL.Bit_Operations" "HOL-Library.Word" *)
  rBPFCommType rBPFSyntax Assembler Disassembler
begin


lemma u4_breg_0 [simp]: "u4_to_bpf_ireg 0 = Some BR0"
apply (unfold u4_to_bpf_ireg_def)
apply auto
done

lemma u4_breg_i64 [simp]: "u4_to_bpf_ireg (bpf_dst x1) = Some aa \<Longrightarrow> (bpf_ireg2i64 aa) = (ucast (bpf_dst x1))"
apply (unfold u4_to_bpf_ireg_def)
apply (cases "bpf_dst x1 = 0")
apply auto
apply (cases "bpf_dst x1 = 1")
apply auto
apply (cases "bpf_dst x1 = 2")
apply auto
apply (cases "bpf_dst x1 = 3")
apply auto
apply (cases "bpf_dst x1 = 4")
apply auto
apply (cases "bpf_dst x1 = 5")
apply auto
apply (cases "bpf_dst x1 = 6")
apply auto
apply (cases "bpf_dst x1 = 7")
apply auto
apply (cases "bpf_dst x1 = 8")
apply auto
apply (cases "bpf_dst x1 = 9")
apply auto
apply (cases "bpf_dst x1 = 10")
apply auto
done

lemma  bpf_ireg_i64_same [simp]: "u4_to_bpf_ireg (ucast (bpf_ireg2i64 x1)) = Some x1"
apply (cases "x1", simp add: u4_to_bpf_ireg_def)
apply (simp add: u4_to_bpf_ireg_def)
apply (simp add: u4_to_bpf_ireg_def)
apply (simp add: u4_to_bpf_ireg_def)
apply (simp add: u4_to_bpf_ireg_def)
apply (simp add: u4_to_bpf_ireg_def)
apply (simp add: u4_to_bpf_ireg_def)
apply (simp add: u4_to_bpf_ireg_def)
apply (simp add: u4_to_bpf_ireg_def)
apply (simp add: u4_to_bpf_ireg_def)
apply (simp add: u4_to_bpf_ireg_def)
done

lemma bpf_opc_simp[simp]:  "(bpf_opc
                 \<lparr>bpf_opc = x1,
                    bpf_dst = x2,
                    bpf_src = x3,
                    bpf_off = x4, bpf_imm = x5\<rparr> = x1)" by fastforce

lemma bpf_dst_simp[simp]:  "(bpf_dst
                 \<lparr>bpf_opc = x1,
                    bpf_dst = x2,
                    bpf_src = x3,
                    bpf_off = x4, bpf_imm = x5\<rparr> = x2)" by fastforce

lemma bpf_src_simp[simp]:  "(bpf_src
                 \<lparr>bpf_opc = x1,
                    bpf_dst = x2,
                    bpf_src = x3,
                    bpf_off = x4, bpf_imm = x5\<rparr> = x3)" by fastforce

lemma bpf_off_simp[simp]:  "(bpf_off
                 \<lparr>bpf_opc = x1,
                    bpf_dst = x2,
                    bpf_src = x3,
                    bpf_off = x4, bpf_imm = x5\<rparr> = x4)" by fastforce

lemma bpf_imm_simp[simp]:  "(bpf_imm
                 \<lparr>bpf_opc = x1,
                    bpf_dst = x2,
                    bpf_src = x3,
                    bpf_off = x4, bpf_imm = x5\<rparr> = x5)" by fastforce


lemma assemble_disassemble_consistency: "assemble l_asm = Some l_bin \<Longrightarrow> disassemble l_bin = Some l_asm"
apply (induction l_asm arbitrary: l_bin)
apply simp
apply simp+ 
subgoal for x1 l_asm

apply (cases "assemble_one_instruction x1")
apply auto

apply (cases "assemble l_asm")
apply auto

subgoal for a aa
apply (cases "x1", auto simp: insn_def) (**r , auto split: option.split *)

subgoal for x11 x12 x13

apply (cases "SCAST(32 signed \<rightarrow> 64 signed) x13
             <s 0xFFFFFFFF80000000 \<or>
             0x7FFFFFFF <s SCAST(32 signed \<rightarrow> 64 signed) x13")
apply auto

apply (unfold disassemble_lddw_def)
apply auto
apply (cases "bpf_ireg2i64 x11 <s 0 \<or> 0xA <s bpf_ireg2i64 x11", auto)
apply (cases " SCAST(32 signed \<rightarrow> 64 signed) x12
        <s 0xFFFFFFFF80000000 \<or>
        0x7FFFFFFF <s SCAST(32 signed \<rightarrow> 64 signed) x12", auto)

apply (cases "bpf_ireg2i64 x11 <s 0 \<or> 0xA <s bpf_ireg2i64 x11", auto)
apply (cases " SCAST(32 signed \<rightarrow> 64 signed) x12
        <s 0xFFFFFFFF80000000 \<or>
        0x7FFFFFFF <s SCAST(32 signed \<rightarrow> 64 signed) x12", auto)
.

subgoal for x21 x22 x23 x24
apply (unfold disassemble_lddw_def)
apply (cases "bpf_ireg2i64 x22 <s 0 \<or> 0xA <s bpf_ireg2i64 x22", auto)
apply (cases "bpf_ireg2i64 x23 <s 0 \<or> 0xA <s bpf_ireg2i64 x23", auto)
apply (cases " SCAST(16 signed \<rightarrow> 64 signed) x24 <s 0xFFFFFFFFFFFF8000 \<or> 0x7FFF <s SCAST(16 signed \<rightarrow> 64 signed) x24", auto)

apply (cases x21, auto)
.

subgoal for x1 x2 x3 x4
apply (cases "bpf_ireg2i64 x2 <s 0 \<or> 0xA <s bpf_ireg2i64 x2")
apply auto

apply (cases "bpf_ireg2i64 x3 <s 0 \<or> 0xA <s bpf_ireg2i64 x3")
apply auto

apply (cases "SCAST(16 signed \<rightarrow> 64 signed) x4 <s 0xFFFFFFFFFFFF8000 \<or> 0x7FFF <s SCAST(16 signed \<rightarrow> 64 signed) x4")
apply auto

apply (cases x1)
apply auto

apply (unfold disassemble_one_instruction_def, auto)
.


subgoal for x31 x32 x33 x34

apply (cases "bpf_ireg2i64 x32 <s 0 \<or> 0xA <s bpf_ireg2i64 x32")
apply auto

apply (cases "snd_op2i64 x33 <s 0 \<or> 0xA <s snd_op2i64 x33")
apply auto

apply (cases "SCAST(16 signed \<rightarrow> 64 signed) x34 <s 0xFFFFFFFFFFFF8000 \<or> 0x7FFF <s SCAST(16 signed \<rightarrow> 64 signed) x34")
apply auto

apply (unfold disassemble_lddw_def)
apply (cases x31, auto, cases x33, auto)
apply (cases x33, auto)
apply (cases x33, auto)
apply (cases x33, auto)
.

subgoal for x31 x32 x33 x34

apply (cases "bpf_ireg2i64 x32 <s 0 \<or> 0xA <s bpf_ireg2i64 x32")
apply auto

apply (cases "snd_op2i64 x33 <s 0 \<or> 0xA <s snd_op2i64 x33")
apply auto

apply (cases "SCAST(16 signed \<rightarrow> 64 signed) x34 <s 0xFFFFFFFFFFFF8000 \<or> 0x7FFF <s SCAST(16 signed \<rightarrow> 64 signed) x34")
apply auto

apply (cases x31, auto)
subgoal
apply (cases x33, auto)

apply (unfold disassemble_one_instruction_def, auto)
.

subgoal for x1

apply (cases "0xA < bpf_ireg2i64 x1")
apply auto
.    

subgoal for x1

apply (cases "0xA < bpf_ireg2i64 x1")
apply auto
.

subgoal for x31 x32

apply (cases "0xA < bpf_ireg2i64 x31")
apply auto
.

subgoal for x31 x32 x33

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto
apply (cases "0xA < snd_op2i64 x33")
apply auto
.   

subgoal for x31

apply (cases "0xA < bpf_ireg2i64 x31")
apply auto
.  

subgoal for x31

apply (cases "0xA < bpf_ireg2i64 x31")
apply auto
.  

subgoal for x31 x32 x33

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto
apply (cases "0xA < snd_op2i64 x33")
apply auto
.  

subgoal for x31 x32 x33

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto
apply (cases "0xA < snd_op2i64 x33")
apply auto
.  

subgoal for x31 x32 x33

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto
apply (cases "0xA < snd_op2i64 x33")
apply auto
.  

subgoal for x31

apply (cases "SCAST(16 signed \<rightarrow> 64 signed) x31 < 0xFFFFFFFFFFFF8000 \<or>
        0x7FFF < SCAST(16 signed \<rightarrow> 64 signed) x31")
apply auto
.  

subgoal for x1 x2 x3 x4

apply (cases "0xA < bpf_ireg2i64 x2")
apply auto
apply (cases "0xA < snd_op2i64 x3")
apply auto

apply (cases "SCAST(16 signed \<rightarrow> 64 signed) x4 < 0xFFFFFFFFFFFF8000 \<or>
        0x7FFF < SCAST(16 signed \<rightarrow> 64 signed) x4")
apply auto
.  

subgoal for x1 x2

apply (cases "0xA < bpf_ireg2i64 x1")
apply auto
.  

subgoal for x1 x2

apply (cases "0xA < bpf_ireg2i64 x1")
apply auto
. 

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

.
done

(**TODO: consistency between assemble and disassemble *)


lemma "(if (0::u64) < 0 \<or> (10::u64) < 0 then None else Some True) = Some True" 
by fastforce

lemma "bpf_opc x1 = 0x18 \<Longrightarrow>
       l_bin = a # l_a \<Longrightarrow>
       bpf_opc a = 0 \<Longrightarrow>
       bpf_dst a = 0 \<Longrightarrow>
       bpf_src a = 0 \<Longrightarrow>
       u4_to_bpf_ireg (bpf_dst x1) = Some aa \<Longrightarrow>
       disassemble l_a = Some aaa \<Longrightarrow>
       insn 0x18 0 0 0
              0 = None"
              apply (unfold insn_def)
              apply auto
              done
(** WHY ?

value "(0::64 sword) < - 0x8000" *)
value "(0::64 sword) <s - 0x8000"

(*
value "- (0x8000:: i64)"
value "(0:: i64)"
value "(0::64 sword) <s ((- 0x8000) :: i64)" *)

lemma disassemble_lddw_assemble_one_instruction[simp]:
"bpf_opc a = 0x18 \<Longrightarrow> disassemble_lddw (bpf_dst a) (bpf_imm a) aa = Some x1 \<Longrightarrow>
assemble_one_instruction x1 = Some a"
apply (unfold disassemble_lddw_def)
apply (cases "bpf_opc aa = 0 \<and> bpf_dst aa = 0 \<and> bpf_src aa = 0")
apply auto
apply (cases "u4_to_bpf_ireg (bpf_dst a)")
apply auto
apply (unfold insn_def) 

sorry

lemma disassemble_lddw_some[simp]:
"bpf_opc a = 0x18 \<Longrightarrow>
u4_to_bpf_ireg (bpf_dst a) = Some d \<Longrightarrow>
disassemble_lddw (bpf_dst a) (bpf_imm a) aa = Some x \<Longrightarrow>
x = BPF_LD_IMM d (bpf_imm a) (bpf_imm aa)"
apply (unfold disassemble_lddw_def)
apply (cases "bpf_opc aa = 0 \<and> bpf_dst aa = 0 \<and> bpf_src aa = 0")
apply auto
done


lemma disassemble_assemble_consistency: "disassemble l_bin = Some l_asm \<Longrightarrow> assemble l_asm = Some l_bin"
apply (induction l_asm arbitrary: l_bin)

(**r l_asm = [] *)
subgoal for l_bin
apply (cases l_bin)
apply auto

subgoal for a l_a
apply (cases "bpf_opc a = 0x18")
apply auto

subgoal
apply (cases l_a)
apply auto

subgoal for aa l_aa
apply (cases "disassemble_lddw (bpf_dst a) (bpf_imm a) aa")
apply auto

apply (cases "disassemble l_aa")
apply auto
.
.

apply (cases "disassemble_one_instruction a")
apply auto

apply (cases "disassemble l_a")
apply auto
.
.

subgoal for x1 l_asm l_bin
apply (cases l_bin)
apply auto

subgoal for a l_a
apply (cases "bpf_opc a = 0x18")
apply auto

subgoal
apply (cases l_a)
apply auto

subgoal for aa l_aa
apply (cases "disassemble_lddw (bpf_dst a) (bpf_imm a) aa")
apply auto

apply (cases "disassemble l_aa")
apply auto

apply (unfold disassemble_lddw_def)
apply (cases "bpf_opc aa = 0 \<and> bpf_dst aa = 0 \<and> bpf_src aa = 0")
apply auto

apply (cases "u4_to_bpf_ireg (bpf_dst a)")
apply auto

../..
apply (unfold insn_def)
apply auto
.
.

apply simp
apply simp+

subgoal for x1 l_bin l_asm
apply (cases "bpf_opc x1 = 0x18")
apply auto

(**r bpf_opc x1 = 0x18  *)
subgoal
apply (cases l_bin)
apply auto

subgoal for a l_a
apply (unfold disassemble_lddw_def)
apply (cases "bpf_opc a = 0 \<and> bpf_dst a = 0 \<and> bpf_src a = 0")
apply auto
apply (cases "u4_to_bpf_ireg (bpf_dst x1)")
apply auto

apply (cases "disassemble l_a")
apply simp

apply simp



apply (unfold disassemble_one_instruction_def)
apply auto

../..
apply (unfold insn_def)
u4_to_bpf_ireg (bpf_dst x1) = Some aa
apply (cases "UCAST(4 \<rightarrow> 64 signed) (bpf_dst x1) < 0 \<or>
                0xA < UCAST(4 \<rightarrow> 64 signed) (bpf_dst x1)")
subgoal

apply simp
apply auto

apply simp

disassemble_one_instruction a = Some 
bpf_opc a = 0 \<Longrightarrow>
bpf_dst a = 0 \<Longrightarrow>
bpf_src a = 0 \<Longrightarrow>
../..

apply (unfold insn_def)
apply auto

subgoal
apply (unfold disassemble_lddw_def)
apply (cases l_a)
apply auto
.

apply (unfold disassemble_lddw_def)
apply (cases "disassemble_one_instruction a")
apply auto

subgoal



../..

apply simp

apply (cases "u4_to_bpf_ireg 0")
apply auto

subgoal

.

done
end