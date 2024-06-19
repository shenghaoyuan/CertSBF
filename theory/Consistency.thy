theory Consistency
imports
  Main
  "HOL.Bit_Operations" "HOL-Library.Word"
  rBPFCommType rBPFSyntax Assembler Disassembler
begin

(*apply (induction l_asm)
apply simp
apply simp
*)
term "assemble_def"

lemma assemble_disassemble_consistency: "assemble l_asm = Some l_bin \<Longrightarrow> disassemble l_bin = Some l_asm"
apply (induction l_asm arbitrary: l_bin)
apply simp
apply simp+ 

subgoal for x1 l_asm

apply (cases "assemble_one_instruction x1")
apply auto

apply (cases "assemble l_asm")
apply auto

apply (cases "x1") (**r , auto split: option.split *)
apply auto

subgoal for a aa x11 x12 x13
apply (unfold insn_def)
apply auto
.

subgoal for a aa x21 x22 x23 x24
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x22")
apply auto

apply (cases "0xA < bpf_ireg2i64 x23")
apply auto

apply (cases "SCAST(16 signed \<rightarrow> 64 signed) x24 < 0xFFFFFFFFFFFF8000 \<or> 0x7FFF < SCAST(16 signed \<rightarrow> 64 signed) x24")
apply auto
.

subgoal for a aa x21 x22 x23 x24
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x22")
apply auto

apply (cases "0xA < bpf_ireg2i64 x23")
apply auto

apply (cases "SCAST(16 signed \<rightarrow> 64 signed) x24 < 0xFFFFFFFFFFFF8000 \<or> 0x7FFF < SCAST(16 signed \<rightarrow> 64 signed) x24")
apply auto
.

subgoal for a aa x31 x32 x33 x34
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto

apply (cases "0xA < snd_op2i64 x33")
apply auto

apply (cases "SCAST(16 signed \<rightarrow> 64 signed) x34 < 0xFFFFFFFFFFFF8000 \<or> 0x7FFF < SCAST(16 signed \<rightarrow> 64 signed) x34")
apply auto
.

subgoal for a aa x31 x32 x33 x34
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto

apply (cases "0xA < snd_op2i64 x33")
apply auto

apply (cases "SCAST(16 signed \<rightarrow> 64 signed) x34 < 0xFFFFFFFFFFFF8000 \<or> 0x7FFF < SCAST(16 signed \<rightarrow> 64 signed) x34")
apply auto
.

subgoal for a aa x31 x32 x33
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto

apply (cases "0xA < snd_op2i64 x33")
apply auto
.

subgoal for a aa x31 x32 x33
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto

apply (cases "0xA < snd_op2i64 x33")
apply auto
.    

subgoal for a aa x1
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x1")
apply auto
.  

subgoal for a aa x1
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x1")
apply auto
.

subgoal for a aa x31 x32
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x31")
apply auto
.

subgoal for a aa x31 x32
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x31")
apply auto
.   

subgoal for a aa x31 x32
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x31")
apply auto
.   

subgoal for a aa x31 x32
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x31")
apply auto
.   

subgoal for a aa x31 x32 x33
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto
apply (cases "0xA < snd_op2i64 x33")
apply auto
.   

subgoal for a aa x31 x32 x33
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto
apply (cases "0xA < snd_op2i64 x33")
apply auto
.  

subgoal for a aa x31
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x31")
apply auto
.  

subgoal for a aa x31
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x31")
apply auto
.  

subgoal for a aa x31 x32
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x31")
apply auto
.  

subgoal for a aa x31 x32
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x31")
apply auto
.  

subgoal for a aa x31 x32 x33
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto
apply (cases "0xA < snd_op2i64 x33")
apply auto
.  

subgoal for a aa x31 x32 x33
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto
apply (cases "0xA < snd_op2i64 x33")
apply auto
.  

subgoal for a aa x31 x32 x33
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto
apply (cases "0xA < snd_op2i64 x33")
apply auto
.  

subgoal for a aa x31 x32 x33
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto
apply (cases "0xA < snd_op2i64 x33")
apply auto
.  

subgoal for a aa x31 x32 x33
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto
apply (cases "0xA < snd_op2i64 x33")
apply auto
.  

subgoal for a aa x31 x32 x33
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x32")
apply auto
apply (cases "0xA < snd_op2i64 x33")
apply auto
.  

subgoal for a aa x31
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "SCAST(16 signed \<rightarrow> 64 signed) x31 < 0xFFFFFFFFFFFF8000 \<or>
        0x7FFF < SCAST(16 signed \<rightarrow> 64 signed) x31")
apply auto
.  

subgoal for a aa x31
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "SCAST(16 signed \<rightarrow> 64 signed) x31 < 0xFFFFFFFFFFFF8000 \<or>
        0x7FFF < SCAST(16 signed \<rightarrow> 64 signed) x31")
apply auto
.  

subgoal for a aa x1 x2 x3 x4
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x2")
apply auto
apply (cases "0xA < snd_op2i64 x3")
apply auto

apply (cases "SCAST(16 signed \<rightarrow> 64 signed) x4 < 0xFFFFFFFFFFFF8000 \<or>
        0x7FFF < SCAST(16 signed \<rightarrow> 64 signed) x4")
apply auto
.  

subgoal for a aa x1 x2 x3 x4
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x2")
apply auto
apply (cases "0xA < snd_op2i64 x3")
apply auto

apply (cases "SCAST(16 signed \<rightarrow> 64 signed) x4 < 0xFFFFFFFFFFFF8000 \<or>
        0x7FFF < SCAST(16 signed \<rightarrow> 64 signed) x4")
apply auto
.  

subgoal for a aa x1 x2
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x1")
apply auto
.  

subgoal for a aa x1 x2
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x1")
apply auto
. 

subgoal for a aa x1 x2
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x1")
apply auto
. 

subgoal for a aa x1 x2
apply (unfold insn_def disassemble_lddw_def)
apply auto

apply (cases "0xA < bpf_ireg2i64 x1")
apply auto
. 

subgoal for a aa
apply (unfold insn_def disassemble_lddw_def)
apply auto

. 

subgoal for a aa
apply (unfold insn_def disassemble_lddw_def)
apply auto

. 
.

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

done

(**TODO: consistency between assemble and disassemble *)

end