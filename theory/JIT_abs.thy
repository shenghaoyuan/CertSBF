section \<open> A collection of common type of JIT \<close>

theory JIT_abs
imports
  Main
  rBPFCommType rBPFSyntax
  vm x86CommType Interpreter x64Semantics x64Disassembler  x64Assembler
begin

record JitProgram =
page_size     :: usize
pc_section    :: "usize list"
text_section  :: "u8 list"

record JitCompiler =
jit_result :: JitProgram 
offset_in_text_section :: usize 
jit_pc :: usize 

definition update_pc_section_aux ::"usize list \<Rightarrow> nat \<Rightarrow> usize \<Rightarrow> usize list" where
"update_pc_section_aux pc_sec pc x = list_update pc_sec pc x"

definition update_pc_section ::"JitCompiler \<Rightarrow> JitCompiler" where
"update_pc_section jcomp = (let jprog = jit_result jcomp;
   r = pc_section jprog; x = update_pc_section_aux r (unat (jit_pc jcomp)) (offset_in_text_section jcomp) in 
    jcomp \<lparr>jit_result := (jit_result jcomp)\<lparr>pc_section := x \<rparr>\<rparr>)"

definition jit_emit :: "JitCompiler \<Rightarrow> u8 list  \<Rightarrow> JitCompiler" where
"jit_emit l n = l
 \<lparr>
  jit_result              := (jit_result l)\<lparr> text_section := (text_section (jit_result l))@n \<rparr>,
  offset_in_text_section  := (offset_in_text_section l) + of_nat (length n)
 \<rparr>"

abbreviation "REG_SCRATCH::ireg \<equiv> x64Syntax.R11"  

definition bpf_to_x64_reg:: "bpf_ireg \<Rightarrow> ireg" where
  "bpf_to_x64_reg br = (
  case br of
  BR0 \<Rightarrow> x64Syntax.RAX |
  BR1 \<Rightarrow> x64Syntax.RDI |
  BR2 \<Rightarrow> x64Syntax.RSI |
  BR3 \<Rightarrow> x64Syntax.RDX |
  BR4 \<Rightarrow> x64Syntax.RCX |
  BR5 \<Rightarrow> x64Syntax.R8 |
  BR6 \<Rightarrow> x64Syntax.RBX |
  BR7 \<Rightarrow> x64Syntax.R13 |
  BR8 \<Rightarrow> x64Syntax.R14 |
  BR9 \<Rightarrow> x64Syntax.R15 |
  BR10 \<Rightarrow> x64Syntax.RBP
)"

lemma bpf_to_x64_reg_corr2[simp]:" bpf_to_x64_reg r1 \<noteq> bpf_to_x64_reg r2  \<longrightarrow> r1 \<noteq> r2 "
  apply(unfold bpf_to_x64_reg_def)
  apply(rule impI)
  apply(cases r1)
    apply(cases r2, simp_all)
           apply(cases r2, simp_all)
    apply(cases r2, simp_all)
         apply(cases r2, simp_all)
    apply(cases r2, simp_all)
       apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  done

lemma bpf_to_x64_reg_corr[simp]:" r1 \<noteq> r2 \<longrightarrow> bpf_to_x64_reg r1 \<noteq> bpf_to_x64_reg r2 "
  apply(unfold bpf_to_x64_reg_def)
  apply(rule impI)
  apply(cases r1)
    apply(cases r2, simp_all)
           apply(cases r2, simp_all)
    apply(cases r2, simp_all)
         apply(cases r2, simp_all)
    apply(cases r2, simp_all)
       apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  done

definition per_jit_add_reg64_1 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> x64_bin option" where
"per_jit_add_reg64_1 dst src = (
  let ins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    x64_encode ins
)"

definition per_jit_exit :: "x64_bin option " where
"per_jit_exit = (
  let ins = Pret in
    x64_encode ins
)"

datatype jit_state =
  JIT_OK JitCompiler regset SBPFV | (**r normal state *) (*reg_map mem stack_state Config SBPFV*)
  JIT_Success |
  JIT_EFlag | (**r find bugs at runtime *)
  JIT_Err (**r bad thing *)

fun per_jit_ins ::" u64 \<Rightarrow> bpf_instruction \<Rightarrow> regset \<Rightarrow> SBPFV \<Rightarrow> x64_bin option"where
"per_jit_ins pc bins rs sv = (
  case bins of
  BPF_ALU64 BPF_ADD dst (SOReg src) \<Rightarrow> (per_jit_add_reg64_1 dst src) |
  BPF_EXIT \<Rightarrow> per_jit_exit |
  _ \<Rightarrow> None
)"

definition update_pc ::"JitCompiler \<Rightarrow> JitCompiler " where
"update_pc jcomp = jcomp\<lparr> jit_pc := (jit_pc jcomp) + 1\<rparr>"

definition jit_compile_aux::"u64 \<Rightarrow> bpf_instruction \<Rightarrow> regset \<Rightarrow> SBPFV \<Rightarrow> JitCompiler \<Rightarrow> jit_state" where
"jit_compile_aux pc bins rs sv jcomp = (let xins = per_jit_ins pc bins rs sv in
   if bins = BPF_EXIT then JIT_Success else
   (case xins of None \<Rightarrow> JIT_Err |
                 Some v \<Rightarrow> let jcomp_updated1 = update_pc_section jcomp; jcomp_updated2 = jit_emit jcomp_updated1 v;
                           jcomp_updated = update_pc jcomp_updated2 in 
    JIT_OK jcomp_updated rs sv))"

fun jit_compile :: "nat \<Rightarrow> bpf_bin \<Rightarrow> jit_state \<Rightarrow> jit_state" where
"jit_compile 0  _ st =  JIT_EFlag " |
"jit_compile (Suc fuel) prog st = (
  case st of 
  JIT_Err \<Rightarrow> JIT_Err |
  JIT_Success \<Rightarrow> JIT_Success |
  JIT_EFlag \<Rightarrow> JIT_EFlag |
  JIT_OK jcomp rs sv \<Rightarrow> ( let pc = jit_pc jcomp in
    if unat pc < length prog then
        case bpf_find_instr (unat pc) prog of 
          None \<Rightarrow> JIT_Err |
          Some ins \<Rightarrow> jit_compile fuel prog (jit_compile_aux pc ins rs sv jcomp)      
    else JIT_Err))"

end