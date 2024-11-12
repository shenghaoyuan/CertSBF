section \<open> A collection of common type of JIT \<close>

theory JIT_abs
imports
  Main
  rBPFCommType rBPFSyntax
  vm x86CommType Interpreter x64Semantics x64Disassembler  x64Assembler
  StepSem
begin

record JitProgram =
page_size     :: usize
pc_section    :: "usize list"
text_section  :: "x64_bin"

record jit_state =
jit_result :: JitProgram 
offset_in_text_section :: usize 
jit_pc :: usize 

definition update_pc_section_aux ::"usize list \<Rightarrow> nat \<Rightarrow> usize \<Rightarrow> usize list" where
"update_pc_section_aux pc_sec pc x = list_update pc_sec pc x"

(*
definition update_pc_section ::"JitCompiler \<Rightarrow> JitCompiler" where
"update_pc_section jcomp = (let jprog = jit_result jcomp;
   r = pc_section jprog; x = update_pc_section_aux r (unat (jit_pc jcomp)) (offset_in_text_section jcomp) in 
    jcomp \<lparr>jit_result := (jit_result jcomp)\<lparr>pc_section := x \<rparr>\<rparr>)"

definition jit_emit :: "JitCompiler \<Rightarrow> u8 list  \<Rightarrow> JitCompiler" where
"jit_emit l n = l
 \<lparr>
  jit_result              := (jit_result l)\<lparr> text_section := (text_section (jit_result l))@n \<rparr>,
  offset_in_text_section  := (offset_in_text_section l) + of_nat (length n)
 \<rparr>" *)

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

(*
datatype jit_state =
  JIT_OK JitCompiler| (**r normal state *) (*regset SBPFV  mem Config*)
  JIT_Success JitProgram|
  JIT_EFlag | (**r find bugs at runtime *)
  JIT_Err (**r bad thing *) *)

fun per_jit_ins ::" bpf_instruction \<Rightarrow> x64_bin option"where
"per_jit_ins bins = (
  case bins of
  BPF_ALU64 BPF_ADD dst (SOReg src) \<Rightarrow> (per_jit_add_reg64_1 dst src) |
  BPF_EXIT \<Rightarrow> per_jit_exit |
  _ \<Rightarrow> None
)"

(*
fun per_jit_insns_aux ::"bpf_instruction list \<Rightarrow> x64_bin option list"where
"per_jit_insns_aux []  = []" |
"per_jit_insns_aux (x#xs) = (let val = per_jit_ins x in case val of None \<Rightarrow> [None] | _ \<Rightarrow> [val] @ per_jit_insns_aux xs )"

definition per_jit_insns::"bpf_instruction list \<Rightarrow> x64_bin option" where
"per_jit_insns l = (let l' = per_jit_insns_aux l in 
                              if last l' = None then None else Some (concat(map Option.the (butlast l'))))"

definition update_pc ::"JitCompiler \<Rightarrow> JitCompiler " where
"update_pc jcomp = jcomp\<lparr> jit_pc := (jit_pc jcomp) + 1\<rparr>"

definition jit_compile_aux::"u64 \<Rightarrow> bpf_instruction \<Rightarrow> JitCompiler \<Rightarrow> jit_state" where
"jit_compile_aux pc bins jcomp = (let xins = per_jit_ins bins ; jprog = jit_result jcomp  in
   if bins = BPF_EXIT then JIT_Success jprog else
   (case xins of None \<Rightarrow> JIT_Err |
                 Some v \<Rightarrow> let jcomp_updated1 = update_pc_section jcomp; jcomp_updated2 = jit_emit jcomp_updated1 v;
                           jcomp_updated = update_pc jcomp_updated2 in 
    JIT_OK jcomp_updated))"

fun jit_compile :: "nat \<Rightarrow> bpf_bin \<Rightarrow> jit_state \<Rightarrow> jit_state" where
"jit_compile 0 _ st =  JIT_EFlag " |
"jit_compile (Suc fuel) prog st = (
  case st of 
  JIT_Err \<Rightarrow> JIT_Err |
  JIT_Success jprog \<Rightarrow> JIT_Success jprog |
  JIT_EFlag \<Rightarrow> JIT_EFlag |
  JIT_OK jcomp \<Rightarrow> ( let pc = jit_pc jcomp in
    if unat pc < length prog then
        case bpf_find_instr (unat pc) prog of 
          None \<Rightarrow> JIT_Err |
          Some ins \<Rightarrow> jit_compile fuel prog (jit_compile_aux pc ins jcomp)      
    else JIT_Err))"
*)

(**r 
TODO: 
1. from sbpf binary (interpreter.rs) to sbpf binary simplified: (0x18 lddw) to (0x18 lddw_low) + (0x10 lddw_high)
2. from sbpf binary (simplified) to sbpf assembly
*)

fun jit1 :: "ebpf_asm \<Rightarrow> u8 list \<Rightarrow> usize list \<Rightarrow> (u8 list * usize list) option" where
"jit1 [] l_bin l_pc = Some (l_bin, l_pc)" |
"jit1 (h#t) l_bin l_pc = (
  case per_jit_ins h of
  None \<Rightarrow> None |
  Some ins \<Rightarrow> (
    jit1 t (l_bin @ ins) (l_pc @ [of_nat (length l_bin)])
  )
)"

fun jit2 :: "ebpf_asm \<Rightarrow> (u8 list * usize list) option" where
"jit2 [] = Some ([], [])" |
"jit2 (h#t) = (
  case jit2 t of
  None \<Rightarrow> None |
  Some (l_bin, l_pc) \<Rightarrow> (
    case per_jit_ins h of
    None \<Rightarrow> None |
    Some ins \<Rightarrow> Some (ins @l_bin, 0#(map (\<lambda> i. i + (of_nat (length ins))) l_pc))
  )
)"

(*
fun jit :: "ebpf_asm \<Rightarrow> jit_state \<Rightarrow> jit_state option" where
"jit [] st = Some st" |
"jit (h#t) st = (
  case per_jit_ins h of
  None \<Rightarrow> None |
  Some ins \<Rightarrow> jit t (upd_x64_ins ins st)
)" *)

(**r star of ebpf *)
datatype sbpf_state =
  SBPF_OK u64 reg_map mem stack_state SBPFV func_map u64 u64 | (**r normal state *)
  SBPF_Success u64

inductive sbpf_step :: "ebpf_asm * sbpf_state \<Rightarrow> ebpf_asm * sbpf_state \<Rightarrow> bool" (infix "\<rightarrow>s" 55)
  where
B_ADD64: "st = SBPF_OK pc rs m stk sv fm cur_cu remain_cu \<Longrightarrow>
          BPF_ALU64 bop d sop = l!(unat pc) \<Longrightarrow>
          bop = BPF_ADD \<Longrightarrow>
          is_v1 = (case sv of V1 \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow>
          OKS rs' = eval_alu32 bop d sop rs is_v1 \<Longrightarrow>
          st' = SBPF_OK (pc+1) rs' m stk sv fm (cur_cu+1) remain_cu \<Longrightarrow>
            (l, st) \<rightarrow>s (l, st')" |
B_EXIT: " st = SBPF_OK pc rs m stk sv fm cur_cu remain_cu \<Longrightarrow>
          BPF_EXIT = l!(unat pc) \<Longrightarrow>
          call_depth stk = 0 \<Longrightarrow>
            (l, st) \<rightarrow>s (l, SBPF_Success (rs BR0))"

abbreviation sbpf_sem::"ebpf_asm * sbpf_state \<Rightarrow> ebpf_asm * sbpf_state \<Rightarrow> bool" (infix "\<rightarrow>*s" 55)
  where "x \<rightarrow>*s y == star sbpf_step x y"


(**r star of x64 *)
datatype x64_state =
  Bin_OK u64 regset mem

axiomatization x64_step :: "u8 list * x64_state \<Rightarrow> u8 list * x64_state \<Rightarrow> bool" (infix "\<rightarrow>x" 55)

abbreviation x64_sem::"u8 list * x64_state \<Rightarrow> u8 list * x64_state \<Rightarrow> bool" (infix "\<rightarrow>*x" 55)
  where "x \<rightarrow>*x y == star x64_step x y"

(**r simulation relation *)
definition match_state :: "sbpf_state \<Rightarrow> x64_state \<Rightarrow> usize list \<Rightarrow> bool" where
"match_state bst xst pc_map = (
  case bst of
  SBPF_OK pc rs m stk sv fm cur_cu remain_cu \<Rightarrow> (
    case xst of
    Bin_OK xpc xrs xm \<Rightarrow>
    (\<forall> r. Vlong (rs r) = xrs (IR (bpf_to_x64_reg r))) \<and> \<comment>\<open> for ALU + MEM + Call \<close>
    pc_map!(unat pc) = xpc \<and>  \<comment>\<open> for Jump \<close>
    m = xm  \<comment>\<open> for MEM + Call \<close>
  ) |
  SBPF_Success v \<Rightarrow>(
    case xst of
    Bin_OK xpc xrs xm \<Rightarrow> Vlong v = xrs (IR (bpf_to_x64_reg BR0)) \<comment>\<open> for EXIT \<close>
  )
)"

theorem jit_correct:
  " jit2 prog = Some (x64_prog, pc_map) \<Longrightarrow>
    match_state bst xst pc_map \<Longrightarrow>
    sbpf_sem (prog, bst) (prog, bst') \<Longrightarrow>
    (\<exists> xst'.
      x64_sem (x64_prog, xst) (x64_prog, xst') \<and>
      match_state bst' xst' pc_map)
"
  sorry


fun interp3 :: "instruction list \<Rightarrow> outcome \<Rightarrow> outcome" where
"interp3 [] s = s" |
"interp3 (ins#l) st = (
  case st of
  Stuck \<Rightarrow> Stuck |
  Next rs m \<Rightarrow> (
        interp3 l (exec_instr ins 1 rs m)
))"

datatype bin_state =
  Bin_OK u64 regset mem | (**r normal state *) (*reg_map mem stack_state Config SBPFV*)
  Bin_Success|
  Bin_EFlag | (**r find bugs at runtime *)
  Bin_Err (**r bad thing *)

definition getInsts::"JitProgram \<Rightarrow> instruction list option" where
"getInsts jprog = (let insns = text_section jprog in 
    case x64_decodes 0 insns of None \<Rightarrow> None |
                                Some v \<Rightarrow> Some (map snd v)) "

fun binary_execute :: "nat \<Rightarrow> JitProgram \<Rightarrow> bin_state \<Rightarrow> bin_state" where
"binary_execute 0 _ st =  Bin_EFlag " |
"binary_execute (Suc fuel) jprog st = (
  case st of 
  Bin_Err \<Rightarrow> Bin_Err |
  Bin_Success \<Rightarrow> Bin_Success |
  Bin_EFlag \<Rightarrow> Bin_EFlag |
  Bin_OK pc rs m \<Rightarrow> (let v = getInsts jprog in 
    case v of None \<Rightarrow> Bin_Err |
              Some insns \<Rightarrow> 
    if unat pc < length insns then
      let result = interp3 insns (Next rs m) in 
        case result of Stuck \<Rightarrow> Bin_EFlag | Next rs' m' \<Rightarrow> Bin_OK (pc+ of_nat(length insns)) rs' m'
    else Bin_Err))"


definition init_jitprog::"JitProgram" where
"init_jitprog \<equiv> \<lparr> page_size = 4096, pc_section = [], text_section = []\<rparr>"

(*
definition init_jitcomp::"JitCompiler" where
"init_jitcomp = \<lparr> jit_result = init_jitprog, offset_in_text_section = 0, jit_pc = 0\<rparr>" *)
 
end