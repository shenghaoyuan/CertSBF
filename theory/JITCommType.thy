section \<open> A collection of common type of JIT \<close>

theory JITCommType
imports
  Main
  rBPFCommType rBPFSyntax
  vm x86CommType Interpreter x64Semantics x64Disassembler  x64Assembler
begin

text \<open> RDI: Used together with slot_in_vm() \<close>
abbreviation "REGISTER_PTR_TO_VM:: u8 \<equiv> ARGUMENT_REGISTERS ! 0"
text \<open> RBX: Program counter limit \<close>
abbreviation "REGISTER_INSTRUCTION_METER:: u8 \<equiv> CALLEE_SAVED_REGISTERS ! 1"
text \<open> R10: Other scratch register \<close>
abbreviation "REGISTER_OTHER_SCRATCH:: u8 \<equiv> CALLER_SAVED_REGISTERS ! 7"
text \<open> R11: Scratch register \<close>
abbreviation "REGISTER_SCRATCH :: u8 \<equiv> CALLER_SAVED_REGISTERS ! 8"

datatype OperandSize = S0 | S8 | S16 | S32 | S64

datatype RuntimeEnvironmentSlot =
  HostStackPointer |
  CallDepth |
  StackPointer |
  ContextObjectPointer |
  PreviousInstructionMeter |
  DueInsnCount |
  StopwatchNumerator |
  StopwatchDenominator |
  Registers |
  ProgramResult |
  MemoryMapping

definition i32_of_RuntimeEnvironmentSlot :: "RuntimeEnvironmentSlot \<Rightarrow> i32" where
"i32_of_RuntimeEnvironmentSlot slot = (
  case slot of
  HostStackPointer          \<Rightarrow> 0 |
  CallDepth                 \<Rightarrow> 1 |
  StackPointer              \<Rightarrow> 2 |
  ContextObjectPointer      \<Rightarrow> 3 |
  PreviousInstructionMeter  \<Rightarrow> 4 |
  DueInsnCount              \<Rightarrow> 5 |
  StopwatchNumerator        \<Rightarrow> 6 |
  StopwatchDenominator      \<Rightarrow> 7 |
  Registers                 \<Rightarrow> 8 |
  ProgramResult             \<Rightarrow> 20 |
  MemoryMapping             \<Rightarrow> 28
)"

record JitProgram =
page_size     :: usize
pc_section    :: "usize list"
text_section  :: "u8 list"

record JitCompiler =
jit_result :: JitProgram (*
text_section_jumps: Vec<Jump>,
    anchors: [*const u8; ANCHOR_COUNT], *)
offset_in_text_section :: nat \<comment> \<open> usize is refined to nat \<close>
(*
    executable: &'a Executable<C>,
    program: &'a [u8],
    program_vm_BPF_ADDr: u64, *)
jit_pc :: usize (*
    last_instruction_meter_validation_pc: usize,
    next_noop_insertion: u32, *)
runtime_environment_key :: i32 (*
    diversification_rng: SmallRng,
    stopwatch_is_active: bool, *)

definition jit_emit :: "JitCompiler \<Rightarrow> u8 list  \<Rightarrow> JitCompiler" where
"jit_emit l n = l
 \<lparr>
  jit_result              := (jit_result l)\<lparr> text_section := (text_section (jit_result l))@n \<rparr>,
  offset_in_text_section  := (offset_in_text_section l) + length n
 \<rparr>"

definition slot_in_vm :: "JitCompiler \<Rightarrow> RuntimeEnvironmentSlot \<Rightarrow> i32" where
"slot_in_vm l slot =
  8 * ((i32_of_RuntimeEnvironmentSlot slot) - (runtime_environment_key l))"

definition jit_emit_variable_length ::
  "JitCompiler \<Rightarrow> OperandSize \<Rightarrow> u64  \<Rightarrow> JitCompiler" where
"jit_emit_variable_length l sz data = (
  case sz of
  S0 \<Rightarrow> l |
  S8 \<Rightarrow> jit_emit l [(ucast (and data 0xff))] |
  S16 \<Rightarrow> jit_emit l (u8_list_of_u16 (ucast data)) |
  S32 \<Rightarrow> jit_emit l (u8_list_of_u32 (ucast data)) |
  S64 \<Rightarrow> jit_emit l (u8_list_of_u64 (ucast data))
)"

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

definition per_jit_sub_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> x64_bin option" where
"per_jit_sub_reg64 dst src = (
  let ins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    x64_encode ins
)"

definition per_jit_or_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> x64_bin option" where
"per_jit_or_reg64 dst src = (
  let ins = Porq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    x64_encode ins
)"

definition per_jit_xor_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> x64_bin option" where
"per_jit_xor_reg64 dst src = (
  let ins = Pxorq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    x64_encode ins
)"

definition per_jit_neg_reg64 :: "bpf_ireg \<Rightarrow> SBPFV \<Rightarrow> x64_bin option" where
"per_jit_neg_reg64 dst sv = (
  case sv of V1 \<Rightarrow> None | V2 \<Rightarrow>  
    let ins = Pnegq (bpf_to_x64_reg dst) in
    x64_encode ins
)"

definition per_jit_and_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg  \<Rightarrow> x64_bin option" where
"per_jit_and_reg64 dst src = (
    let ins = Pandq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg dst) in
    x64_encode ins
)"

definition per_jit_mov_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> x64_bin option" where
"per_jit_mov_reg64 dst src  = (
    let ins = Pmovq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg dst) in
    x64_encode ins
)"

(*no addq_ri?*)
definition per_jit_add_reg64_1 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> x64_bin option" where
"per_jit_add_reg64_1 dst src = (
  let ins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    x64_encode ins
)"

definition per_jit_mul_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> x64_bin option" where
"per_jit_mul_reg64 dst src = (
  let cond1 = ((bpf_to_x64_reg dst) \<noteq> x64Syntax.RAX); cond2 = ((bpf_to_x64_reg dst) \<noteq> x64Syntax.RDX);
      ins_prefix = if cond1 then [Ppushl_r x64Syntax.RAX, Pmovq_rr (bpf_to_x64_reg dst) (x64Syntax.RAX)] else [];
      ins = [Pmulq_r (bpf_to_x64_reg src)];
      ins_suffix = if cond1 then [Pmovq_rr (x64Syntax.RAX) (bpf_to_x64_reg dst),Ppopl x64Syntax.RAX] 
                   else [Ppopl x64Syntax.RAX] in 
    x64_encodes (ins_prefix@ins@ins_suffix)
)"

 (** 32 bit shift may use REG_SCRACH **)
definition per_jit_shift_reg64 :: "nat \<Rightarrow> bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> x64_bin option" where
"per_jit_shift_reg64 n dst src = (
  let opcode = (if n = 4 then Pshlq_r else if n = 5 then Pshrq_r else Psarl_r) in
  let cond1 = ((bpf_to_x64_reg dst) = x64Syntax.RCX);
      ins_prefix = if cond1 then [Ppushl_r (bpf_to_x64_reg src), Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)]
                   else [Ppushl_r x64Syntax.RCX, Pmovq_rr (bpf_to_x64_reg src) (x64Syntax.RCX)] ;
      ins = if cond1 then  [opcode (bpf_to_x64_reg src)] else [opcode (bpf_to_x64_reg dst)];
      ins_suffix = if cond1 then [Pmovq_rr (bpf_to_x64_reg src) (x64Syntax.RCX), Ppopl (bpf_to_x64_reg src)] else [Ppopl x64Syntax.RCX] in 
    x64_encodes (ins_prefix@ins@ins_suffix)
)"


(*TODO: transfer offset*)
definition get_relative_offset ::"u32 \<Rightarrow> u32" where
"get_relative_offset off = off"

definition per_jit_ja :: "off_ty \<Rightarrow> x64_bin option" where
"per_jit_ja off = (
  let ins = Pjmp (get_relative_offset (ucast off)) in
    x64_encode ins
)"

definition per_jit_conditional_jump_reg64 :: "u64 \<Rightarrow> condition \<Rightarrow> reg_map \<Rightarrow> bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> off_ty \<Rightarrow> x64_bin option" where
"per_jit_conditional_jump_reg64 pc cond rs dst src off = (
  let tcond = (case cond of Eq \<Rightarrow> Some Cond_e | Ne \<Rightarrow> Some Cond_ne
  | Lt \<Rightarrow> Some Cond_b | Le \<Rightarrow> Some Cond_be | Ge \<Rightarrow> Some Cond_ae | Gt \<Rightarrow> Some Cond_a
  | SLt \<Rightarrow> Some Cond_l | SLe \<Rightarrow> Some Cond_le | SGe \<Rightarrow> Some Cond_ge | SGt \<Rightarrow> Some Cond_g
  | _ \<Rightarrow> None ) in
  let t_pc = ucast pc + ucast off; t_pc' = get_relative_offset t_pc; 
      ins_prefix = if tcond \<noteq> None then [Pcmpq_rr (bpf_to_x64_reg src) (bpf_to_x64_reg dst)]
                   else [Ptestq_rr (bpf_to_x64_reg src) (bpf_to_x64_reg dst)] ;
      ins = if tcond \<noteq> None then  [Pjcc (Option.the tcond) t_pc' ] else [Pjcc Cond_e t_pc']
      in x64_encodes (ins_prefix@ins)
)"

definition per_jit_load_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> memory_chunk \<Rightarrow> off_ty \<Rightarrow>x64_bin option" where
"per_jit_load_reg64 dst src chk off = (
  let ins = Pmov_mr (Addrmode (Some (bpf_to_x64_reg src)) None (ucast (off))) (bpf_to_x64_reg dst) chk in
    x64_encode ins
)"

datatype jit_state =
  JIT_OK JitProgram reg_map SBPFV | (**r normal state *) (*reg_map mem stack_state Config SBPFV*)
  JIT_Success |
  JIT_EFlag | (**r find bugs at runtime *)
  JIT_Err (**r bad thing *)

fun per_jit_ins ::" u64 \<Rightarrow> bpf_instruction \<Rightarrow> reg_map \<Rightarrow> SBPFV \<Rightarrow> x64_bin option"where
"per_jit_ins pc bins rs sv = (
  case bins of
  BPF_ALU64 BPF_ADD dst (SOReg src) \<Rightarrow> (per_jit_add_reg64_1 dst src) |
  BPF_ALU64 BPF_SUB dst (SOReg src) \<Rightarrow> (per_jit_sub_reg64 dst src) |
  BPF_ALU64 BPF_AND dst (SOReg src) \<Rightarrow> (per_jit_and_reg64 dst src) |
  BPF_ALU64 BPF_MOV dst (SOReg src) \<Rightarrow> (per_jit_mov_reg64 dst src) |
  BPF_NEG64_REG dst \<Rightarrow> (per_jit_neg_reg64 dst sv) |
  BPF_ALU64 BPF_MUL dst (SOReg src) \<Rightarrow> (per_jit_mul_reg64 dst src) |
  BPF_ALU64 BPF_LSH dst (SOReg src) \<Rightarrow> (per_jit_shift_reg64 4 dst src) |
  BPF_ALU64 BPF_RSH dst (SOReg src) \<Rightarrow> (per_jit_shift_reg64 5 dst src) |
  BPF_ALU64 BPF_ARSH dst (SOReg src) \<Rightarrow> (per_jit_shift_reg64 7 dst src) |
  BPF_LDX chk dst src off  \<Rightarrow> (per_jit_load_reg64 dst src chk off )|
  BPF_JA off \<Rightarrow> per_jit_ja off |
  BPF_JUMP cond dst (SOReg src) ofs \<Rightarrow> per_jit_conditional_jump_reg64 pc cond rs dst src ofs |
  _ \<Rightarrow> None
)"

definition jit_compile_aux::"u64 \<Rightarrow> bpf_instruction \<Rightarrow> reg_map \<Rightarrow> SBPFV \<Rightarrow> JitProgram  \<Rightarrow> jit_state" where
"jit_compile_aux pc bins rs sv jprog = (let xins = per_jit_ins pc bins rs sv in 
   (case xins of None \<Rightarrow> JIT_Err |
                 Some v \<Rightarrow> let ts' = (text_section jprog @ v) in JIT_OK (jprog \<lparr>text_section:=ts'\<rparr>) rs sv))"

fun jit_compile :: "nat \<Rightarrow> u64 \<Rightarrow> bpf_bin \<Rightarrow> reg_map \<Rightarrow> jit_state \<Rightarrow> jit_state " where
"jit_compile 0 _ _ _ st =  JIT_EFlag " |
"jit_compile (Suc fuel) pc prog rs st = (
  case st of 
  JIT_Err \<Rightarrow> JIT_Err |
  JIT_Success \<Rightarrow> JIT_Success |
  JIT_EFlag \<Rightarrow> JIT_EFlag |
  JIT_OK jprog rs sv \<Rightarrow> (
    if unat pc < length prog then
        case bpf_find_instr (unat pc) prog of 
          None \<Rightarrow> JIT_Err |
          Some ins \<Rightarrow> jit_compile fuel (pc+1) prog rs (jit_compile_aux pc ins rs sv jprog)      
    else JIT_Err))"


(**jit compiler with CU algorithm**)
(*
type_synonym target_pc ="usize"
type_synonym pc = "usize"
type_synonym insn_meter = "usize"
type_synonym last_pc = "usize"

definition emit_validate_instruction_count::"pc \<Rightarrow> insn_meter \<Rightarrow> last_pc option" where
"emit_validate_instruction_count pc im = (if pc+1 > im then Some pc else None)"

definition emit_profile_instruction_count::"target_pc \<Rightarrow> pc \<Rightarrow> insn_meter \<Rightarrow> insn_meter" where
"emit_profile_instruction_count t_pc pc im = im + (t_pc -(pc+1))"

definition emit_validate_and_profile_instruction_count::"target_pc \<Rightarrow> pc \<Rightarrow> insn_meter \<Rightarrow> (last_pc \<times> insn_meter) option"where
"emit_validate_and_profile_instruction_count t_pc pc im = (
  case emit_validate_instruction_count pc im of
  None \<Rightarrow> None |
  Some l_pc \<Rightarrow>
    let meter = emit_profile_instruction_count t_pc pc im in 
    Some (l_pc, meter))"


fun jit_compile :: "nat \<Rightarrow> nat \<Rightarrow> insn_meter \<Rightarrow> last_pc \<Rightarrow> bpf_bin \<Rightarrow> reg_map \<Rightarrow> jit_state \<Rightarrow> jit_state " where
"jit_compile 0 _ _ _ _ _ st =  st " |
"jit_compile (Suc fuel) cur_pc n l_pc prog rs st = (
  case st of 
  JIT_Err \<Rightarrow> JIT_Err |
  JIT_Success \<Rightarrow> JIT_Success |
  JIT_EFlag \<Rightarrow> JIT_EFlag |
  JIT_OK jprog rs sv \<Rightarrow> (
    let w_cur_pc = word_of_nat cur_pc in
      if (instruction_meter_checkpoint_distance + l_pc \<le> w_cur_pc) \<and> w_cur_pc + 1 > n then
        JIT_EFlag
      else
        let l_pc' = if instruction_meter_checkpoint_distance + l_pc \<le> w_cur_pc then w_cur_pc else l_pc in (
          case bpf_find_instr cur_pc prog of 
          None \<Rightarrow> JIT_Err |
          Some ins \<Rightarrow> (
            let n' = (
              case ins of
              BPF_JA ofs \<Rightarrow>
                let t_pc :: u64 = w_cur_pc + scast ofs + 1 in
                  emit_validate_and_profile_instruction_count t_pc w_cur_pc n |
              BPF_JUMP cond bpf_ireg snd_op ofs \<Rightarrow>
                let t_pc = w_cur_pc + scast ofs + 1 in 
                  emit_validate_and_profile_instruction_count t_pc w_cur_pc n |
              BPF_LD_IMM dst imm1 imm2 \<Rightarrow>
                emit_validate_and_profile_instruction_count (w_cur_pc+2) w_cur_pc n |
              BPF_CALL_IMM src imm \<Rightarrow> (
                case get_function_registry (ucast imm) of
                None \<Rightarrow> None |
                Some t_pc \<Rightarrow> emit_validate_and_profile_instruction_count t_pc w_cur_pc n) |
              BPF_CALL_REG src imm \<Rightarrow>
                let v = case sv of
                V1 \<Rightarrow> Option.the (u4_to_bpf_ireg (scast imm)) |
                V2 \<Rightarrow> src in 
                emit_validate_and_profile_instruction_count (rs v) w_cur_pc n |
              BPF_EXIT \<Rightarrow> emit_validate_and_profile_instruction_count 0 w_cur_pc n |
              _ \<Rightarrow> Some(l_pc,n)) in (
              if n' = None then
                JIT_EFlag
              else
                let meter' = (snd (Option.the n')) in
                let l_pc' = fst (Option.the n') in
                  jit_compile fuel cur_pc meter' l_pc' prog rs (jit_compile_aux ins rs sv jprog )
              )
          )
        )
  ))"
*)

(*
lemma 
  assumes a0:"jstate = jit_compile (length bprog) remain_cu 0 prog rs (JIT_OK jprog rs)" and
          a1:"bstate = bpf_interp (length bprog+1) bprog (BPF_OK rs m ss sv 0 remain_cu) " and
          a2:"jstate = JIT_CU"
  shows "bstate = BPF_CU"
  sorry

lemma 
  assumes a0:"jstate = jit_compile (length bprog) remain_cu 0 prog rs (JIT_OK jprog rs)" and
          a1:"bstate = bpf_interp (length bprog+1) bprog (BPF_OK rs m ss sv 0 remain_cu) " and
          a2:"bstate = BPF_OK rs m ss sv cur_cu remain_cu "
  shows "jstate = JIT_OK jprog rs"
  sorry *)


end