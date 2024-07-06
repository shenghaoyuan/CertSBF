section \<open> x86_64 Just-In-Time Compiler of Solana rBPF \<close>

theory JIT
imports
  Main
  rBPFCommType rBPFSyntax
  JITCommType x86 vm
begin

text \<open> TBC \<close>


subsection  \<open> JIT State \<close>
text \<open> the state is a record including
- a list of rBPF instructions (maybe as global varaible of `step`)
- registers
- memory_model
- VM configuration
- ... \<close>

definition emit_ins :: "JitCompiler \<Rightarrow> X86Instruction \<Rightarrow> JitCompiler option" where
"emit_ins l ins = emit ins l
  \<comment> \<open> TBC: currently, we ignore the `next_noop_insertion` things
        if self.next_noop_insertion == 0 {
            self.next_noop_insertion = self.diversification_rng.gen_range(0..self.config.noop_instruction_rate * 2);
            // X86Instruction::noop().emit(self)?;
            self.emit::<u8>(0x90);
        } else {
            self.next_noop_insertion -= 1;
        }
    } \<close>
"

definition should_sanitize_constant :: "JitCompiler \<Rightarrow> i64 \<Rightarrow> bool" where
"should_sanitize_constant l v = (
  if \<not> (sanitize_user_provided_values (jit_config l)) then
    False
  else if v = 0xFFFF \<or>
          v = 0xFFFFFF \<or>
          v = 0xFFFFFFFF \<or>
          v = 0xFFFFFFFFFF \<or>
          v = 0xFFFFFFFFFFFF \<or>
          v = 0xFFFFFFFFFFFFFF \<or>
          v = 0xFFFFFFFFFFFFFFFF then
    False
  else
    False   \<comment> \<open> TBC: something wrongs

match value as u64 {
            0xFFFF
            | 0xFFFFFF
            | 0xFFFFFFFF
            | 0xFFFFFFFFFF
            | 0xFFFFFFFFFFFF
            | 0xFFFFFFFFFFFFFF
            | 0xFFFFFFFFFFFFFFFF => false,
            v if v <= 0xFF => false,
            v if !v <= 0xFF => false,
            _ => true
        }
 \<close>
)"

definition emit_sanitized_alu :: "JitCompiler \<Rightarrow> OperandSize \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> u8
  \<Rightarrow> i64 \<Rightarrow> JitCompiler option" where
"emit_sanitized_alu l sz op ope dst imm = (
  \<comment> \<open> ignore the following, as we don't know how to model random number
if self.should_sanitize_constant(immediate) {
            self.emit_sanitized_load_immediate(size, REGISTER_OTHER_SCRATCH, immediate);
            self.emit_ins(X86Instruction::alu(size, opcode, REGISTER_OTHER_SCRATCH, destination, 0, None));
        } else
 \<close>
  if (scast i32_MIN) \<le>s imm \<and> imm \<le>s (scast i32_MAX) then
    case x86.alu sz 0x81 ope dst imm None of
    None \<Rightarrow> None |
    Some ins \<Rightarrow> emit_ins l ins
  else (
    case x86.load_immediate sz REGISTER_OTHER_SCRATCH imm of
    None \<Rightarrow> None |
    Some ins \<Rightarrow> (
      case emit_ins l ins of
      None \<Rightarrow> None |
      Some l \<Rightarrow> (
        case x86.alu sz op REGISTER_OTHER_SCRATCH dst 0 None of
        None \<Rightarrow> None |
        Some ins \<Rightarrow> emit_ins l ins)))
)"

  \<comment> \<open> ../.. \<close>



subsection  \<open> ALU \<close>
subsection  \<open> JUMP \<close>
subsection  \<open> MEM \<close>
subsection  \<open> CALL \<close>
subsection  \<open> EXIT \<close>
subsection  \<open> JIT_One \<close>



end