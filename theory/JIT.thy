section \<open> x86_64 Just-In-Time Compiler of Solana rBPF \<close>

theory JIT
imports
  Main
  rBPFCommType rBPFSyntax
  JITCommType x86 vm
begin

text \<open> TBC

 \<close>


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

(**

fn emit_sanitized_load_immediate(&mut self, size: OperandSize, destination: u8, value: i64) {
        match size {
            OperandSize::S32 => {
                let key = self.diversification_rng.gen::<i32>() as i64;
                self.emit_ins(X86Instruction::load_immediate(size, destination, (value as i32).wrapping_sub(key as i32) as i64));
                self.emit_ins(X86Instruction::alu(size, 0x81, 0, destination, key, None));
            },
            OperandSize::S64 if value >= i32::MIN as i64 && value <= i32::MAX as i64 => {
                let key = self.diversification_rng.gen::<i32>() as i64;
                self.emit_ins(X86Instruction::load_immediate(size, destination, value.wrapping_sub(key)));
                self.emit_ins(X86Instruction::alu(size, 0x81, 0, destination, key, None));
            },
            OperandSize::S64 if value as u64 & u32::MAX as u64 == 0 => {
                let key = self.diversification_rng.gen::<i32>() as i64;
                self.emit_ins(X86Instruction::load_immediate(size, destination, value.rotate_right(32).wrapping_sub(key)));
                self.emit_ins(X86Instruction::alu(size, 0x81, 0, destination, key, None)); // wrapping_add(key)
                self.emit_ins(X86Instruction::alu(size, 0xc1, 4, destination, 32, None)); // shift_left(32)
            },
            OperandSize::S64 => {
                let key = self.diversification_rng.gen::<i64>();
                if destination != REGISTER_SCRATCH {
                    self.emit_ins(X86Instruction::load_immediate(size, destination, value.wrapping_sub(key)));
                    self.emit_ins(X86Instruction::load_immediate(size, REGISTER_SCRATCH, key));
                    self.emit_ins(X86Instruction::alu(size, 0x01, REGISTER_SCRATCH, destination, 0, None));
                } else {
                    let lower_key = key as i32 as i64;
                    let upper_key = (key >> 32) as i32 as i64;
                    self.emit_ins(X86Instruction::load_immediate(size, destination, value.wrapping_sub(lower_key).rotate_right(32).wrapping_sub(upper_key)));
                    self.emit_ins(X86Instruction::alu(size, 0x81, 0, destination, upper_key, None)); // wrapping_add(upper_key)
                    self.emit_ins(X86Instruction::alu(size, 0xc1, 1, destination, 32, None)); // rotate_right(32)
                    self.emit_ins(X86Instruction::alu(size, 0x81, 0, destination, lower_key, None)); // wrapping_add(lower_key)
                }
            },
            _ => {
                #[cfg(debug_assertions)]
                unreachable!();
            }
        }
    }

*)

(*
definition emit_product_quotient_remainder ::
  "JitCompiler \<Rightarrow> OperandSize \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
    u8 \<Rightarrow> u8 \<Rightarrow> i64 option \<Rightarrow> JitCompiler option" where
"emit_product_quotient_remainder l sz alt_dst dv sg src dst imm = (
  if dv then
    case imm of
    None \<Rightarrow> (
      case x86.load_immediate S64 REGISTER_OTHER_SCRATCH (scast (jit_pc l)) of
      None \<Rightarrow> None | Some ins \<Rightarrow>
        case emit_ins l ins of
        None \<Rightarrow> None | Some l \<Rightarrow>
          case x86.test szsrc src None of
          None \<Rightarrow> None | Some ins \<Rightarrow>
            case emit_ins l ins of
            None \<Rightarrow> None | Some l \<Rightarrow>
              case x86.conditional_jump_immediate 0x84 
      ) |
    Some i \<Rightarrow> None
  else
    None
)" *)
  \<comment> \<open> 

       conditional_jump_immediate(0x84, self.relative_to_anchor(ANCHOR_DIV_BY_ZERO, 6)));
            }

            // Signed division overflows with MIN / -1.
            // If we have an immediate and it's not -1, we can skip the following check.
            if signed && imm.unwrap_or(-1) == -1 {
                self.emit_ins(X86Instruction::load_immediate(size, REGISTER_SCRATCH, if let OperandSize::S64 = size { i64::MIN } else { i32::MIN as i64 }));
                self.emit_ins(X86Instruction::cmp(size, dst, REGISTER_SCRATCH, None)); // dst == MIN

                if imm.is_none() {
                    // The exception case is: dst == MIN && src == -1
                    // Via De Morgan's law becomes: !(dst != MIN || src != -1)
                    // Also, we know that src != 0 in here, so we can use it to set REGISTER_SCRATCH to something not zero
                    self.emit_ins(X86Instruction::load_immediate(size, REGISTER_SCRATCH, 0)); // No XOR here because we need to keep the status flags
                    self.emit_ins(X86Instruction::cmov(size, 0x45, src, REGISTER_SCRATCH)); // if dst != MIN { REGISTER_SCRATCH = src; }
                    self.emit_ins(X86Instruction::cmp_immediate(size, src, -1, None)); // src == -1
                    self.emit_ins(X86Instruction::cmov(size, 0x45, src, REGISTER_SCRATCH)); // if src != -1 { REGISTER_SCRATCH = src; }
                    self.emit_ins(X86Instruction::test(size, REGISTER_SCRATCH, REGISTER_SCRATCH, None)); // REGISTER_SCRATCH == 0
                }

                // MIN / -1, raise EbpfError::DivideOverflow
                self.emit_ins(X86Instruction::load_immediate(OperandSize::S64, REGISTER_SCRATCH, self.pc as i64));
                self.emit_ins(X86Instruction::conditional_jump_immediate(0x84, self.relative_to_anchor(ANCHOR_DIV_OVERFLOW, 6)));
            }
        }

        if let Some(imm) = imm {
            if self.should_sanitize_constant(imm) {
                self.emit_sanitized_load_immediate(OperandSize::S64, REGISTER_SCRATCH, imm);
            } else {
                self.emit_ins(X86Instruction::load_immediate(OperandSize::S64, REGISTER_SCRATCH, imm));
            }
        } else {
            self.emit_ins(X86Instruction::mov(OperandSize::S64, src, REGISTER_SCRATCH));
        }
        if dst != RAX {
            self.emit_ins(X86Instruction::push(RAX, None));
            self.emit_ins(X86Instruction::mov(OperandSize::S64, dst, RAX));
        }
        if dst != RDX {
            self.emit_ins(X86Instruction::push(RDX, None));
        }
        if division {
            if signed {
                self.emit_ins(X86Instruction::sign_extend_rax_rdx(size));
            } else {
                self.emit_ins(X86Instruction::alu(size, 0x31, RDX, RDX, 0, None)); // RDX = 0
            }
        }

        self.emit_ins(X86Instruction::alu(size, 0xf7, 0x4 | (division as u8) << 1 | signed as u8, REGISTER_SCRATCH, 0, None));

        if dst != RDX {
            if alt_dst {
                self.emit_ins(X86Instruction::mov(OperandSize::S64, RDX, dst));
            }
            self.emit_ins(X86Instruction::pop(RDX));
        }
        if dst != RAX {
            if !alt_dst {
                self.emit_ins(X86Instruction::mov(OperandSize::S64, RAX, dst));
            }
            self.emit_ins(X86Instruction::pop(RAX));
        }
        if let OperandSize::S32 = size {
            if signed {
                self.emit_ins(X86Instruction::alu(OperandSize::S64, 0x63, dst, dst, 0, None)); // sign extend i32 to i64
            }
        }
    }


../.. \<close>



subsection  \<open> ALU \<close>
subsection  \<open> JUMP \<close>
subsection  \<open> MEM \<close>
subsection  \<open> CALL \<close>
subsection  \<open> EXIT \<close>
subsection  \<open> JIT_One \<close>



end