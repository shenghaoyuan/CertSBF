section \<open> x86 \<close>

theory x86
imports
  Main
  rBPFCommType rBPFSyntax
  JITCommType
begin

abbreviation "RAX:: u8 \<equiv> 0"
abbreviation "RCX:: u8 \<equiv> 1"
abbreviation "RDX:: u8 \<equiv> 2"
abbreviation "RBX:: u8 \<equiv> 3"
abbreviation "RSP:: u8 \<equiv> 4"
abbreviation "RBP:: u8 \<equiv> 5"
abbreviation "RSI:: u8 \<equiv> 6"
abbreviation "RDI:: u8 \<equiv> 7"
abbreviation "R8 :: u8 \<equiv> 8"
abbreviation "R9 :: u8 \<equiv> 9"
abbreviation "R10:: u8 \<equiv> 10"
abbreviation "R11:: u8 \<equiv> 11"
abbreviation "R12:: u8 \<equiv> 12"
abbreviation "R13:: u8 \<equiv> 13"
abbreviation "R14:: u8 \<equiv> 14"
abbreviation "R15:: u8 \<equiv> 15"


(**
pub enum X86IndirectAccess {
    /// [second_operand + offset]
    Offset(i32),
    /// [second_operand + offset + index << shift]
    OffsetIndexShift(i32, u8, u8),
}
*)
datatype X86IndirectAccess =
  X86IndirectAccess_Offset i32 |
  X86IndirectAccess_OffsetIndexShift i32 u8 u8

record X86Instruction =
x86_ins_size                    :: OperandSize
x86_ins_opcode_escape_sequence  :: u8
x86_ins_opcode                  :: u8
x86_ins_modrm                   :: bool
x86_ins_indirect                :: "X86IndirectAccess option"
x86_ins_first_operand           :: u8
x86_ins_second_operand          :: u8
x86_ins_immediate_size          :: OperandSize
x86_ins_immediate               :: i64

text \<open> size = 4, align = 0x1 \<close>
record X86Rex =
x86_rex_w :: bool
x86_rex_r :: bool
x86_rex_x :: bool
x86_rex_b :: bool

definition upd_x86_rex_x :: "bool \<Rightarrow> X86Rex \<Rightarrow> X86Rex" where
"upd_x86_rex_x v m =
  \<lparr> x86_rex_w = x86_rex_w m, x86_rex_r = x86_rex_r m,
    x86_rex_x = v, x86_rex_b = x86_rex_b m \<rparr>"

text \<open> size = 3, align = 0x1 \<close>
record X86ModRm =
x86_rm_mode :: u8
x86_rm_r    :: u8
x86_rm_m    :: u8

definition upd_x86_rm_mode :: "u8 \<Rightarrow> X86ModRm \<Rightarrow> X86ModRm" where
"upd_x86_rm_mode v m =
  \<lparr> x86_rm_mode = v, x86_rm_r = x86_rm_r m, x86_rm_m = x86_rm_m m \<rparr>"


text \<open> size = 3, align = 0x1 \<close>
record X86Sib =
x86_sib_scale :: u8
x86_sib_index :: u8
x86_sib_base  :: u8

definition emit :: "X86Instruction \<Rightarrow> JitCompiler \<Rightarrow> JitCompiler option" where
"emit ins l = (
  if (x86_ins_size ins) = S0 then None else (
  \<comment> \<open> why? debug_assert!(!matches!(self.size, OperandSize::S0)) \<close>
  let rex = \<lparr>
              x86_rex_w = ((x86_ins_size ins) = S64),
              x86_rex_r = (and (x86_ins_first_operand ins) 0b1000 \<noteq> 0),
              x86_rex_x = False,
              x86_rex_b = (and (x86_ins_second_operand ins) 0b1000 \<noteq> 0)
            \<rparr> in (
  let modrm = \<lparr>
                x86_rm_mode = 0,
                x86_rm_r = and (x86_ins_first_operand ins) 0b111,
                x86_rm_m = and (x86_ins_first_operand ins) 0b111
              \<rparr> in (
  let sib = \<lparr>
              x86_sib_scale = 0,
              x86_sib_index = 0,
              x86_sib_base = 0
            \<rparr> in (
  let displacement_size = S0 in (
  let displacement = 0 in (

  let (rex, modrm, sib, displacement, displacement_size) = (
    if x86_ins_modrm ins then (
      case x86_ins_indirect ins of
        Some (X86IndirectAccess_Offset ofs) \<Rightarrow> (
\<comment>  \<open> ignore `debug_assert_ne!(self.second_operand & 0b111, RSP)  \<close>
          if ( (-128 \<le>s ofs) \<and> (ofs \<le>s 127) ) \<or>
             ( (ofs = 0) \<and> ((and (x86_ins_second_operand ins) 0b111) = RBP) ) then
            (rex, upd_x86_rm_mode 1 modrm, sib, ofs, S8)
          else
            (rex, upd_x86_rm_mode 2 modrm, sib, ofs, S32)
          ) | 
        Some (X86IndirectAccess_OffsetIndexShift ofs index shift) \<Rightarrow>
          (upd_x86_rex_x ((and index 0b1000) \<noteq> 0) rex,
            \<lparr> x86_rm_mode = 2, x86_rm_r = x86_rm_r modrm, x86_rm_m = RSP \<rparr>,
              \<lparr>
                x86_sib_scale = and shift 0b11,
                x86_sib_index = and index 0b111,
                x86_sib_base = and (x86_ins_second_operand ins) 0b111 \<rparr>,
                    ofs, S32) |
        _ \<Rightarrow> (rex, modrm, sib, displacement, displacement_size))
    else
      (rex, upd_x86_rm_mode 3 modrm, sib, displacement, displacement_size)) in (

    let l = (if x86_ins_size ins = S16 then jit_emit l [0x66]  else l) in (

    let rex::u8 = or (or (or  (((u8_of_bool (x86_rex_w rex))) << 3)
                              (((u8_of_bool (x86_rex_r rex))) << 2 ))
                              (((u8_of_bool (x86_rex_x rex))) << 1 ))
                              ((u8_of_bool (x86_rex_b rex))) in (

    let l = (if rex \<noteq> 0 then jit_emit l [(or 0x40 rex)] else l) in (

    let l = (
      if x86_ins_opcode_escape_sequence ins = 1 then
        jit_emit l [0x0f]
      else if x86_ins_opcode_escape_sequence ins = 2 then
        jit_emit l (u8_list_of_u16 0x0f38) \<comment>  \<open> 0x0f38 is first 0x38, then 0x0f  \<close>
      else if x86_ins_opcode_escape_sequence ins = 3 then
        jit_emit l [0x3a, 0x0f]
      else l
      ) in (

    let l = jit_emit l [(x86_ins_opcode ins)] in (

    let l = (
      if x86_ins_modrm ins then (
        let l = jit_emit l [( or (or  ((x86_rm_mode modrm) << 6)
                                      ((x86_rm_r modrm) << 3) )
                                      (x86_rm_m modrm) )] in (
        let sib = ( or (or  ((x86_sib_scale sib) << 6)
                            ((x86_sib_index sib) << 3) )
                            (x86_sib_base sib) ) in (
        let l = (if sib \<noteq> 0 then jit_emit l [sib] else l) in
          jit_emit_variable_length l displacement_size (ucast displacement)
      )))
      else l
      ) in (
    let l = jit_emit_variable_length l
      (x86_ins_immediate_size ins) (ucast (x86_ins_immediate ins)) in (
    Some l
  )))))))))))))))"


text \<open> ../..
 \<close>

end