section \<open> x86 \<close>

theory x86
imports
  Main
  rBPFCommType rBPFSyntax
  JITCommType x86CommType
begin

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

  let (rex, modrm, sib, displacement, displacement_size) =
    if x86_ins_modrm ins then
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
        _ \<Rightarrow> (rex, modrm, sib, displacement, displacement_size)
    else
      (rex, upd_x86_rm_mode 3 modrm, sib, displacement, displacement_size) in (

    let l = if x86_ins_size ins = S16 then jit_emit l [0x66]  else l in (

    let rex::u8 = or (or (or  (((u8_of_bool (x86_rex_w rex))) << 3)
                              (((u8_of_bool (x86_rex_r rex))) << 2 ))
                              (((u8_of_bool (x86_rex_x rex))) << 1 ))
                              ((u8_of_bool (x86_rex_b rex))) in (

    let l = (if rex \<noteq> 0 then jit_emit l [(or 0x40 rex)] else l) in (

    let l =
      if x86_ins_opcode_escape_sequence ins = 1 then
        jit_emit l [0x0f]
      else if x86_ins_opcode_escape_sequence ins = 2 then
        jit_emit l (u8_list_of_u16 0x0f38) \<comment>  \<open> 0x0f38 is first 0x38, then 0x0f  \<close>
      else if x86_ins_opcode_escape_sequence ins = 3 then
        jit_emit l [0x3a, 0x0f]
      else l
      in (

    let l = jit_emit l [(x86_ins_opcode ins)] in (

    let l =
      if x86_ins_modrm ins then
        let l = jit_emit l [( or (or  ((x86_rm_mode modrm) << 6)
                                      ((x86_rm_r modrm) << 3) )
                                      (x86_rm_m modrm) )] in
        let sib = ( or (or  ((x86_sib_scale sib) << 6)
                            ((x86_sib_index sib) << 3) )
                            (x86_sib_base sib) ) in
        let l = (if sib \<noteq> 0 then jit_emit l [sib] else l) in
          jit_emit_variable_length l displacement_size (ucast displacement)
      else l
       in (
    let l = jit_emit_variable_length l
      (x86_ins_immediate_size ins) (ucast (x86_ins_immediate ins)) in
      Some l
  ))))))))))))))"


definition DEFAULT :: "X86Instruction" where
"DEFAULT = \<lparr> 
  x86_ins_size                    = S0,
  x86_ins_opcode_escape_sequence  = 0,
  x86_ins_opcode                  = 0,
  x86_ins_modrm                   = True,
  x86_ins_indirect                = None,
  x86_ins_first_operand           = 0,
  x86_ins_second_operand          = 0,
  x86_ins_immediate_size          = S0,
  x86_ins_immediate               = 0
\<rparr>"

definition alu :: "OperandSize \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> i64
  \<Rightarrow> X86IndirectAccess option \<Rightarrow> X86Instruction option" where
"alu sz op src dst imm ind = (
  case sz of
  S0 \<Rightarrow> None |
  S8 \<Rightarrow> None |
  S16 \<Rightarrow> None |
  _ \<Rightarrow> Some \<lparr>
        x86_ins_size                    = sz,
        x86_ins_opcode_escape_sequence  = 0,
        x86_ins_opcode                  = op,
        x86_ins_modrm                   = True,
        x86_ins_indirect                = ind,
        x86_ins_first_operand           = src,
        x86_ins_second_operand          = dst,
        x86_ins_immediate_size          = (
               if op = 0xc1 then S8
          else if op = 0x81 then S32
          else if op = 0xf7 then (if src = 0 then S32 else S0)
          else S0
          ),
        x86_ins_immediate               = imm
      \<rparr>
)"


definition load_immediate :: "OperandSize \<Rightarrow> u8 \<Rightarrow> i64 \<Rightarrow> X86Instruction option" where
"load_immediate sz dst imm = (
  case sz of
  S0 \<Rightarrow> None |
  S8 \<Rightarrow> None |
  S16 \<Rightarrow> None |
  _ \<Rightarrow>
    let immediate_size =
      if (scast i32_MIN) \<le>s imm \<and> imm \<le>s (scast i32_MAX) then S32
      else S64 in (

    case sz of
      S32 \<Rightarrow> Some \<lparr>
              x86_ins_size                    = sz,
              x86_ins_opcode_escape_sequence  = 0,
              x86_ins_opcode                  = 0xc7,
              x86_ins_modrm                   = True,
              x86_ins_indirect                = None,
              x86_ins_first_operand           = 0,
              x86_ins_second_operand          = dst,
              x86_ins_immediate_size          = S32,
              x86_ins_immediate               = imm
            \<rparr> |
      S64 \<Rightarrow> Some \<lparr>
              x86_ins_size                    = sz,
              x86_ins_opcode_escape_sequence  = 0,
              x86_ins_opcode                  = or 0xb8 (and dst 0b111),
              x86_ins_modrm                   = False,
              x86_ins_indirect                = None,
              x86_ins_first_operand           = 0,
              x86_ins_second_operand          = dst,
              x86_ins_immediate_size          = S64,
              x86_ins_immediate               = imm
            \<rparr> |
      _ \<Rightarrow>  None \<comment>  \<open> unimplemented  \<close> )
)"

text \<open> ../..

 \<close>




end