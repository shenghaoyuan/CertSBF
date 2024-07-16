section \<open> x86 \<close>

theory x86
imports
  Main
  rBPFCommType rBPFSyntax
  JITCommType x86CommType
begin

datatype X86IndirectAccess =
  X86IndirectAccess_Offset i32 |
  X86IndirectAccess_OffsetIndexShift i32 u8 u8

datatype FenceType = FT_Load |  FT_All | FT_Store

definition u8_of_fence_type :: "FenceType \<Rightarrow> u8" where
"u8_of_fence_type ft = (
  case ft of
  FT_Load   \<Rightarrow> 5 |
  FT_All    \<Rightarrow> 6 |
  FT_Store  \<Rightarrow> 7
)"

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
            (rex, modrm \<lparr> x86_rm_mode := 1 \<rparr>, sib, ofs, S8)
          else
            (rex, modrm \<lparr> x86_rm_mode := 2 \<rparr>, sib, ofs, S32)
          ) | 
        Some (X86IndirectAccess_OffsetIndexShift ofs index shift) \<Rightarrow>
          (rex \<lparr> x86_rex_x := (and index 0b1000) \<noteq> 0 \<rparr>,
            \<lparr> x86_rm_mode = 2, x86_rm_r = x86_rm_r modrm, x86_rm_m = RSP \<rparr>,
              \<lparr>
                x86_sib_scale = and shift 0b11,
                x86_sib_index = and index 0b111,
                x86_sib_base = and (x86_ins_second_operand ins) 0b111 \<rparr>,
                    ofs, S32) |
        _ \<Rightarrow> (rex, modrm, sib, displacement, displacement_size)
    else
      (rex, modrm \<lparr> x86_rm_mode := 3 \<rparr>, sib, displacement, displacement_size) in (

    let l = if x86_ins_size ins = S16 then jit_emit l [0x66]  else l in (

    let rex::u8 = construct_rex_to_u8 (x86_rex_w rex) (x86_rex_r rex) (x86_rex_x rex) (x86_rex_b rex) in (

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
        let l = jit_emit l [construct_modsib_to_u8 (x86_rm_mode modrm) (x86_rm_r modrm) (x86_rm_m modrm)] in
        let sib =construct_modsib_to_u8 (x86_sib_scale sib) (x86_sib_index sib) (x86_sib_base sib) in
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
  _ \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size            := sz,
        x86_ins_opcode          := op,
        x86_ins_indirect        := ind,
        x86_ins_first_operand   := src,
        x86_ins_second_operand  := dst,
        x86_ins_immediate_size  := (
               if op = 0xc1 then S8
          else if op = 0x81 then S32
          else if op = 0xf7 then (if src = 0 then S32 else S0)
          else S0
          ),
        x86_ins_immediate       := imm
      \<rparr>)
)"
        
definition mov :: "OperandSize \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> X86Instruction option" where
"mov sz src dst = (
  case sz of
  S0 \<Rightarrow> None |
  S8 \<Rightarrow> None |
  S16 \<Rightarrow> None |
  _ \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size            := sz,
        x86_ins_opcode          := 0x89,
        x86_ins_first_operand   := src,
        x86_ins_second_operand  := dst
      \<rparr>)
)"
        
definition cmov :: "OperandSize \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> X86Instruction option" where
"cmov sz cond src dst = (
  case sz of
  S0 \<Rightarrow> None |
  S8 \<Rightarrow> None |
  S16 \<Rightarrow> None |
  _ \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size                    := sz,
        x86_ins_opcode_escape_sequence  := 1,
        x86_ins_opcode                  := cond,
        x86_ins_first_operand           := dst,
        x86_ins_second_operand          := src
      \<rparr>)
)"
        
definition xchg :: "OperandSize \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow> X86IndirectAccess option \<Rightarrow> X86Instruction option" where
"xchg sz src dst ind = (
  case sz of
  S0 \<Rightarrow> None |
  S8 \<Rightarrow> None |
  S16 \<Rightarrow> None |
  S32 \<Rightarrow> None |
  _ \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size            := sz,
        x86_ins_opcode          := 0x87,
        x86_ins_first_operand   := src,
        x86_ins_second_operand  := dst,
        x86_ins_indirect        := ind
      \<rparr>)
)"
        
definition bswap :: "OperandSize \<Rightarrow> u8 \<Rightarrow> X86Instruction option" where
"bswap sz dst = (
  case sz of
  S0 \<Rightarrow> None |
  S8 \<Rightarrow> None |
  S16 \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size            := sz,
        x86_ins_opcode          := 0xc1,
        x86_ins_second_operand  := dst,
        x86_ins_immediate_size  := S8,
        x86_ins_immediate       := 8
      \<rparr>) |
  S32 \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size                    := sz,
        x86_ins_opcode_escape_sequence  := 1,
        x86_ins_opcode                  := or 0xc8 (and dst 0b111),
        x86_ins_modrm                   := False,
        x86_ins_second_operand          := dst
      \<rparr>) |
  S64 \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size                    := sz,
        x86_ins_opcode_escape_sequence  := 1,
        x86_ins_opcode                  := or 0xc8 (and dst 0b111),
        x86_ins_modrm                   := False,
        x86_ins_second_operand          := dst
      \<rparr>)
)"

definition test :: "OperandSize \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow>
  X86IndirectAccess option \<Rightarrow> X86Instruction option" where
"test sz src dst ind = (
  case sz of
  S0 \<Rightarrow> None |
  _ \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size            := sz,
        x86_ins_opcode          := if sz = S8 then 0x84 else 0x85,
        x86_ins_indirect        := ind,
        x86_ins_first_operand   := src,
        x86_ins_second_operand  := dst
      \<rparr>)
)"

definition test_immediate :: "OperandSize \<Rightarrow> u8 \<Rightarrow> i64 \<Rightarrow>
  X86IndirectAccess option \<Rightarrow> X86Instruction option" where
"test_immediate sz dst imm ind = (
  case sz of
  S0 \<Rightarrow> None |
  _ \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size            := sz,
        x86_ins_opcode          := if sz = S8 then 0xf6 else 0xf7,
        x86_ins_first_operand   := RAX,
        x86_ins_second_operand  := dst,
        x86_ins_immediate_size  := if sz = S64 then S32 else sz,
        x86_ins_immediate       := imm,
        x86_ins_indirect        := ind
      \<rparr>)
)"

definition cmp :: "OperandSize \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow>
  X86IndirectAccess option \<Rightarrow> X86Instruction option" where
"cmp sz src dst ind = (
  case sz of
  S0 \<Rightarrow> None |
  _ \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size            := sz,
        x86_ins_opcode          := if sz = S8 then 0x38 else 0x39,
        x86_ins_first_operand   := src,
        x86_ins_second_operand  := dst,
        x86_ins_indirect        := ind
      \<rparr>)
)"

definition cmp_immediate :: "OperandSize \<Rightarrow> u8 \<Rightarrow> i64 \<Rightarrow>
  X86IndirectAccess option \<Rightarrow> X86Instruction option" where
"cmp_immediate sz dst imm ind = (
  case sz of
  S0 \<Rightarrow> None |
  _ \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size            := sz,
        x86_ins_opcode          := if sz = S8 then 0x80 else 0x81,
        x86_ins_first_operand   := RDI,
        x86_ins_second_operand  := dst,
        x86_ins_immediate_size  := if sz = S64 then S32 else sz,
        x86_ins_immediate       := imm,
        x86_ins_indirect        := ind
      \<rparr>)
)"

definition lea :: "OperandSize \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow>
  X86IndirectAccess option \<Rightarrow> X86Instruction option" where
"lea sz src dst ind = (
  case sz of
  S0 \<Rightarrow> None |
  S8 \<Rightarrow> None |
  S16 \<Rightarrow> None |
  S32 \<Rightarrow> None |
  S64 \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size            := sz,
        x86_ins_opcode          := 0x8d,
        x86_ins_first_operand   := dst,
        x86_ins_second_operand  := src,
        x86_ins_indirect        := ind
      \<rparr>)
)"

definition sign_extend_rax_rdx :: "OperandSize \<Rightarrow> X86Instruction option" where
"sign_extend_rax_rdx sz = (
  case sz of
  S0 \<Rightarrow> None |
  S8 \<Rightarrow> None |
  S16 \<Rightarrow> None |
  _ \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size            := sz,
        x86_ins_opcode          := 0x99,
        x86_ins_modrm           := False
      \<rparr>)
)"

definition load :: "OperandSize \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow>
  X86IndirectAccess \<Rightarrow> X86Instruction option" where
"load sz src dst ind = (
  case sz of
  S0 \<Rightarrow> None |
  _  \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size                    := if sz = S64 then S64 else S32,
        x86_ins_opcode_escape_sequence  := (case sz of S8 \<Rightarrow> 1 | S16 \<Rightarrow> 1 | _ \<Rightarrow> 0 ),
        x86_ins_opcode                  := (case sz of S8 \<Rightarrow> 0xb6 | S16 \<Rightarrow> 0xb7 | _ \<Rightarrow> 0x8b),
        x86_ins_first_operand           := dst,
        x86_ins_second_operand          := src,
        x86_ins_indirect                := Some ind
      \<rparr>)
)"

definition store :: "OperandSize \<Rightarrow> u8 \<Rightarrow> u8 \<Rightarrow>
  X86IndirectAccess \<Rightarrow> X86Instruction option" where
"store sz src dst ind = (
  case sz of
  S0 \<Rightarrow> None |
  _  \<Rightarrow> Some (DEFAULT \<lparr>
        x86_ins_size                    := sz,
        x86_ins_opcode                  := (case sz of S8 \<Rightarrow> 0x88 | _ \<Rightarrow> 0x89),
        x86_ins_first_operand           := src,
        x86_ins_second_operand          := dst,
        x86_ins_indirect                := Some ind
      \<rparr>)
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
      S32 \<Rightarrow> Some (DEFAULT \<lparr>
              x86_ins_size            := sz,
              x86_ins_opcode          := 0xc7,
              x86_ins_second_operand  := dst,
              x86_ins_immediate_size  := S32,
              x86_ins_immediate       := imm
            \<rparr>) |
      S64 \<Rightarrow> Some (DEFAULT \<lparr>
              x86_ins_size            := sz,
              x86_ins_opcode          := or 0xb8 (and dst 0b111),
              x86_ins_modrm           := False,
              x86_ins_second_operand  := dst,
              x86_ins_immediate_size  := S64,
              x86_ins_immediate       := imm
            \<rparr>) |
      _ \<Rightarrow>  None \<comment>  \<open> unimplemented  \<close> )
)"

definition store_immediate ::
  "OperandSize \<Rightarrow> u8 \<Rightarrow> X86IndirectAccess \<Rightarrow> i64 \<Rightarrow> X86Instruction option" where
"store_immediate sz dst ind imm = (
  case sz of
  S0 \<Rightarrow> None |
  _ \<Rightarrow>  Some (DEFAULT \<lparr>
          x86_ins_size            := sz,
          x86_ins_opcode          := case sz of S8 \<Rightarrow> 0xc6 | _ \<Rightarrow> 0xc7,
          x86_ins_second_operand  := dst,
          x86_ins_indirect        := Some ind,
          x86_ins_immediate_size  := if sz = S64 then S32 else sz,
          x86_ins_immediate       := imm
        \<rparr>)
)"

definition push_immediate :: "OperandSize \<Rightarrow> i32 \<Rightarrow> X86Instruction option" where
"push_immediate sz imm = (
  case sz of
  S0 \<Rightarrow> None |
  S16 \<Rightarrow> None |
  _ \<Rightarrow>  Some (DEFAULT \<lparr>
          x86_ins_size            := sz,
          x86_ins_opcode          := case sz of S8 \<Rightarrow> 0x6A | _ \<Rightarrow> 0x68,
          x86_ins_modrm           := False,
          x86_ins_immediate_size  := if sz = S64 then S32 else sz,
          x86_ins_immediate       := (scast imm)
        \<rparr>)
)"

definition push :: "u8 \<Rightarrow> X86IndirectAccess option \<Rightarrow> X86Instruction" where
"push src ind = (
  case ind of
  None \<Rightarrow> DEFAULT \<lparr>
            x86_ins_size            := S32,
            x86_ins_opcode          := or 0x50 (and src 0b111),
            x86_ins_modrm           := False,
            x86_ins_second_operand  := src
          \<rparr> |
  Some i \<Rightarrow> DEFAULT \<lparr>
          x86_ins_size            := S64,
          x86_ins_opcode          := 0xFF,
          x86_ins_modrm           := True,
          x86_ins_first_operand   := 6,
          x86_ins_second_operand  := src,
          x86_ins_indirect        := ind
        \<rparr>
)"

definition pop :: "u8 \<Rightarrow> X86Instruction" where
"pop dst = DEFAULT \<lparr>
          x86_ins_size            := S32,
          x86_ins_opcode          := or 0x58 (and dst 0b111),
          x86_ins_modrm           := False,
          x86_ins_second_operand  := dst
        \<rparr>"

definition conditional_jump_immediate :: " u8 \<Rightarrow> i32 \<Rightarrow> X86Instruction" where
"conditional_jump_immediate op rel_dst = DEFAULT \<lparr>
    x86_ins_size                    := S32,
    x86_ins_opcode_escape_sequence  := 1,
    x86_ins_opcode                  := op,
    x86_ins_modrm                   := False,
    x86_ins_immediate_size          := S32,
    x86_ins_immediate               := (scast rel_dst)
  \<rparr>"

definition jump_immediate :: " i32 \<Rightarrow> X86Instruction" where
"jump_immediate rel_dst = DEFAULT \<lparr>
    x86_ins_size            := S32,
    x86_ins_opcode          := 0xe9,
    x86_ins_modrm           := False,
    x86_ins_immediate_size  := S32,
    x86_ins_immediate       := (scast rel_dst)
  \<rparr>"

definition call_immediate :: " i32 \<Rightarrow> X86Instruction" where
"call_immediate rel_dst = DEFAULT \<lparr>
    x86_ins_size            := S32,
    x86_ins_opcode          := 0xe8,
    x86_ins_modrm           := False,
    x86_ins_immediate_size  := S32,
    x86_ins_immediate       := (scast rel_dst)
  \<rparr>"

definition call_reg :: " u8 \<Rightarrow> X86IndirectAccess option \<Rightarrow> X86Instruction" where
"call_reg dst ind = DEFAULT \<lparr>
    x86_ins_size            := S64,
    x86_ins_opcode          := 0xff,
    x86_ins_first_operand   := 2,
    x86_ins_second_operand  := dst,
    x86_ins_indirect        := ind
  \<rparr>"

definition return_near :: "X86Instruction" where
"return_near = DEFAULT \<lparr>
    x86_ins_size            := S32,
    x86_ins_opcode          := 0xc3,
    x86_ins_modrm           := False
  \<rparr>"

definition noop :: "X86Instruction" where
"noop = DEFAULT \<lparr>
    x86_ins_size            := S32,
    x86_ins_opcode          := 0x90,
    x86_ins_modrm           := False
  \<rparr>"

definition interrupt :: "u8 \<Rightarrow> X86Instruction" where
"interrupt imm = (
  if imm = 3 then
    DEFAULT \<lparr>
      x86_ins_size            := S32,
      x86_ins_opcode          := 0xcc,
      x86_ins_modrm           := False
    \<rparr>
  else
    DEFAULT \<lparr>
      x86_ins_size            := S32,
      x86_ins_opcode          := 0xcd,
      x86_ins_modrm           := False,
      x86_ins_immediate_size  := S8,
      x86_ins_immediate       := (scast imm)
    \<rparr>
)"

definition cycle_count :: "X86Instruction" where
"cycle_count = DEFAULT \<lparr>
    x86_ins_size                    := S32,
    x86_ins_opcode_escape_sequence  := 1,
    x86_ins_opcode                  := 0x31,
    x86_ins_modrm                   := False
  \<rparr>"

definition fence :: "FenceType \<Rightarrow> X86Instruction" where
"fence ft = DEFAULT \<lparr>
    x86_ins_size                    := S32,
    x86_ins_opcode_escape_sequence  := 1,
    x86_ins_opcode                  := 0xae,
    x86_ins_first_operand           := u8_of_fence_type ft
  \<rparr>"

end