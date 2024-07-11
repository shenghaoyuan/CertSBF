theory x64Disassembler
imports
  Main
  rBPFCommType rBPFSyntax
  x64Syntax
begin

fun x64_disassemble :: "x64_bin \<Rightarrow> x64_asm option" where
"x64_disassemble [] = Some []" |
"x64_disassemble (h#t) = (
  if h = 0b10010000 then \<comment> \<open> P2884 `NOP – No Operation` -> `1001 0000` \<close>
    case x64_disassemble t of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pnop # l)
  else if h = 0x66 then \<comment> \<open> P518 `Operand-size override prefix is encoded using 66H`  \<close>
    case t of [] \<Rightarrow> None | h1#[] \<Rightarrow> None | h1#h2#[] \<Rightarrow> None | rex#op#reg#t1 \<Rightarrow> (
      \<comment> \<open> P2882 `MOV register1 to register2` -> `0100 0R0B : 1000 100w : 11 reg1 reg2` \<close>
      if op = 0x89 then
        let r     = unsigned_bitfield_extract_u8 2 1 rex in
        let b     = unsigned_bitfield_extract_u8 0 1 rex in
        let modrm = unsigned_bitfield_extract_u8 6 2 reg in
        let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
        let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
        let src   = bitfield_insert_u8 0 3 reg1 r in
        let dst   = bitfield_insert_u8 0 3 reg2 b in
          if modrm = 0b11 then (
            case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              case x64_disassemble t of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pmov_rr dst src # l) )))
          else
            None
      else
        None)
  else
    None
)"

end