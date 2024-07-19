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
  else 
     \<comment> \<open>if h = 0x66 then P518 `Operand-size override prefix is encoded using 66H`  \<close>
    case t of [] \<Rightarrow> None | h1#[] \<Rightarrow> None | h1#h2#[] \<Rightarrow> None | rex#op#reg#t1 \<Rightarrow> (
      \<comment> \<open> P2882 `MOV register1 to register2` -> `0100 0R0B : 1000 100w : 11 reg1 reg2` \<close>
      if op = 0x89 then
        let r     = unsigned_bitfield_extract_u8 2 1 rex in
        let b     = unsigned_bitfield_extract_u8 0 1 rex in
        let modrm = unsigned_bitfield_extract_u8 6 2 reg in
        let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
        let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
        let src   = bitfield_insert_u8 3 1 reg1 r in
        let dst   = bitfield_insert_u8 3 1 reg2 b in
          if modrm = 0b11 then (
            case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pmovq_rr dst src # l) )))
          else
            None
      else if op = 0x01 then
      \<comment> \<open> P2887 `ADD register1 to register2` -> `0100 WR0B : 0000 000w : 11 reg1 reg2` \<close>
        let w     = unsigned_bitfield_extract_u8 3 1 rex in
        let r     = unsigned_bitfield_extract_u8 2 1 rex in
        let b     = unsigned_bitfield_extract_u8 0 1 rex in
        let modrm = unsigned_bitfield_extract_u8 6 2 reg in
        let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
        let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
        let src   = bitfield_insert_u8 3 1 reg1 r in
        let dst   = bitfield_insert_u8 3 1 reg2 b in
          if modrm = 0b11 then (
            case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Paddq_rr dst src # l)
              else 
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Paddl_rr dst src # l) )))
          else
            None
      else if op = 0x29 then
      \<comment> \<open> P2891 `SUB register1 from register2` -> `0100 WR0B : 0010 100w : 11 reg1 reg2` \<close> 
        let w     = unsigned_bitfield_extract_u8 3 1 rex in
        let r     = unsigned_bitfield_extract_u8 2 1 rex in
        let b     = unsigned_bitfield_extract_u8 0 1 rex in
        let modrm = unsigned_bitfield_extract_u8 6 2 reg in
        let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
        let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
        let src   = bitfield_insert_u8 3 1 reg1 r in
        let dst   = bitfield_insert_u8 3 1 reg2 b in
          if modrm = 0b11 then (
            case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Psubq_rr dst src # l)
              else 
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Psubl_rr dst src # l) )))
          else
            None
      else if op = 0xf7 then
      \<comment> \<open> P2884 `NEG register2` -> `0100 W00B : 1111 011w : 11011reg` \<close>
        let w     = unsigned_bitfield_extract_u8 3 1 rex in
        let r     = unsigned_bitfield_extract_u8 2 1 rex in
        let b     = unsigned_bitfield_extract_u8 0 1 rex in
        let modrm = unsigned_bitfield_extract_u8 6 2 reg in
        let opex  = unsigned_bitfield_extract_u8 3 3 reg in
        let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
        let dst   = bitfield_insert_u8 3 1 reg2 b in
          if (modrm = 0b11) \<and> (opex = 0b011) then (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pnegq dst # l) 
              else 
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pnegl dst # l))) 
          else
            None
      else if op = 0x09 then
      \<comment> \<open> P2884 `OR register1 to register2` -> ` 0100 WR0B : 0000 100w : 11 reg1 reg2` \<close>
        let w     = unsigned_bitfield_extract_u8 3 1 rex in
        let r     = unsigned_bitfield_extract_u8 2 1 rex in
        let b     = unsigned_bitfield_extract_u8 0 1 rex in
        let modrm = unsigned_bitfield_extract_u8 6 2 reg in
        let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
        let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
        let src   = bitfield_insert_u8 3 1 reg1 r in
        let dst   = bitfield_insert_u8 3 1 reg2 b in
          if modrm = 0b11 then (
            case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Porq_rr dst src # l) 
              else 
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Porl_rr dst src # l) )))
          else
            None
      else if op = 0x21 then
       \<comment> \<open> P2876 `AND register1 to register2` -> ` 0100 WR0B : 0000 100w : 11 reg1 reg2` \<close>
        let w     = unsigned_bitfield_extract_u8 3 1 rex in
        let r     = unsigned_bitfield_extract_u8 2 1 rex in
        let b     = unsigned_bitfield_extract_u8 0 1 rex in
        let modrm = unsigned_bitfield_extract_u8 6 2 reg in
        let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
        let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
        let src   = bitfield_insert_u8 3 1 reg1 r in
        let dst   = bitfield_insert_u8 3 1 reg2 b in
          if modrm = 0b11 then (
            case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pandq_rr dst src # l)
              else
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pandl_rr dst src # l))) ) 
          else
            None
       else if op = 0x31 then
         \<comment> \<open> P2893 `XOR register1 to register2` -> ` 0100 WRXB : 0011 000w : 11 reg1 reg2` \<close>
        let w     = unsigned_bitfield_extract_u8 3 1 rex in
        let r     = unsigned_bitfield_extract_u8 2 1 rex in
        let b     = unsigned_bitfield_extract_u8 0 1 rex in
        let modrm = unsigned_bitfield_extract_u8 6 2 reg in
        let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
        let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
        let src   = bitfield_insert_u8 3 1 reg1 r in
        let dst   = bitfield_insert_u8 3 1 reg2 b in
          if modrm = 0b11 then (
            case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pxorq_rr dst src # l)
              else
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pxorl_rr dst src # l))) ) 
          else
            None
       else
        None )
)"

(*
(**r 
 [Pmov_rr ireg.R8 ireg.RAX]"
(**r Some [102, 65, 137, 200] 11 001 000 *)
*)
value "x64_disassemble [102, 65, 137, 200]"
value "102 = (0x66::u8)"
value "137 = (0x89::u8)"

value "unsigned_bitfield_extract_u8 2 1 64" (**r r = 0 *)
value "unsigned_bitfield_extract_u8 0 1 64" (**r b = 0 *)
value "unsigned_bitfield_extract_u8 6 2 195" (**r modrm = 3 *)
value "unsigned_bitfield_extract_u8 3 3 200" (**r reg1 = 0 *)
value "unsigned_bitfield_extract_u8 0 3 195" (**r reg2 = 3 *)
value "bitfield_insert_u8 3 1 0 0" (**r src = 0 *)
value "bitfield_insert_u8 3 1  3 0" (**r dst = 3 *)
value "ireg_of_u8 0" (**r Some RAX *)
value "ireg_of_u8 3" (**r Some RBX *) *)

end