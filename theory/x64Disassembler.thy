theory x64Disassembler
imports
  Main
  rBPFCommType rBPFSyntax
  x64Syntax
begin

(*    *)

fun x64_disassemble :: "x64_bin \<Rightarrow> x64_asm option" where
"x64_disassemble [] = Some []" |  
"x64_disassemble (h#t) = (
  
  if h = 0x90 then \<comment> \<open> P2884 `NOP – No Operation` -> `1001 0000` \<close>
    case x64_disassemble t of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pnop # l)
  else 
    if h = 0x66 then 
      case t of [] \<Rightarrow> None | h1#t1 \<Rightarrow>(
      if unsigned_bitfield_extract_u8 4 4 h1 \<noteq> 0b0100 then \<comment> \<open> h1 is not rex \<close>
        case t1 of [] \<Rightarrow> None | reg#t2 \<Rightarrow>(
          let modrm = unsigned_bitfield_extract_u8 6 2 reg in
          let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
          let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
          let src   = bitfield_insert_u8 3 1 reg1 0 in
          let dst   = bitfield_insert_u8 3 1 reg2 0 in
          if h1 = 0xc1 then 
            case t2 of [] \<Rightarrow> None | imm#t3 \<Rightarrow> (
            if modrm = 0b11 \<and> src = 0b000 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                case x64_disassemble t2 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Prolw_ri dst imm # l))
            else None )
          else if h1 = 0x89 then 
                 if modrm = 0b01 then
                   if ireg_of_u8 src = Some R11 \<and>
                      ireg_of_u8 dst = Some R10 then
                      case x64_disassemble t2 of None \<Rightarrow> None | Some l \<Rightarrow>
                        \<comment> \<open> Some (Pmovw_rm R10 (Addrmode (Some R11) None 0) # l)  \<close>
                        Some (Pmov_rm R11 (Addrmode (Some R10) None 0) M16 # l)
                   else None
                 else None
               else None)
      else 
        let w = unsigned_bitfield_extract_u8 3 1 h1 in
        let r = unsigned_bitfield_extract_u8 2 1 h1 in
        let x = unsigned_bitfield_extract_u8 1 1 h1 in
        let b = unsigned_bitfield_extract_u8 0 1 h1 in
        case t1 of [] \<Rightarrow> None | h1#[] \<Rightarrow> None | op#reg#t2 \<Rightarrow>( 
          let modrm = unsigned_bitfield_extract_u8 6 2 reg in
          let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
          let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
          let src   = bitfield_insert_u8 3 1 reg1 r in
          let dst   = bitfield_insert_u8 3 1 reg2 b in
          if h1 = 0xc1 then 
            case t2 of [] \<Rightarrow> None | imm#t3 \<Rightarrow> (
            if modrm = 0b11 \<and> src = 0b000 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                case x64_disassemble t2 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Prolw_ri dst imm # l))
             else None )
          else if op = 0x89 then 
            if modrm = 0b11 then
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                case x64_disassemble t2 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pmovl_rr dst src # l)))
            else None
          else None))
  else
    if unsigned_bitfield_extract_u8 4 4 h \<noteq> 0b0100 then  \<comment> \<open> h is not rex  \<close>
     \<comment> \<open> 32-bit instructions and default 64-bit instruction\<close>
        if h = 0x0f then \<comment> \<open> with opcode escape sequence 0x0f \<close>
        \<comment> \<open> P2885 `RDTSC – Read Time-Stamp Counter` -> `0000 1111 : 0011 0001` \<close>
          case t of [] \<Rightarrow> None | h1#t1 \<Rightarrow>(
            if h1 = 0x31 then 
              case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Prdtsc # l)
            else if h1 = 0x45 then
              None
            else
              None)
        else 
        \<comment> \<open> without rex and  opcode escape sequence \<close>
          case t of [] \<Rightarrow> None | reg#t1 \<Rightarrow> ( 
            let modrm = unsigned_bitfield_extract_u8 6 2 reg in
            let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
            let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
            let src   = bitfield_insert_u8 3 1 reg1 0 in
            let dst   = bitfield_insert_u8 3 1 reg2 0 in
          if h = 0x89 then 
            if modrm = 0b11 then
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pmovl_rr dst src # l)))
             else None
          else if h = 0x01 then
            if modrm = 0b11 then
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Paddl_rr dst src # l))) 
             else
               None
          else 
            None)
    else  \<comment> \<open> h is rex  \<close>
     \<comment> \<open> 64-bit instructions and 32-bit instructions accessing extended registers  (R8-R15) \<close>
    let w = unsigned_bitfield_extract_u8 3 1 h in
    let r = unsigned_bitfield_extract_u8 2 1 h in
    let x = unsigned_bitfield_extract_u8 1 1 h in
    let b = unsigned_bitfield_extract_u8 0 1 h in
      case t of [] \<Rightarrow> None | h1#[] \<Rightarrow> None | op#reg#t1 \<Rightarrow> (
        let modrm = unsigned_bitfield_extract_u8 6 2 reg in
        let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
        let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
        let src   = bitfield_insert_u8 3 1 reg1 r in
        let dst   = bitfield_insert_u8 3 1 reg2 b in
          if h = 0x0f then None
          else
          \<comment> \<open> P2882 `MOV register1 to register2` -> `0100 WR0B : 1000 100w : 11 reg1 reg2` \<close>
          if op = 0x89 then
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then   \<comment> \<open> rex should be `W=1` and `X=0`\<close>
                  case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pmovq_rr dst src # l) 
                else if w = 0 \<and> x = 0 then 
                  case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pmovl_rr dst src # l)
                else None))) 
            else
              None
          else if op = 0x01 then
          \<comment> \<open> P2887 `ADD register1 to register2` -> `0100 WR0B : 0000 000w : 11 reg1 reg2` \<close>
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
          \<comment> \<open> P2884 `NEG  register2`                           -> ` 0100 W00B : 1111 011w : 11 011 reg` \<close>
          \<comment> \<open> P2884 `MUL  AL, AX, or EAX with register2`       -> ` 0100 000B : 1111 011w : 11 100 reg` \<close>
          \<comment> \<open> P2884 `MUL  RAX with qwordregister (to RDX:RAX)` -> ` 0100 100B : 1111 011w : 11 100 qowrdreg` \<close>
          \<comment> \<open> P2880 `IMUL AL, AX, or EAX with register2`       -> ` 0100 000B : 1111 011w : 11 101 reg` \<close>
          \<comment> \<open> P2880 `IMUL RAX with qwordregister (to RDX:RAX)` -> ` 0100 100B : 1111 011w : 11 101 qwordreg` \<close>
          \<comment> \<open> P2879 `DIV AL, AX, or EAX by register2`          -> ` 0100 000B : 1111 011w : 11 110 reg` \<close>
          \<comment> \<open> P2879 `DIV EAX by qwordregister (to RDX:RAX)`    -> ` 0100 100B : 1111 011w : 11 110 qwordreg` \<close>
          \<comment> \<open> P2879 `IDIV AL, AX, or EAX by register2`         -> ` 0100 000B : 1111 011w : 11 111 reg` \<close>
          \<comment> \<open> P2879 `IDIV RAX by qwordregister (to RDX:RAX)`   -> ` 0100 100B : 1111 011w : 11 111 qwordreg` \<close>
          if modrm = 0b11 \<and> reg1 = 0b011 then 
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pnegq dst # l) 
              else 
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pnegl dst # l))
             
          else if modrm = 0b11 \<and> reg1 = 0b100 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pmulq_r dst # l) 
              else 
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pmull_r dst # l))
          else if modrm = 0b11 \<and> reg1 = 0b101 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pimulq_r dst # l) 
              else 
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pimull_r dst # l))
          else if modrm = 0b11 \<and> reg1 = 0b110 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pdivq_r dst # l) 
              else 
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pdivl_r dst # l))
          else if modrm = 0b11 \<and> reg1 = 0b111 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pidivq_r dst # l) 
              else 
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pidivl_r dst # l))
          else None
        else if op = 0x09 then
        \<comment> \<open> P2884 `OR register1 to register2` -> ` 0100 WR0B : 0000 100w : 11 reg1 reg2` \<close>
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
          if modrm = 0b11 then (
            case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pxorq_rr dst src # l)
              else
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pxorl_rr dst src # l))) ) 
          else
            None
         else if op = 0xc1 then
        \<comment> \<open> P2889 `SHL register by immediate count`      -> ` 0100 000B 1100 000w : 11 100 reg : imm8 ` \<close>
        \<comment> \<open> P2889 `SHL qwordregister by immediate count` -> ` 0100 100B 1100 000w : 11 100 reg : imm8 ` \<close>
        \<comment> \<open> P2890 `SHR register by immediate count`      -> ` 0100 000B 1100 000w : 11 101 reg : imm8 ` \<close>
        \<comment> \<open> P2890 `SHR qwordregister by immediate count` -> ` 0100 100B 1100 000w : 11 101 reg : imm8 ` \<close>
        \<comment> \<open> P2888 `SAR register by immediate count`      -> ` 0100 000B 1100 000w : 11 111 reg : imm8 ` \<close>
        \<comment> \<open> P2888 `SAR qwordregister by immediate count` -> ` 0100 100B 1100 000w : 11 111 reg : imm8 ` \<close>
          case t1 of
              [] \<Rightarrow> None 
            | imm#t2 \<Rightarrow> ( 
                if modrm = 0b11 \<and> reg1 = 0b100 then 
                  case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                    if w = 1 then
                      case x64_disassemble t2 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pshlq_ri dst imm # l)
                    else
                      case x64_disassemble t2 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pshll_ri dst imm # l))
                else if modrm = 0b11 \<and> reg1 = 0b101 then 
                  case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                    if w = 1 then
                      case x64_disassemble t2 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pshrq_ri dst imm # l)
                    else
                      case x64_disassemble t2 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pshrl_ri dst imm # l))
                else if modrm = 0b11 \<and> reg1 = 0b111 then 
                  case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                    if w = 1 then
                      case x64_disassemble t2 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Psarq_ri dst imm # l)
                    else
                      case x64_disassemble t2 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Psarl_ri dst imm # l))
                else None)
        else if op = 0xd3 then
        \<comment> \<open> P2889 `SHL register by CL`                   -> ` 0100 000B 1100 000w : 11 100 reg ` \<close>
        \<comment> \<open> P2889 `SHL qwordregister by CL`              -> ` 0100 100B 1100 000w : 11 100 reg ` \<close>
        \<comment> \<open> P2890 `SHR register by CL`                   -> ` 0100 000B 1100 000w : 11 101 reg ` \<close>
        \<comment> \<open> P2890 `SHR qwrodregister by CL`              -> ` 0100 100B 1100 000w : 11 101 reg ` \<close>
        \<comment> \<open> P2888 `SAR register by CL`                   -> ` 0100 000B 1100 000w : 11 111 reg ` \<close>
        \<comment> \<open> P2888 `SAR qwordregister by CL`              -> ` 0100 100B 1100 000w : 11 111 reg ` \<close>
          if modrm = 0b11 \<and> reg1 = 0b100 then 
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pshlq_r dst # l) 
              else 
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pshll_r dst # l)) 
          else if modrm = 0b11 \<and> reg1 = 0b101 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pshrq_r dst # l) 
              else 
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pshrl_r dst # l)) 
          else if modrm = 0b11 \<and> reg1 = 0b111 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Psarq_r dst # l) 
              else 
                case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Psarl_r dst # l)) 
          else None
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