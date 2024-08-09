theory x64Disassembler
imports
  Main
  rBPFCommType rBPFSyntax
  x64Syntax
begin

(*
value "[(1::nat)]!(0::nat)"

value "[(1::nat)]!(1::nat)" returns an error, we should have a nth_error? *)

definition x64_decode :: "nat \<Rightarrow> x64_bin \<Rightarrow> (nat * instruction) option" where
"x64_decode pc l_bin = (
  let h = l_bin!pc in
    if h = 0x90 then \<comment> \<open> P2884 `NOP – No Operation` -> `1001 0000` \<close> Some (1, Pnop)
    else if h = 0x66 then  \<comment> \<open> 16-bit mode \<close>
      let h1 = l_bin!(pc+1) in
        if unsigned_bitfield_extract_u8 4 4 h1 \<noteq> 0b0100 then \<comment> \<open> h1 is not rex \<close>
          let reg = l_bin!(pc+2) in
          let modrm = unsigned_bitfield_extract_u8 6 2 reg in
          let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
          let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
          let src   = bitfield_insert_u8 3 1 reg1 0 in
          let dst   = bitfield_insert_u8 3 1 reg2 0 in
            if h1 = 0xc1 then 
           \<comment> \<open> P2887 `ROL : register by immediate count` -> `0x66 1100 000w : 11 000 reg : imm8` \<close>
              let imm = l_bin!(pc+3) in
                if modrm = 0b11 \<and> src = 0b000 then
                  case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                    Some (4, Prolw_ri dst imm))
                else None
            else  None
        else  \<comment> \<open> h1 is rex \<close>
          let w = unsigned_bitfield_extract_u8 3 1 h1 in
          let r = unsigned_bitfield_extract_u8 2 1 h1 in
          let x = unsigned_bitfield_extract_u8 1 1 h1 in
          let b = unsigned_bitfield_extract_u8 0 1 h1 in
            let op = l_bin!(pc+2) in let reg = l_bin!(pc+3) in 
            let modrm = unsigned_bitfield_extract_u8 6 2 reg in
            let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
            let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
            let src   = bitfield_insert_u8 3 1 reg1 r in
            let dst   = bitfield_insert_u8 3 1 reg2 b in
              if op = 0xc1 then 
              \<comment> \<open> P2887 `ROL : register by immediate count` -> `0x66 1100 000w : 11 000 reg : imm8` \<close>
                let imm = l_bin!(pc+4) in
                  if modrm = 0b11 \<and> src = 0b000 then
                    case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                      Some (5, Prolw_ri dst imm))
                  else None
              else if op = 0x89 then 
              \<comment> \<open> P2882 ` MOV: reg to memory`  ->  `66H 0100 0RXB : 1000 1001 : mod reg r/m `\<close>
                if modrm = 0b01 then
                  if ireg_of_u8 src = Some R10 \<and> ireg_of_u8 dst = Some R11 then
                    Some (4, Pmov_mr (Addrmode (Some R11) None 0) R10  M16)
                  else None
                else None
              else None
    else if unsigned_bitfield_extract_u8 4 4 h \<noteq> 0b0100 then  \<comment> \<open> h is not rex  \<close>
      \<comment> \<open> 8/32-bit mode \<close>
      if h = 0x0f then \<comment> \<open> 8/32-bit mode with opcode escape sequence 0x0f \<close>
        \<comment> \<open> P2885 `RDTSC – Read Time-Stamp Counter` -> `0000 1111 : 0011 0001` \<close>
        let h1 = l_bin!(pc+1) in
          if h1 = 0x31 then Some (2, Prdtsc)
          else if h1 = 0x45 then None
          else None
      else 
        \<comment> \<open> 8/32bit mode without rex and opcode escape sequence \<close>
        let reg = l_bin!(pc+1) in
        let modrm = unsigned_bitfield_extract_u8 6 2 reg in
        let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
        let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
        let src   = bitfield_insert_u8 3 1 reg1 0 in
        let dst   = bitfield_insert_u8 3 1 reg2 0 in
          if h = 0x89 then 
            if modrm = 0b11 then
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                Some (2, Pmovl_rr dst src)))
            else None
          else if h = 0x01 then
            if modrm = 0b11 then
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                Some (2, Paddl_rr dst src))) 
            else None
          else if h = 0x81 then
         \<comment> \<open> P2876 `ADD immediate to register` -> `0100 000B : 1000 00sw : 11 000 reg : immediate data` \<close>
            if modrm = 0b11 \<and> reg1 = 0b000 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                let i1 = l_bin!(pc+2)  in
                let i2 = l_bin!(pc+3)  in
                let i3 = l_bin!(pc+4)  in
                let i4 = l_bin!(pc+5)  in
                let imm::u32 = u32_of_u8_list [i1,i2,i3,i4] in
                  Some (5, Paddl_ri dst imm))
            else None
          else None
    else  \<comment> \<open> h is rex  \<close>
     \<comment> \<open> 64-bit or 32-bit instructions accessing extended registers  (R8-R15) \<close>
      let w = unsigned_bitfield_extract_u8 3 1 h in
      let r = unsigned_bitfield_extract_u8 2 1 h in
      let x = unsigned_bitfield_extract_u8 1 1 h in
      let b = unsigned_bitfield_extract_u8 0 1 h in
      let op = l_bin!(pc+1) in let reg = l_bin!(pc+2) in (
      let modrm = unsigned_bitfield_extract_u8 6 2 reg in
      let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
      let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
      let src   = bitfield_insert_u8 3 1 reg1 r in
      let dst   = bitfield_insert_u8 3 1 reg2 b in
        if h = 0x0f then None
        else if h = 0x88 then
          \<comment> \<open> P2882 ` MOV: reg to memory`  ->  `0100 0RXB : 1000 1000 : mod reg r/m `\<close>
          if modrm = 0b01 then
            if ireg_of_u8 src = Some R10 \<and> ireg_of_u8 dst = Some R11 then
              Some (3, Pmov_mr (Addrmode (Some R11)  None 0) R10  M8)
            else None
          else None
        else if op = 0x89 then
          if modrm = 0b11 then (
          \<comment> \<open> P2882 `MOV register1 to register2` -> `0100 WR0B : 1000 100w : 11 reg1 reg2` \<close>
          \<comment> \<open> P2882 `MOV qwordregister1 to qwordregister2` -> `0100 1R0B : 1000 1001 : 11 reg1 reg2` \<close>
            case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 \<and> x = 0 then   \<comment> \<open> rex should be `W=1` and `X=0`\<close> Some (3, Pmovq_rr dst src) 
              else if w = 0 \<and> x = 0 then
                if r = 0 \<and> b = 0 then None
                else Some (3, Pmovl_rr dst src)
              else None))) 
          else if modrm = 0b01 then
            \<comment> \<open> P2882 ` MOV: reg to memory` ->  `0100 WRXB : 1000 1001 : mod reg r/m` \<close>
            \<comment> \<open> P2882 ` MOV: qwordregister to memory64` ->  `0100 1RXB 1000 1001 : mod qwordreg r/m` \<close>
            if ireg_of_u8 src = Some R10 \<and> ireg_of_u8 dst = Some R11 then
              if w = 1 then Some (3, Pmov_mr (Addrmode (Some R11) None 0) R10 M64)
              else Some (3, Pmov_mr (Addrmode (Some R11) None 0) R10  M32)
              else None
            else None
          else if op = 0x8b then    
            if modrm = 0b01 then
            \<comment> \<open> P2882 ` MOV: memory to reg`             ->  `0100 0RXB : 1000 101w : mod reg r/m`\<close>
            \<comment> \<open> P2882 ` MOV: memory64 to qwordregister` ->  `0100 1RXB : 1000 1011 : mod qwordreg r/m`\<close>
              if ireg_of_u8 dst = Some R11 then 
                case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (  
                 Some (3, Pmov_rm src (Addrmode (Some R11) None 0)  (if w = 1 then M64 else M32)))
              else None  
            else None
          else if op = 0x63 then
            \<comment> \<open> P2883 `MOVXD dwordregister2 to qwordregister1` -> ` 0100 1R0B 0110 0011 : 11 quadreg1 dwordreg2` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 then Some (3, Pmovsq_rr src dst)
                else None)))
            else None
          else if op = 0x01 then
            \<comment> \<open> P2887 `ADD register1 to register2` -> `0100 WR0B : 0000 000w : 11 reg1 reg2` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 then Some (3, Paddq_rr dst src)
                else Some (3, Paddl_rr dst src) )))
            else None
          else if h = 0x81 then
         \<comment> \<open> P2876 `ADD immediate to register` -> `0100 000B : 1000 00sw : 11 000 reg : immediate data` \<close>
            if modrm = 0b11 \<and> reg1 = 0b000 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                let i1 = l_bin!(pc+3)  in
                let i2 = l_bin!(pc+4)  in
                let i3 = l_bin!(pc+5)  in
                let i4 = l_bin!(pc+6)  in
                let imm::u32 = u32_of_u8_list [i1,i2,i3,i4] in
                  Some (6, Paddl_ri dst imm))
            else None
          else if op = 0x29 then
            \<comment> \<open> P2891 `SUB register1 from register2` -> `0100 WR0B : 0010 100w : 11 reg1 reg2` \<close> 
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 then Some (3, Psubq_rr dst src)
                else Some (3, Psubl_rr dst src) )))
            else None
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
                if w = 1 then Some (3, Pnegq dst) 
                else Some (3, Pnegl dst))
            else if modrm = 0b11 \<and> reg1 = 0b100 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 then Some (3, Pmulq_r dst) 
              else Some (3, Pmull_r dst))
            else if modrm = 0b11 \<and> reg1 = 0b101 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 then Some (3, Pimulq_r dst) 
                else Some (3, Pimull_r dst))
            else if modrm = 0b11 \<and> reg1 = 0b110 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 then Some (3, Pdivq_r dst) 
              else Some (3, Pdivl_r dst))
            else if modrm = 0b11 \<and> reg1 = 0b111 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 then Some (3, Pidivq_r dst) 
                else Some (3, Pidivl_r dst))
            else None
          else if op = 0x09 then
          \<comment> \<open> P2884 `OR register1 to register2` -> ` 0100 WR0B : 0000 100w : 11 reg1 reg2` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 then Some (3, Porq_rr dst src) 
                else Some (3, Porl_rr dst src) )))
            else None
          else if op = 0x21 then
          \<comment> \<open> P2876 `AND register1 to register2` -> ` 0100 WR0B : 0000 100w : 11 reg1 reg2` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 then Some (3, Pandq_rr dst src)
                else Some (3, Pandl_rr dst src))) ) 
            else None
          else if op = 0x31 then
          \<comment> \<open> P2893 `XOR register1 to register2` -> ` 0100 WRXB : 0011 000w : 11 reg1 reg2` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 then Some (3, Pxorq_rr dst src)
                else Some (3, Pxorl_rr dst src))) ) 
            else None
          else if op = 0xc1 then
          \<comment> \<open> P2889 `SHL register by immediate count`      -> ` 0100 000B 1100 000w : 11 100 reg : imm8 ` \<close>
          \<comment> \<open> P2889 `SHL qwordregister by immediate count` -> ` 0100 100B 1100 000w : 11 100 reg : imm8 ` \<close>
          \<comment> \<open> P2890 `SHR register by immediate count`      -> ` 0100 000B 1100 000w : 11 101 reg : imm8 ` \<close>
          \<comment> \<open> P2890 `SHR qwordregister by immediate count` -> ` 0100 100B 1100 000w : 11 101 reg : imm8 ` \<close>
          \<comment> \<open> P2888 `SAR register by immediate count`      -> ` 0100 000B 1100 000w : 11 111 reg : imm8 ` \<close>
          \<comment> \<open> P2888 `SAR qwordregister by immediate count` -> ` 0100 100B 1100 000w : 11 111 reg : imm8 ` \<close>
            let imm = l_bin!(pc+3) in ( 
              if modrm = 0b11 \<and> reg1 = 0b100 then 
                case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                  if w = 1 then Some (4, Pshlq_ri dst imm)
                  else Some (4, Pshll_ri dst imm))
              else if modrm = 0b11 \<and> reg1 = 0b101 then 
                case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                  if w = 1 then Some (4, Pshrq_ri dst imm)
                  else Some (4, Pshrl_ri dst imm))
              else if modrm = 0b11 \<and> reg1 = 0b111 then 
                case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                  if w = 1 then Some (4, Psarq_ri dst imm)
                  else Some (4, Psarl_ri dst imm))
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
                if w = 1 then Some (3, Pshlq_r dst) 
                else Some (3, Pshll_r dst)) 
            else if modrm = 0b11 \<and> reg1 = 0b101 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 then Some (3, Pshrq_r dst) 
                else Some (3, Pshrl_r dst)) 
            else if modrm = 0b11 \<and> reg1 = 0b111 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 then Some (3, Psarq_r dst) 
                else Some (3, Psarl_r dst)) 
          else None
        else None )
)"

(*
fun x64_disassemble_aux :: "nat \<Rightarrow> nat \<Rightarrow> x64_bin \<Rightarrow> x64_asm option" where
"x64_disassemble_aux 0 _ _ = Some []" |
"x64_disassemble_aux (Suc n) pc l_bin = (
  case x64_decode pc l_bin of
  None        \<Rightarrow> None |
  Some (k, l) \<Rightarrow> (
    case x64_disassemble_aux n (pc+k) l_bin of
    None    \<Rightarrow> None |
    Some l1 \<Rightarrow> Some (l#l1))
)"

definition x64_disassemble :: "x64_bin \<Rightarrow> x64_asm option" where
"x64_disassemble l_bin = x64_disassemble_aux (length l_bin) 0 l_bin" *)

(*
definition x64_disassemble :: "x64_bin \<Rightarrow> x64_asm option" where
"x64_disassemble [] = Some []" |  
"x64_disassemble (h#t) = (
  
  if h = 0x90 then \<comment> \<open> P2884 `NOP – No Operation` -> `1001 0000` \<close>
    case x64_disassemble t of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pnop # l)
  else 
    if h = 0x66 then  \<comment> \<open> 16-bit mode \<close>
      case t of [] \<Rightarrow> None | h1#t1 \<Rightarrow>(
      if unsigned_bitfield_extract_u8 4 4 h1 \<noteq> 0b0100 then \<comment> \<open> h1 is not rex \<close>
        case t1 of [] \<Rightarrow> None | reg#t2 \<Rightarrow>(
          let modrm = unsigned_bitfield_extract_u8 6 2 reg in
          let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
          let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
          let src   = bitfield_insert_u8 3 1 reg1 0 in
          let dst   = bitfield_insert_u8 3 1 reg2 0 in
          if h1 = 0xc1 then 
           \<comment> \<open> P2887 `ROL : register by immediate count` -> `0x66 1100 000w : 11 000 reg : imm8` \<close>
            case t2 of [] \<Rightarrow> None | imm#t3 \<Rightarrow> (
            if modrm = 0b11 \<and> src = 0b000 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                case x64_disassemble t2 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Prolw_ri dst imm # l))
            else None )
          else  None)
      else  \<comment> \<open> h1 is rex \<close>
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
          if op = 0xc1 then 
           \<comment> \<open> P2887 `ROL : register by immediate count` -> `0x66 1100 000w : 11 000 reg : imm8` \<close>
            case t2 of [] \<Rightarrow> None | imm#t3 \<Rightarrow> (
            if modrm = 0b11 \<and> src = 0b000 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                case x64_disassemble t2 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Prolw_ri dst imm # l))
             else None )
          else if op = 0x89 then 
          \<comment> \<open> P2882 ` MOV: reg to memory`  ->  `66H 0100 0RXB : 1000 1001 : mod reg r/m `\<close>
            if modrm = 0b01 then
              if ireg_of_u8 src = Some R10 \<and>
                 ireg_of_u8 dst = Some R11 then
                  case x64_disassemble t2 of None \<Rightarrow> None | Some l \<Rightarrow>
                    Some (Pmov_rm (Addrmode (Some R11) None 0) R10 M16 # l)
               else None
             else None
           else None))
  else
    if unsigned_bitfield_extract_u8 4 4 h \<noteq> 0b0100 then  \<comment> \<open> h is not rex  \<close>
     \<comment> \<open> 8/32-bit mode \<close>
        if h = 0x0f then \<comment> \<open> 8/32-bit mode with opcode escape sequence 0x0f \<close>
        \<comment> \<open> P2885 `RDTSC – Read Time-Stamp Counter` -> `0000 1111 : 0011 0001` \<close>
          case t of [] \<Rightarrow> None | h1#t1 \<Rightarrow>(
            if h1 = 0x31 then 
              case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Prdtsc # l)
            else if h1 = 0x45 then
              None
            else
              None)
        else 
        \<comment> \<open> 8/32bit mode without rex and opcode escape sequence \<close>
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
             else  None
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
     \<comment> \<open> 64-bit or 32-bit instructions accessing extended registers  (R8-R15) \<close>
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
          if h = 0x88 then
          \<comment> \<open> P2882 ` MOV: reg to memory`  ->  `0100 0RXB : 1000 1000 : mod reg r/m `\<close>
            if modrm = 0b01 then
              if ireg_of_u8 src = Some R10 \<and>
                 ireg_of_u8 dst = Some R11 then
                  case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow>
                    Some (Pmov_rm (Addrmode (Some R11) None 0) R10 M8 # l)
               else None
             else None
          else
          if op = 0x89 then
            if modrm = 0b11 then (
          \<comment> \<open> P2882 `MOV register1 to register2` -> `0100 WR0B : 1000 100w : 11 reg1 reg2` \<close>
          \<comment> \<open> P2882 `MOV qwordregister1 to qwordregister2` -> `0100 1R0B : 1000 1001 : 11 reg1 reg2` \<close>
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then   \<comment> \<open> rex should be `W=1` and `X=0`\<close>
                  case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pmovq_rr dst src # l) 
                else if w = 0 \<and> x = 0 then 
                  case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pmovl_rr dst src # l)
                else None))) 
            else
              if modrm = 0b01 then
          \<comment> \<open> P2882 ` MOV: reg to memory` ->  `0100 WRXB : 1000 1001 : mod reg r/m` \<close>
          \<comment> \<open> P2882 ` MOV: qwordregister to memory64` ->  `0100 1RXB 1000 1001 : mod qwordreg r/m` \<close>
                if ireg_of_u8 src = Some R10 \<and>
                   ireg_of_u8 dst = Some R11 then
                    if w = 1 then 
                      case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow>
                        Some (Pmov_rm (Addrmode (Some R11) None 0) R10 M64 # l)
                    else case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow>
                        Some (Pmov_rm (Addrmode (Some R11) None 0) R10 M32 # l)
                 else None
             else None
          else if op = 0x8b then
              if modrm = 0b01 then
          \<comment> \<open> P2882 ` MOV: memory to reg`             ->  `0100 0RXB : 1000 101w : mod reg r/m`\<close>
          \<comment> \<open> P2882 ` MOV: memory64 to qwordregister` ->  `0100 1RXB : 1000 1011 : mod qwordreg r/m`\<close>
                if ireg_of_u8 dst = Some R11 then 
                  case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
                    if w = 1 then 
                      case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow>
                        Some (Pmov_mr src (Addrmode (Some R11) None 0)  M64 # l)
                    else case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow>
                        Some (Pmov_mr src (Addrmode (Some R11) None 0)  M32 # l))
                    else None
             else None
          else if op = 0x63 then
          \<comment> \<open> P2883 `MOVXD dwordregister2 to qwordregister1` -> ` 0100 1R0B 0110 0011 : 11 quadreg1 dwordreg2` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 then
                  case x64_disassemble t1 of None \<Rightarrow> None | Some l \<Rightarrow> Some (Pmovq_rr src dst # l)
                else
                  None)))
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
)" *)

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