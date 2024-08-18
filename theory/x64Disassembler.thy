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
    \<comment> \<open> R1 [opcode] \<close>
    if h = 0x90 then 
      \<comment> \<open> P2884 `NOP – No Operation` -> `1001 0000` \<close> 
      Some (1, Pnop)
    \<comment> \<open> R7 legacy \<close>
    else if h = 0x66 then  \<comment> \<open> 16-bit mode \<close>
      let h1 = l_bin!(pc+1) in
        if unsigned_bitfield_extract_u8 4 4 h1 \<noteq> 0b0100 then  
          \<comment> \<open> R7.1 [legacy + opcode + modrm + imm] \<close>
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
          \<comment> \<open> R7.2 [legacy + opcode + modrm + displacement] \<close>
            else if h1 = 0x89 then 
              \<comment> \<open> P2882 ` MOV: reg to memory`  ->  `66H 0100 0RXB : 1000 1001 : mod reg r/m `\<close>
                if modrm = 0b01  then
                  let (imm::int) = uint (l_bin!(pc+3)) in  \<comment> \<open> displacement8 \<close>
                    if (imm \<le> 127) \<and> (imm \<ge> -128)then
                      case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
                      case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                          Some (4, Pmov_mr (Addrmode (Some dst) None imm) src  M16)))
                    else None
                else None
              else None
        else  
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
              \<comment> \<open> R7.3 [legacy + rex + opcode + modrm + imm] \<close>
              if op = 0xc1 then 
              \<comment> \<open> P2887 `ROL : register by immediate count` -> `0x66 1100 000w : 11 000 reg : imm8` \<close>
                let imm = l_bin!(pc+4) in
                  if modrm = 0b11 \<and> src = 0b000 then
                    case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                      if w = 0 \<and> b = 0 then
                        Some (5, Prolw_ri dst imm)
                      else None)
                  else None
              \<comment> \<open> R7.4 [legacy + rex + opcode + modrm + displacement\<close>
              else if op = 0x89 then 
              \<comment> \<open> P2882 ` MOV: reg to memory`  ->  `66H 0100 0RXB : 1000 1001 : mod reg r/m `\<close>
                if modrm = 0b01  then
                  let (imm::int) = uint (l_bin!(pc+4)) in  \<comment> \<open> displacement8 \<close>
                    if (imm \<le> 127) \<and> (imm \<ge> -128)then
                      case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
                      case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                        if w = 0 \<and> x = 0 then
                          Some (5, Pmov_mr (Addrmode (Some dst) None imm) src  M16)
                        else None))
                    else None
                else None
              else None
  else if h = 0x0f then \<comment> \<open> R8 escape \<close>
    let h1 = l_bin!(pc+1) in
      \<comment> \<open> R8.1 [escape + opcode] \<close>         
      if h1 = 0x31 then 
        Some (2, Prdtsc)
      \<comment> \<open> R8.2 [escape + opcode + modrm] \<close>
      else if h1 = 0x45 then
        None
      else None  
  else if unsigned_bitfield_extract_u8 4 4 h \<noteq> 0b0100 then  \<comment> \<open> h is not rex  \<close>
      \<comment> \<open> R1 [opcode] \<close>
      \<comment> \<open> P2885 `PUSH: qwordregister (alternate encoding)`   -> ` 0100 W00BS : 0101 0 reg64` \<close>
      if unsigned_bitfield_extract_u8 5 5 h = 0b01010 then
        let reg2 = unsigned_bitfield_extract_u8 0 3 h in
        let dst  = bitfield_insert_u8 3 1 reg2 0 in
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (1, Ppushl_r dst))
      \<comment> \<open> P2885 `POP: qwordregister (alternate encoding)`   -> ` 0100 W00B : 0101 1 reg64 ` \<close>
      else if unsigned_bitfield_extract_u8 5 5 h = 0b01011 then
        let reg2 = unsigned_bitfield_extract_u8 0 3 h in
        let dst  = bitfield_insert_u8 3 1 reg2 0 in
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (1, Ppopl dst))
      \<comment> \<open> R4 [opcode + displacement] \<close>
      else if h = 0xe8 then
      \<comment> \<open> P2878 `CALL: direct`   -> `1110 1000 : displacement32` \<close>
          let i1 = l_bin!(pc+1)  in
          let i2 = l_bin!(pc+2)  in
          let i3 = l_bin!(pc+3)  in
          let i4 = l_bin!(pc+4)  in
            case u32_of_u8_list [i1,i2,i3,i4] of None \<Rightarrow> None |
              Some d \<Rightarrow> ( Some (5, Pcall_i (scast d))) 
      else
        let reg = l_bin!(pc+1) in
        let modrm = unsigned_bitfield_extract_u8 6 2 reg in
        let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
        let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
        let src   = bitfield_insert_u8 3 1 reg1 0 in
        let dst   = bitfield_insert_u8 3 1 reg2 0 in
          \<comment> \<open> R2 [opcode + modrm] \<close>
          if h = 0x89 then 
          \<comment> \<open> P2887 `MOV register1 to register2` -> `0100 0R0B : 1000 1001 : 11 reg1 reg2` \<close>
            if modrm = 0b11 then
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                Some (2, Pmovl_rr dst src)))
            else None
          else if h = 0x01 then
          \<comment> \<open> P2876 `ADD register1 to register2` -> `0100 0R0B : 0000 000w : 11 reg1 reg2` \<close>
            if modrm = 0b11 then
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                Some (2, Paddl_rr dst src))) 
            else None
          else if h = 0xff then
          \<comment> \<open> P2878 `CALL: register indirect`   -> `0100 W00Bw 1111 1111 : 11 010 reg ` \<close>
            if modrm = 0b11 \<and> reg1 = 0b010 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                Some (2, Pcall_r dst)) 
            else None
          \<comment> \<open> R3 [opcode + modrm + imm] \<close>
          \<comment> \<open> P2882 `MOV immediate to register` -> `0100 000B : 1100 011w : 11 000 reg : imm` \<close>
          else if h = 0xc7 then
            let i1 = l_bin!(pc+2)  in
            let i2 = l_bin!(pc+3)  in
            let i3 = l_bin!(pc+4)  in
            let i4 = l_bin!(pc+5)  in
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
            case u32_of_u8_list [i1, i2, i3, i4] of None \<Rightarrow> None |
                Some imm \<Rightarrow> 
                  if modrm = 0b11 \<and> reg1 = 0b000 then
                    Some (6, Pmovl_ri dst imm)
              else None)
          \<comment> \<open> P2876 `ADD immediate to register` -> `0100 000B : 1000 00sw : 11 000 reg : immediate data` \<close>
          else if h = 0x81 then
            if modrm = 0b11 \<and> reg1 = 0b000 then
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                let i1 = l_bin!(pc+2)  in
                let i2 = l_bin!(pc+3)  in
                let i3 = l_bin!(pc+4)  in
                let i4 = l_bin!(pc+5)  in
                  case u32_of_u8_list [i1,i2,i3,i4] of None \<Rightarrow> None |
                    Some imm \<Rightarrow> Some (6, Paddl_ri dst imm))
            else None
          \<comment> \<open> R5 [opcode + modrm + displacement] \<close>
          \<comment> \<open> P2882 ` MOV: memory to reg`   ->  `0100 0RXB : 1000 101w : mod reg r/m`\<close>
          else if h = 0x88 then
            if modrm = 0b01  then
              let (imm::int) = uint (l_bin!(pc+2)) in  \<comment> \<open> displacement8 \<close>
                if (imm \<le> 127) \<and> (imm \<ge> -128)then
                  case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
                  case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                    Some (3, Pmov_mr (Addrmode (Some dst) None imm) src  M8)))
                else None
            else None
          else if h = 0x89 then
            if modrm = 0b01 then
              \<comment> \<open> P2882 ` MOV: reg to memory` ->  `0100 WRXB : 1000 1001 : mod reg r/m` \<close>
              \<comment> \<open> P2882 ` MOV: qwordregister to memory64` ->  `0100 1RXB 1000 1001 : mod qwordreg r/m` \<close>
              let (imm::int) = uint (l_bin!(pc+2)) in  \<comment> \<open> displacement8 \<close>
                if (imm \<le> 127) \<and> (imm \<ge> -128) then
                  case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
                  case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                      Some (3, Pmov_mr (Addrmode (Some dst) None 0) src M32)))
                else None
            else None
          else if h = 0x8b then 
            if modrm = 0b01 then
              let (imm::int) = uint (l_bin!(pc+2)) in  \<comment> \<open> displacement8 \<close>
                if (imm \<le> 127) \<and> (imm \<ge> -128)then
                  case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
                  case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                    Some (3, Pmov_rm src (Addrmode (Some dst) None imm)  M32)))
                else None
            else None
          else None
    else if unsigned_bitfield_extract_u8 0 4 h = 0 then   \<comment> \<open> h is rex, the low 4-bit must not 0  \<close> 
      None
    else  \<comment> \<open> h is rex  \<close> 
      let w = unsigned_bitfield_extract_u8 3 1 h in
      let r = unsigned_bitfield_extract_u8 2 1 h in
      let x = unsigned_bitfield_extract_u8 1 1 h in
      let b = unsigned_bitfield_extract_u8 0 1 h in
      let op = l_bin!(pc+1) in 
      \<comment> \<open> R6.1 [rex + opcode] \<close>
      \<comment> \<open> P2885 `PUSH: qwordregister (alternate encoding)`   -> ` 0100 W00BS : 0101 0 reg64` \<close>
      if unsigned_bitfield_extract_u8 5 5 op = 0b01010 then
        let reg2 = unsigned_bitfield_extract_u8 0 3 op in
        let dst  = bitfield_insert_u8 3 1 reg2 b in
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          if w = 0 \<and> r = 0 \<and> x = 0 then
            Some (2, Ppushl_r dst)
          else None)
      \<comment> \<open> P2885 `POP: qwordregister (alternate encoding)`   -> ` 0100 W00B : 0101 1 reg64 ` \<close>
      else if unsigned_bitfield_extract_u8 5 5 op = 0b01011 then
        let reg2 = unsigned_bitfield_extract_u8 0 3 op in
        let dst  = bitfield_insert_u8 3 1 reg2 b in
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          if w = 0 \<and> r = 0 \<and> x = 0 then
            Some (2, Ppopl dst)
          else None)
      \<comment> \<open> R6.2 [rex + opcode + imm] \<close> 
      \<comment> \<open> P2882 `MOV immediate64 to qwordregister (alternate encoding)` -> `0100 100B 1011 1reg : imm64` \<close>
      else if unsigned_bitfield_extract_u8 5 5 op = 0b10111 then
        let reg2 = unsigned_bitfield_extract_u8 0 3 op in
        let dst  = bitfield_insert_u8 3 1 reg2 b in
        let i1 = l_bin!(pc+2)  in
        let i2 = l_bin!(pc+3)  in
        let i3 = l_bin!(pc+4)  in
        let i4 = l_bin!(pc+5)  in
        let i5 = l_bin!(pc+6)  in
        let i6 = l_bin!(pc+7)  in
        let i7 = l_bin!(pc+8)  in
        let i8 = l_bin!(pc+9)  in
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
        case u64_of_u8_list [i1, i2, i3, i4, i5, i6, i7, i8] of None \<Rightarrow> None |
            Some imm \<Rightarrow> 
              if w = 1 \<and> r = 0 \<and> x = 0 then
                Some (10, Pmovq_ri dst imm)
          else None)
      else if op = 0x68 then 
        let i1 = l_bin!(pc+2)  in
        let i2 = l_bin!(pc+3)  in
        let i3 = l_bin!(pc+4)  in
        let i4 = l_bin!(pc+5)  in
          case u32_of_u8_list [i1, i2, i3, i4] of None \<Rightarrow> None |
            Some imm \<Rightarrow> 
              if w = 1 \<and> r = 0 \<and> x = 0 \<and> b = 0 then
                Some (6, Ppushl_i imm)
              else None
      else
        let reg = l_bin!(pc+2) in
        let modrm = unsigned_bitfield_extract_u8 6 2 reg in
        let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
        let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
        let src   = bitfield_insert_u8 3 1 reg1 r in
        let dst   = bitfield_insert_u8 3 1 reg2 b in
          \<comment> \<open> R8.4 [rex + escape + opcode + modrm] \<close>
          if h = 0x0f then 
            None
          \<comment> \<open> R6.3 [rex + opcode + modrm] \<close>
          else if op = 0x89 then
            if modrm = 0b11 then (
            \<comment> \<open> P2882 `MOV register1 to register2` -> `0100 WR0B : 1000 100w : 11 reg1 reg2` \<close>
            \<comment> \<open> P2882 `MOV qwordregister1 to qwordregister2` -> `0100 1R0B : 1000 1001 : 11 reg1 reg2` \<close>
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then   \<comment> \<open> rex should be `W=1` and `X=0`\<close> 
                  Some (3, Pmovq_rr dst src) 
                else if w = 0 \<and> x = 0 then
                  if r = 0 \<and> b = 0 then None
                  else 
                    Some (3, Pmovl_rr dst src)
                else None))) 
            \<comment> \<open> R6.5 [rex + opcode + modrm + displacement] \<close>
            else if modrm = 0b01 then
              \<comment> \<open> P2882 ` MOV: reg to memory` ->  `0100 WRXB : 1000 1001 : mod reg r/m` \<close>
              \<comment> \<open> P2882 ` MOV: qwordregister to memory64` ->  `0100 1RXB 1000 1001 : mod qwordreg r/m` \<close>
              let (imm::int) = uint (l_bin!(pc+3)) in  \<comment> \<open> displacement8 \<close>
                if (imm \<le> 127) \<and> (imm \<ge> -128) then
                  case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
                  case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                    if w = 1 \<and> x = 0 then
                      Some (4, Pmov_mr (Addrmode (Some dst) None 0) src M64)
                    else if w = 0 \<and> x = 0 then
                      Some (4, Pmov_mr (Addrmode (Some dst) None 0) src M32)
                    else None))
                else None
            else None
          else if op = 0x87 then
          \<comment> \<open> P2893 `XCHG: register1 with register2 `   -> ` 0100 1R0B 1000 011w : 11 reg1 reg2 ` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then Some (3, Pxchgq_rr src dst)
                else None)))
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
          else if op = 0xd3 then
          \<comment> \<open> P2889 `SHL register by CL`              -> ` 0100 000B 1100 000w : 11 100 reg ` \<close>
          \<comment> \<open> P2889 `SHL qwordregister by CL`         -> ` 0100 100B 1100 000w : 11 100 reg ` \<close>
          \<comment> \<open> P2890 `SHR register by CL`              -> ` 0100 000B 1100 000w : 11 101 reg ` \<close>
          \<comment> \<open> P2890 `SHR qwrodregister by CL`         -> ` 0100 100B 1100 000w : 11 101 reg ` \<close>
          \<comment> \<open> P2888 `SAR register by CL`              -> ` 0100 000B 1100 000w : 11 111 reg ` \<close>
          \<comment> \<open> P2888 `SAR qwordregister by CL`         -> ` 0100 100B 1100 000w : 11 111 reg ` \<close>
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
        else if op = 0xff then
        \<comment> \<open> P2878 `CALL: register indirect`   -> `0100 W00Bw 1111 1111 : 11 010 reg ` \<close>
          if modrm = 0b11 \<and> reg1 = 0b010 then
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              Some (2, Pcall_r dst)) 
          else None
        \<comment> \<open> R6.4 [rex + opcode + modrm + imm] \<close>
        \<comment> \<open> P2882 `MOV immediate to register` -> `0100 000B : 1100 011w : 11 000 reg : imm` \<close>
        else if op = 0xc7 then
          let i1 = l_bin!(pc+3)  in
          let i2 = l_bin!(pc+4)  in
          let i3 = l_bin!(pc+5)  in
          let i4 = l_bin!(pc+6)  in
          case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          case u32_of_u8_list [i1, i2, i3, i4] of None \<Rightarrow> None |
              Some imm \<Rightarrow> 
                if  modrm = 0b11 \<and> reg1 = 0b000 \<and> w = 0 \<and> r = 0 \<and> x = 0 then
                  Some (7, Pmovl_ri dst imm)
            else None)
        \<comment> \<open> P2876 `ADD immediate to register` -> `0100 000B : 1000 00sw : 11 000 reg : immediate data` \<close>
        else if op = 0x81 then
          if modrm = 0b11 \<and> reg1 = 0b000 then
            case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              let i1 = l_bin!(pc+3)  in
              let i2 = l_bin!(pc+4)  in
              let i3 = l_bin!(pc+5)  in
              let i4 = l_bin!(pc+6)  in
                case u32_of_u8_list [i1,i2,i3,i4] of None \<Rightarrow> None |
                  Some imm \<Rightarrow> Some (7, Paddl_ri dst imm))
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
    \<comment> \<open> R6.5 [rex + opcode + modrm + displacement] \<close>
        else if h = 0x88 then
          \<comment> \<open> P2882 ` MOV: reg to memory`  ->  `0100 0RXB : 1000 1000 : mod reg r/m `\<close>
          if modrm = 0b01 \<and> x = 0 \<and> w = 0 then
            let (imm::int) = uint (l_bin!(pc+3)) in  \<comment> \<open> displacement8 \<close>
              if (imm \<le> 127) \<and> (imm \<ge> -128)then
                case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
                case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                Some (4, Pmov_mr (Addrmode (Some dst) None imm) src  M8)))
              else None
          else None
        else if op = 0x8b then    
          if modrm = 0b01 \<and> x = 0 then
          \<comment> \<open> P2882 ` MOV: memory to reg`             ->  `0100 0RXB : 1000 101w : mod reg r/m`\<close>
          \<comment> \<open> P2882 ` MOV: memory64 to qwordregister` ->  `0100 1RXB : 1000 1011 : mod qwordreg r/m`\<close>
            let (imm::int) = uint (l_bin!(pc+3)) in  \<comment> \<open> displacement8 \<close>
              if (imm \<le> 127) \<and> (imm \<ge> -128)then
                case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
                case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> ( 
                  Some (4, Pmov_rm src (Addrmode (Some dst) None imm)  (if w = 1 then M64 else M32))))  
              else None
          else None
        else None 
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