section \<open> x64 Semantics \<close>

theory x64Semantics
imports
  Main
  rBPFCommType Val
begin

text \<open> define our x64 semantics in Isabelle/HOL, following the style of CompCert x64 semantics: https://github.com/AbsInt/CompCert/blob/master/x86/Asm.v  \<close>


subsection  \<open> x64 Syntax \<close>

datatype ireg = RAX | RBX | RAC | RDX | RSI | RDI | RBP | RSP | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15

text \<open> skip float registers, as Solana rBPF doesn't deal with float \<close>

datatype crbit = ZF | CF | PF | SF | OF

datatype preg = PC | IR ireg | CR crbit | RA

abbreviation "RIP \<equiv> PC"  \<comment> \<open> the RIP register in x86-64 (x64) architecture is the equivalent of the program counter (PC) in many other architectures.  \<close>
  
abbreviation "SP \<equiv> RSP"

type_synonym label = nat

datatype addrmode =
  Addrmode "ireg option" "(ireg * int) option" int

datatype testcond =
    Cond_e | Cond_ne
  | Cond_b | Cond_be | Cond_ae | Cond_a
  | Cond_l | Cond_le | Cond_ge | Cond_g
  | Cond_p | Cond_np

(** Instructions.  IA32 instructions accept many combinations of
  registers, memory references and immediate constants as arguments.
  Here, we list only the combinations that we actually use.

  Naming conventions for types:
- [b]: 8 bits
- [w]: 16 bits ("word")
- [l]: 32 bits ("longword")
- [q]: 64 bits ("quadword")
- [d] or [sd]: FP double precision (64 bits)
- [s] or [ss]: FP single precision (32 bits)

  Naming conventions for operands:
- [r]: integer register operand
- [f]: XMM register operand
- [m]: memory operand
- [i]: immediate integer operand
- [s]: immediate symbol operand
- [l]: immediate label operand
- [cl]: the [CL] register

  For two-operand instructions, the first suffix describes the result
  (and first argument), the second suffix describes the second argument.
*)

datatype instruction =
  (** Moves *)
    Pmov_rr ireg ireg       (**r [mov] (integer) *)
  | Pmovl_ri ireg u32
  | Pmovq_ri ireg u64
  | Pmovl_rm ireg addrmode
  | Pmovq_rm ireg addrmode
  | Pmovl_mr addrmode ireg
  | Pmovq_mr addrmode ireg
  | Pfldl_m addrmode               (**r [fld] double precision *)
  | Pfstpl_m addrmode              (**r [fstp] double precision *)
  | Pflds_m addrmode               (**r [fld] simple precision *)
  | Pfstps_m addrmode              (**r [fstp] simple precision *)
  (** Moves with conversion *)
  | Pmovb_mr addrmode ireg   (**r [mov] (8-bit int) *)
  | Pmovw_mr addrmode ireg   (**r [mov] (16-bit int) *)
  | Pmovzb_rr ireg ireg     (**r [movzb] (8-bit zero-extension) *)
  | Pmovzb_rm ireg addrmode
  | Pmovsb_rr ireg ireg     (**r [movsb] (8-bit sign-extension) *)
  | Pmovsb_rm ireg addrmode
  | Pmovzw_rr ireg ireg     (**r [movzw] (16-bit zero-extension) *)
  | Pmovzw_rm ireg addrmode
  | Pmovsw_rr ireg ireg     (**r [movsw] (16-bit sign-extension) *)
  | Pmovsw_rm ireg addrmode
  | Pmovzl_rr ireg ireg     (**r [movzl] (32-bit zero-extension) *)
  | Pmovsl_rr ireg ireg     (**r [movsl] (32-bit sign-extension) *)
  | Pmovls_rr ireg                (** 64 to 32 bit conversion (pseudo) *)
  (** Integer arithmetic *)
  | Pleal ireg addrmode
  | Pleaq ireg addrmode
  | Pnegl ireg
  | Pnegq ireg
  | Paddl_ri ireg u32
  | Paddq_ri ireg u64 (*
  | Psubl_rr ireg ireg
  | Psubq_rr ireg ireg
  | Pimull_rr ireg ireg
  | Pimulq_rr ireg ireg
  | Pimull_ri ireg u32
  | Pimulq_ri ireg u64
  | Pimull_r ireg
  | Pimulq_r ireg
  | Pmull_r ireg
  | Pmulq_r ireg
  | Pcltd
  | Pcqto
  | Pdivl ireg
  | Pdivq ireg
  | Pidivl ireg
  | Pidivq ireg
  | Pandl_rr ireg ireg
  | Pandq_rr ireg ireg
  | Pandl_ri ireg u32
  | Pandq_ri ireg u64
  | Porl_rr ireg ireg
  | Porq_rr ireg ireg
  | Porl_ri ireg u32
  | Porq_ri ireg u64
  | Pxorl_r ireg                  (**r [xor] with self = set to zero *)
  | Pxorq_r ireg
  | Pxorl_rr ireg ireg
  | Pxorq_rr ireg ireg
  | Pxorl_ri ireg u32
  | Pxorq_ri ireg u64
  | Pnotl ireg
  | Pnotq ireg
  | Psall_rcl ireg
  | Psalq_rcl ireg
  | Psall_ri ireg u32
  | Psalq_ri ireg u32
  | Pshrl_rcl ireg
  | Pshrq_rcl ireg
  | Pshrl_ri ireg u32
  | Pshrq_ri ireg u32
  | Psarl_rcl ireg
  | Psarq_rcl ireg
  | Psarl_ri ireg u32
  | Psarq_ri ireg u32
  | Pshld_ri ireg ireg u32
  | Prorl_ri ireg u32
  | Prorq_ri ireg u32
  | Pcmpl_rr ireg ireg
  | Pcmpq_rr ireg ireg
  | Pcmpl_ri ireg u32
  | Pcmpq_ri ireg u64
  | Ptestl_rr ireg ireg
  | Ptestq_rr ireg ireg
  | Ptestl_ri ireg u32
  | Ptestq_ri ireg u64
  | Pcmov testcond ireg ireg
  | Psetcc testcond ireg
  (** Branches and calls *)
  | Pjmp_l label
  | Pjcc testcond label
  | Pjcc2 testcond testcond label   (**r pseudo *)
  | Pjmptbl ireg "label list" (**r pseudo *)
  | Pret
  (** Saving and restoring registers *)
  | Pmov_rm_a ireg addrmode  (**r like [Pmov_rm], using [Many64] chunk *)
  | Pmov_mr_a addrmode ireg  (**r like [Pmov_mr], using [Many64] chunk *) *)


type_synonym regset = "preg \<Rightarrow> val"
type_synonym mem = "(u64, val) map"

syntax "_pregmap_set" :: "'a => 'b => 'c => 'a" ("_ # _ <- _" [1000, 1000, 1000] 1)

(* Define the translation for the notation *)
translations
  "_pregmap_set a b c" => "(a(b := c))"

(*
abbreviation bit_left_shift ::
  "regset \<Rightarrow> preg \<Rightarrow> val \<Rightarrow> regset" (infix " _ # _ <- _ " 50)
where "a # b <- c \<equiv> (a(b := c))" *)

fun undef_regs :: "preg list \<Rightarrow> regset \<Rightarrow> regset" where
"undef_regs [] rs = rs" |
"undef_regs (r#l') rs = undef_regs l' (rs#r <- Vundef)"

(**r igore it, as currently we only consider 64 architecture *)
definition eval_addrmode32 :: "addrmode \<Rightarrow> regset \<Rightarrow> val" where
"eval_addrmode32 a rs = (
  case a of Addrmode base ofs const \<Rightarrow>
    Val.add (case base of None \<Rightarrow> (Vint 0) | Some r \<Rightarrow> (rs (IR r)) )
      (Val.add (
        case ofs of None \<Rightarrow> (Vint 0) | Some (r, sc) \<Rightarrow>
          if sc = 1 then (rs (IR r)) else Val.mul (rs (IR r)) (Vint (of_int sc))
        )
        (Vint (of_int const))
      )
)"

definition eval_addrmode64 :: "addrmode \<Rightarrow> regset \<Rightarrow> val" where
"eval_addrmode64 a rs = (
  case a of Addrmode base ofs const \<Rightarrow>
    Val.addl (case base of None \<Rightarrow> (Vlong 0) | Some r \<Rightarrow> (rs (IR r)) )
      (Val.addl (
        case ofs of None \<Rightarrow> (Vlong 0) | Some (r, sc) \<Rightarrow>
          if sc = 1 then (rs (IR r)) else Val.mull (rs (IR r)) (Vlong (of_int sc))
        )
        (Vlong (of_int const))
      )
)"

definition compare_ints :: "val \<Rightarrow> val \<Rightarrow> regset \<Rightarrow> regset" where
"compare_ints x y rs = (((((
  rs#(CR ZF) <- (Val.cmpu Ceq x y))
    #(CR CF) <- (Val.cmpu Clt x y))
    #(CR SF) <- (Val.negative (Val.sub x y)))
    #(CR OF) <- (Val.sub_overflow x y))
    #(CR PF) <- Vundef)"

definition compare_longs :: "val \<Rightarrow> val \<Rightarrow> regset \<Rightarrow> regset" where
"compare_longs x y rs = (((((
  rs#(CR ZF) <- (Val.cmplu Ceq x y))
    #(CR CF) <- (Val.cmplu Clt x y))
    #(CR SF) <- (Val.negativel (Val.sub x y)))
    #(CR OF) <- (Val.subl_overflow x y))
    #(CR PF) <- Vundef)"

definition eval_testcond :: "testcond \<Rightarrow> regset \<Rightarrow> bool option" where
"eval_testcond c rs = (
  case c of
  Cond_e  \<Rightarrow> (case rs (CR ZF) of Vint n \<Rightarrow> Some (n = 1) | _ \<Rightarrow> None) |      
  Cond_ne \<Rightarrow> (case rs (CR ZF) of Vint n \<Rightarrow> Some (n = 0) | _ \<Rightarrow> None) |
  Cond_b  \<Rightarrow> (case rs (CR CF) of Vint n \<Rightarrow> Some (n = 1) | _ \<Rightarrow> None) |      
  Cond_be \<Rightarrow> (case rs (CR CF) of Vint c \<Rightarrow> (
                case rs (CR ZF) of  Vint z \<Rightarrow> Some (c = 1 \<or> z = 1) |
                                    _ \<Rightarrow> None) | _ \<Rightarrow> None) |
  Cond_ae \<Rightarrow> (case rs (CR CF) of Vint n \<Rightarrow> Some (n = 0) | _ \<Rightarrow> None) |      
  Cond_a  \<Rightarrow> (case rs (CR CF) of Vint c \<Rightarrow> (
                case rs (CR ZF) of  Vint z \<Rightarrow> Some (c = 0 \<or> z = 0) |
                                    _ \<Rightarrow> None) | _ \<Rightarrow> None) |
  Cond_l  \<Rightarrow> (case rs (CR OF) of Vint n \<Rightarrow> (
                case rs (CR SF) of  Vint s \<Rightarrow> Some ((xor n s) = 1) |
                                    _ \<Rightarrow> None) | _ \<Rightarrow> None) |
  Cond_le \<Rightarrow> (case rs (CR OF) of Vint n \<Rightarrow> (
                case rs (CR SF) of  Vint s \<Rightarrow> (
                  case rs (CR ZF) of Vint z \<Rightarrow> Some ((xor n s) = 1 \<or> z = 1) | _ \<Rightarrow> None) |
                                    _ \<Rightarrow> None) | _ \<Rightarrow> None) |
  Cond_ge \<Rightarrow> (case rs (CR OF) of Vint n \<Rightarrow> (
                case rs (CR SF) of  Vint s \<Rightarrow> Some ((xor n s) = 0) |
                                    _ \<Rightarrow> None) | _ \<Rightarrow> None) |
  Cond_g  \<Rightarrow> (case rs (CR OF) of Vint n \<Rightarrow> (
                case rs (CR SF) of  Vint s \<Rightarrow> (
                  case rs (CR ZF) of Vint z \<Rightarrow> Some ((xor n s) = 0 \<and> z = 0) | _ \<Rightarrow> None) |
                                    _ \<Rightarrow> None) | _ \<Rightarrow> None) |
  Cond_p  \<Rightarrow> (case rs (CR PF) of Vint n \<Rightarrow> Some (n = 1) | _ \<Rightarrow> None) |
  Cond_np \<Rightarrow> (case rs (CR PF) of Vint n \<Rightarrow> Some (n = 0) | _ \<Rightarrow> None)
)"

datatype outcom = Next regset mem | Stuck

(**r


*)

end
