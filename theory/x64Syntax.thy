section \<open> x64 Syntax \<close>

theory x64Syntax
imports
  Main
  rBPFCommType Mem
begin
  
subsection  \<open> x64 Syntax \<close>

datatype ireg = RAX | RBX | RCX | RDX | RSI | RDI | RBP | RSP | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15

(*
fun u8_of_ireg ::"ireg \<Rightarrow> u8" where
"u8_of_ireg RAX = 0" |
"u8_of_ireg RBX = 1" |
"u8_of_ireg RCX = 2" |
"u8_of_ireg RDX = 3" |
"u8_of_ireg RSI = 4" |
"u8_of_ireg RDI = 5" |
"u8_of_ireg RBP = 6" |
"u8_of_ireg RSP = 7" |
"u8_of_ireg R8  = 8" |
"u8_of_ireg R9  = 9" |
"u8_of_ireg R10 = 10" |
"u8_of_ireg R11 = 11" |
"u8_of_ireg R12 = 12" |
"u8_of_ireg R13 = 13" |
"u8_of_ireg R14 = 14" |
"u8_of_ireg R15 = 15" *)

text \<open> TODO: Solana rBPF uses the following mapping, very weird.
I don't understand, see: https://github.com/solana-labs/rbpf/blob/main/src/x86.rs#L16 
But this mapping doesn't effect x64 semantics, only binary code
\<close>

fun u8_of_ireg ::"ireg \<Rightarrow> u8" where
"u8_of_ireg RAX = 0" |
"u8_of_ireg RCX = 1" |
"u8_of_ireg RDX = 2" |
"u8_of_ireg RBX = 3" |
"u8_of_ireg RSP = 4" | 
"u8_of_ireg RBP = 5" |
"u8_of_ireg RSI = 6" |
"u8_of_ireg RDI = 7" |
"u8_of_ireg R8  = 8" |        
"u8_of_ireg R9  = 9" |
"u8_of_ireg R10 = 10" |
"u8_of_ireg R11 = 11" |
"u8_of_ireg R12 = 12" |
"u8_of_ireg R13 = 13" |
"u8_of_ireg R14 = 14" |
"u8_of_ireg R15 = 15"

definition ireg_of_u8 ::"u8 \<Rightarrow> ireg option" where
"ireg_of_u8 i = (
        if i = 0 then
    Some RAX
  else  if i = 1 then
    Some RCX
  else  if i = 2 then
    Some RDX
  else  if i = 3 then
    Some RBX
  else  if i = 4 then
    Some RSP
  else  if i = 5 then
    Some RBP
  else  if i = 6 then
    Some RSI
  else  if i = 7 then
    Some RDI
  else  if i = 8 then
    Some R8
  else  if i = 9 then
    Some R9
  else  if i = 10 then
    Some R10
  else  if i = 11 then
    Some R11
  else  if i = 12 then
    Some R12
  else  if i = 13 then
    Some R13
  else  if i = 14 then
    Some R14
  else  if i = 15 then
    Some R15
  else
    None
)"

text \<open> skip float registers, as Solana rBPF doesn't deal with float \<close>

datatype crbit = ZF | CF | PF | SF | OF

datatype preg = PC | IR ireg | CR crbit | RA | TSC
          
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

  Naming conventions for types: Pmov_rm   rd a c  \<Rightarrow> exec_store  sz c m a rs (IR rd) [] |                 \<comment> \<open> load  mem to reg \<close>
  Pmov_mr   a r1 c  \<Rightarrow> exec_load   sz c m a rs (IR r1) |            
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
    Pmovl_rr ireg ireg       (**r [mov] (integer) *)
  | Pmovq_rr ireg ireg       (**r [mov] (integer) *)
  | Pmovl_ri ireg u32        (**imm   to reg *)
  | Pmovq_ri ireg u64        (**imm32 to qwordreg *)
  | Pmov_rm ireg addrmode  memory_chunk
  | Pmov_mr addrmode ireg memory_chunk
  | Pmov_mi addrmode u32  memory_chunk       (**imm to mem *)
  | Pcmov testcond ireg ireg
  (** Moves with conversion *)
    | Pmovsq_rr ireg ireg     (**r [movsl] (32-bit sign-extension) *)
  (** Integer arithmetic *)
  | Pleal ireg addrmode
  | Pleaq ireg addrmode
  | Pnegl ireg
  | Pnegq ireg
  | Paddq_rr ireg ireg
  | Paddl_rr ireg ireg
  | Paddl_ri ireg u32
  | Psubl_rr ireg ireg
  | Psubq_rr ireg ireg
  | Psubl_ri ireg u32
  | Pmull_r ireg
  | Pmulq_r ireg
  | Pimull_r ireg
  | Pimulq_r ireg
  | Pdivl_r ireg
  | Pdivq_r ireg
  | Pidivl_r ireg
  | Pidivq_r ireg

  | Pandl_rr ireg ireg
  | Pandl_ri ireg u32
  | Pandq_rr ireg ireg
  | Porl_rr ireg ireg
  | Porl_ri ireg u32
  | Porq_rr ireg ireg
  | Pxorl_rr ireg ireg
  | Pxorq_rr ireg ireg
  | Pxorl_ri ireg u32
  | Pshll_ri ireg u8
  | Pshlq_ri ireg u8
  | Pshll_r ireg
  | Pshlq_r ireg
  | Pshrl_ri ireg u8
  | Pshrq_ri ireg u8
  | Pshrl_r ireg
  | Pshrq_r ireg
  | Psarl_ri ireg u8
  | Psarq_ri ireg u8
  | Psarl_r ireg
  | Psarq_r ireg
  | Prolw_ri ireg u8
  | Prorl_ri ireg u8
  | Prorq_ri ireg u8

  | Ppushl ireg
  | Ppushq ireg
  | Ppushi u64

  | Pjcc testcond u32
  | Pjmp u32
  | Prdtsc
  | Pnop
(*
  | Pmovzb_rr ireg ireg     (**r [movzb] (8-bit zero-extension) *)
  | Pmovzb_rm ireg addrmode
  | Pmovsb_rr ireg ireg     (**r [movsb] (8-bit sign-extension) *)
  | Pmovsb_rm ireg addrmode
  | Pmovzw_rr ireg ireg     (**r [movzw] (16-bit zero-extension) *)
  | Pmovzw_rm ireg addrmode
  | Pmovsw_rr ireg ireg     (**r [movsw] (16-bit sign-extension) *)
  | Pmovsw_rm ireg addrmode
  | Pmovzl_rr ireg ireg     (**r [movzl] (32-bit zero-extension) *)
  | Pmovls_rr ireg          (** 64 to 32 bit conversion (pseudo) *)
  | Paddl_ri ireg u32
  | Paddq_ri ireg u64
  | Psubl_ri ireg u32
  | Psubq_ri ireg u64
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
  | Pidivq ireg *)
(*| Pxorl_r ireg                  (**r [xor] with self = set to zero *)
  | Pxorq_r ireg
  | Pandl_ri ireg u32
  | Pandq_ri ireg u64
  | Porl_ri ireg u32
  | Porq_ri ireg u64 
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
  | Psetcc testcond ireg*)
  (** Branches and calls *)
(*| Pjmp_l label
  | Pjcc testcond label
  | Pjcc2 testcond testcond label   (**r pseudo *)
  | Pjmptbl ireg "label list" (**r pseudo *)
  | Pcall_r (r: ireg)
  | Pret*)
  (** Saving and restoring registers *)
(*| Pmov_rm_a ireg addrmode  (**r like [Pmov_rm], using [Many64] chunk *)
  | Pmov_mr_a addrmode ireg  (**r like [Pmov_mr], using [Many64] chunk *) *)

type_synonym x64_asm = "instruction list"
type_synonym x64_bin = "u8 list"

lemma u8_of_ireg_of_u8_iff: "(u8_of_ireg r = i) = (ireg_of_u8 i = Some r)"
  by (cases r, auto simp add: ireg_of_u8_def)

end