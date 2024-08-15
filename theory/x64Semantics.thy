section \<open> x64 Semantics \<close>

theory x64Semantics
imports
  Main
  rBPFCommType Val Mem x64Syntax
begin

text \<open> define our x64 semantics in Isabelle/HOL, following the style of CompCert x64 semantics: https://github.com/AbsInt/CompCert/blob/master/x86/Asm.v  \<close>

type_synonym regset = "preg \<Rightarrow> val"

syntax "_pregmap_set" :: "'a => 'b => 'c => 'a" ("_ # _ <- _" [1000, 1000, 1000] 1)

(* Define the translation for the notation *)
translations
  "_pregmap_set a b c" => "(a(b := c))"

(*section \<open> Axiom Memory model \<close>

theory Mem
imports
  Main
  rBPFCommType Val
begin

type_synonym mem = "(u64, val) map"

datatype memory_chunk = M8 | M16 | M32 | M64

type_synonym addr_type = val

axiomatization
  loadv   :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val option" and
  storev  :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val \<Rightarrow> mem option"


end
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
    Val.add32 (case base of None \<Rightarrow> (Vint 0) | Some r \<Rightarrow> (rs (IR r)) )
      (Val.add32 (
        case ofs of None \<Rightarrow> (Vint 0) | Some (r, sc) \<Rightarrow>
          if sc = 1 then (rs (IR r)) else Val.mul32 (rs (IR r)) (Vint (of_int sc))
        )
        (Vint (of_int const))
      )
)"

definition eval_addrmode64 :: "addrmode \<Rightarrow> regset \<Rightarrow> val" where
"eval_addrmode64 a rs = (
  case a of Addrmode base ofs const \<Rightarrow>
    Val.add64 (case base of None \<Rightarrow> (Vlong 0) | Some r \<Rightarrow> (rs (IR r)) )
      (Val.add64 (
        case ofs of None \<Rightarrow> (Vlong 0) | Some (r, sc) \<Rightarrow>
          if sc = 1 then (rs (IR r)) else Val.mul64 (rs (IR r)) (Vlong (of_int sc))
        )
        (Vlong (of_int const))
      )
)"

definition compare_ints :: "val \<Rightarrow> val \<Rightarrow> regset \<Rightarrow> regset" where
"compare_ints x y rs = (((((
  rs#(CR ZF) <- (Val.cmpu Ceq x y))
    #(CR CF) <- (Val.cmpu Clt x y))
    #(CR SF) <- (Val.negative32 (Val.sub32 x y)))
    #(CR OF) <- (Val.sub_overflow32 x y))
    #(CR PF) <- Vundef)"

definition compare_longs :: "val \<Rightarrow> val \<Rightarrow> regset \<Rightarrow> regset" where
"compare_longs x y rs = (((((
  rs#(CR ZF) <- (Val.cmplu Ceq x y))
    #(CR CF) <- (Val.cmplu Clt x y))
    #(CR SF) <- (Val.negative64 (Val.sub64 x y)))
    #(CR OF) <- (Val.sub_overflow64 x y))
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

datatype outcome = Next regset mem | Stuck

definition nextinstr :: "u64 \<Rightarrow> regset \<Rightarrow> regset" where
"nextinstr sz rs = (rs#PC <- (Val.add64 (rs PC) (Vlong sz)))"

definition call :: "preg \<Rightarrow> regset \<Rightarrow> regset" where
"call dst rs = (rs#PC <- (rs dst))"

definition nextinstr_nf :: "u64 \<Rightarrow> regset \<Rightarrow> regset" where
"nextinstr_nf sz rs = nextinstr sz (undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] rs)"

definition exec_load :: "u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> addrmode \<Rightarrow> regset \<Rightarrow> preg \<Rightarrow> outcome" where
"exec_load sz chunk m a rs rd = (
  case Mem.loadv chunk m (eval_addrmode64 a rs) of
  None \<Rightarrow> Stuck |
  Some v \<Rightarrow> Next (nextinstr_nf sz (rs#rd <- v)) m
)"

definition exec_store :: "u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> addrmode \<Rightarrow> regset \<Rightarrow> preg \<Rightarrow> preg list \<Rightarrow> outcome" where
"exec_store sz chunk m a rs r1 destroyed = (
  case Mem.storev chunk m (eval_addrmode64 a rs) (rs r1) of
  None \<Rightarrow> Stuck |
  Some m' \<Rightarrow> Next (nextinstr_nf sz (undef_regs destroyed rs)) m'
)"

definition exec_pop :: "u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> preg \<Rightarrow> outcome" where
"exec_pop sz chunk m rs rd = (
  let nsp = Val.add64 (rs (IR SP)) (vlong_of_memory_chunk chunk) in
    case Mem.loadv chunk m (rs (IR SP)) of
    None \<Rightarrow> Stuck |
    Some v => let rs1 = rs#rd <- v in
      Next (nextinstr_nf sz (rs1#(IR SP) <- nsp)) m
)"

definition exec_push :: "u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> val \<Rightarrow> outcome" where
"exec_push sz chunk m rs v = (
  let nsp = Val.sub64 (rs (IR SP)) (vlong_of_memory_chunk chunk) in
    case Mem.storev chunk m nsp v of
    None \<Rightarrow> Stuck |
    Some m' => Next (nextinstr_nf sz (rs#(IR SP) <- nsp)) m'
)"

definition exec_call :: "u64  \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> val \<Rightarrow> outcome" where
"exec_call sz chunk m rs v = (
  let nsp = Val.sub64 (rs (IR SP)) (vlong_of_memory_chunk chunk) in
    case Mem.storev M64 m nsp v of
    None \<Rightarrow> Stuck |
    Some m' \<Rightarrow> let rs1 = rs#(IR SP) <- nsp in
              Next ((rs1#PC <- v)) m'
)"
    
                                                   
definition exec_instr :: "instruction \<Rightarrow> u64 \<Rightarrow> regset \<Rightarrow> mem \<Rightarrow> outcome" where
"exec_instr i sz rs m = (\<comment> \<open> sz is the binary size (n-byte) of current instruction  \<close>
  case i of
  \<comment> \<open> Moves \<close>
  Pmovl_rr  rd r1   \<Rightarrow> Next (nextinstr  sz (rs#(IR rd) <- (rs (IR r1)))) m |
  Pmovq_rr  rd r1   \<Rightarrow> Next (nextinstr  sz (rs#(IR rd) <- (rs (IR r1)))) m |
  Pmovl_ri  rd n    \<Rightarrow> Next (nextinstr  sz (rs#(IR rd) <- (Vint n))) m |    \<comment> \<open> load imm32 to reg \<close>
  Pmovq_ri  rd n    \<Rightarrow> Next (nextinstr  sz (rs#(IR rd) <- (Vlong n))) m |   \<comment> \<open> load imm64 to reg \<close>
  Pmov_rm   rd a c  \<Rightarrow> exec_store  sz c m a rs (IR rd) [] |                 \<comment> \<open> load  mem to reg \<close>
  Pmov_mr   a r1 c  \<Rightarrow> exec_load   sz c m a rs (IR r1) |                    \<comment> \<open> store reg to mem \<close>
  Pcmov     t rd r1 \<Rightarrow> let v = (case eval_testcond t rs of
                               Some b \<Rightarrow> if b then (rs (IR r1)) else (rs (IR rd)) |
                               None   \<Rightarrow> Vundef ) in
                         Next (nextinstr sz (rs#(IR rd)<-v)) m |
  Pxchgq_rr  rd r1 \<Rightarrow> let tmp = rs (IR rd) in
                      let rs1 = (rs#(IR rd)<- (rs (IR r1))) in
                        Next (nextinstr_nf sz (rs1#(IR r1)<- tmp)) m |
  \<comment> \<open> Pmov_mi   a n c  \<Rightarrow> exec_load   sz c m a rs (Vint n) | store immediate to memory \<close>
  \<comment> \<open> Moves with conversion \<close>
  Pmovsq_rr rd r1  \<Rightarrow> Next (nextinstr  sz (rs#(IR rd)  <- (Val.longofintu(rs (IR r1))))) m |
  \<comment> \<open> Integer arithmetic \<close>
  Pnegq     rd    \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.neg64 (rs (IR rd))))) m |
  Pnegl     rd    \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.neg32 (rs (IR rd))))) m |
  Paddq_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.add64 (rs (IR rd)) (rs (IR r1))))) m |
  Paddl_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.add32 (rs (IR rd)) (rs (IR r1))))) m |
  Paddl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.add32 (rs (IR rd)) (Vint n)))) m |
  Psubq_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.sub64 (rs (IR rd)) (rs (IR r1))))) m |
  Psubl_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.sub32 (rs (IR rd)) (rs (IR r1))))) m |
  Psubl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.sub32 (rs (IR rd)) (Vint n)))) m |
  Pandq_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.and64 (rs (IR rd)) (rs (IR r1))))) m |
  Pandl_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.and32 (rs (IR rd)) (rs (IR r1))))) m |
  Pandl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.and32 (rs (IR rd)) (Vint n)))) m |
  Porq_rr   rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.or64  (rs (IR rd)) (rs (IR r1))))) m |
  Porl_rr   rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.or32  (rs (IR rd)) (rs (IR r1))))) m |
  Porl_ri   rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.or32   (rs (IR rd)) (Vint n)))) m |
  Pxorq_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.or64  (rs (IR rd)) (rs (IR r1))))) m |
  Pxorl_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.or32  (rs (IR rd)) (rs (IR r1))))) m |
  Pmull_r   r1    \<Rightarrow> let rs1 = (rs#(IR RAX)<- (Val.mul32  (rs(IR RAX)) (rs (IR r1)))) in
                     Next (nextinstr_nf sz (rs1#(IR RDX)<-(Val.mulhu32 (rs (IR RAX))(rs (IR r1))))) m |
  Pmulq_r   r1    \<Rightarrow> let rs1 = (rs#(IR RAX)<- (Val.mul64 (rs(IR RAX)) (rs (IR r1)))) in
                     Next (nextinstr_nf sz (rs1#(IR RDX)<-(Val.mulhu32 (rs (IR RAX))(rs (IR r1))))) m |
  Pimull_r  r1    \<Rightarrow> let rs1 = (rs#(IR RAX)<- (Val.mul32  (rs(IR RAX)) (rs (IR r1)))) in
                     Next (nextinstr_nf sz (rs1#(IR RDX)<-(Val.mulhs32 (rs (IR RAX))(rs (IR r1))))) m |
  Pimulq_r  r1    \<Rightarrow> let rs1 = (rs#(IR RAX)<- (Val.mul64 (rs(IR RAX)) (rs (IR r1)))) in
                     Next (nextinstr_nf sz (rs1#(IR RDX)<-(Val.mulhs32 (rs (IR RAX))(rs (IR r1))))) m |
  Pdivl_r   r1    \<Rightarrow> (case Val.divmod32u (rs (IR RDX)) (rs (IR RAX)) (rs (IR r1)) of Some (Vint q, Vint r) \<Rightarrow> (
                         let rs1= (rs#(IR RAX) <- (Vint q)) in 
                     Next (nextinstr_nf sz (rs#(IR RDX) <- (Vint r)) ) m) | _  \<Rightarrow> Stuck ) |
  Pdivq_r   r1    \<Rightarrow> (case Val.divmod64u (rs (IR RDX)) (rs (IR RAX)) (rs (IR r1)) of Some (Vint q, Vint r) \<Rightarrow> (
                         let rs1= (rs#(IR RAX) <- (Vint q)) in 
                     Next (nextinstr_nf sz (rs#(IR RDX) <- (Vint r)) ) m) | _  \<Rightarrow> Stuck ) |
  Pidivl_r  r1    \<Rightarrow> (case Val.divmod64u (rs (IR RDX)) (rs (IR RAX)) (rs (IR r1)) of Some (Vint q, Vint r) \<Rightarrow> (
                         let rs1= (rs#(IR RAX) <- (Vint q)) in 
                     Next (nextinstr_nf sz (rs#(IR RDX) <- (Vint r)) ) m) | _  \<Rightarrow> Stuck ) |
  Pidivq_r  r1    \<Rightarrow> (case Val.divmod64u (rs (IR RDX)) (rs (IR RAX)) (rs (IR r1)) of Some (Vint q, Vint r) \<Rightarrow> (
                         let rs1= (rs#(IR RAX) <- (Vint q)) in 
                     Next (nextinstr_nf sz (rs#(IR RDX) <- (Vint r)) ) m) | _  \<Rightarrow> Stuck ) |
  Pshll_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.shl32  (rs (IR rd)) (Vbyte n)))) m |  \<comment>\<open> imm8 \<close>
  Pshlq_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.shl64  (rs (IR rd)) (Vbyte n)))) m |  \<comment>\<open> imm8 \<close>
  Pshll_r   rd    \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.shl32  (rs (IR rd)) (rs(IR RCX))))) m |
  Pshlq_r   rd    \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.shl64  (rs (IR rd)) (rs(IR RCX))))) m |
  Pshrl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.shr32  (rs (IR rd)) (Vbyte n)))) m |  \<comment>\<open> imm8 \<close>
  Pshrq_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.shr64  (rs (IR rd)) (Vbyte n)))) m |  \<comment>\<open> imm8 \<close>
  Pshrl_r   rd    \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.shr32  (rs (IR rd)) (rs(IR RCX))))) m |
  Pshrq_r   rd    \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.shr64  (rs (IR rd)) (rs(IR RCX))))) m |
  Psarl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.sar32  (rs (IR rd)) (Vbyte n)))) m |  \<comment>\<open> imm8 \<close>
  Psarq_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.sar64  (rs (IR rd)) (Vbyte n)))) m |  \<comment>\<open> imm8 \<close>
  Psarl_r   rd    \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.sar32  (rs (IR rd)) (rs(IR RCX))))) m |
  Psarq_r   rd    \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.sar64  (rs (IR rd)) (rs(IR RCX))))) m | 
  Prolw_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.rol16  (rs (IR rd)) (Vbyte n)))) m | \<comment>\<open> bswap16 \<close>
  Prorl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.ror32  (rs (IR rd)) (Vbyte n)))) m |  
  Prorq_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.ror64  (rs (IR rd)) (Vbyte n)))) m |  

  Ppushl_r  r1    \<Rightarrow> exec_push sz M32 m rs (rs (IR r1)) |
  Ppushl_i  n     \<Rightarrow> exec_push sz M32 m rs (Vint (ucast n)) |
  Ppopl     rd    \<Rightarrow> exec_pop  sz M32 m rs (IR rd) |

  Pjcc      t d   \<Rightarrow> (case eval_testcond t rs of
                               Some b  \<Rightarrow>if b then Next (nextinstr (scast d) rs) m
                                         else      Next (nextinstr sz rs) m|
                               None    \<Rightarrow> Stuck)|
  Pjmp      d     \<Rightarrow> Next (nextinstr (scast d) rs) m |
  Pcall_r   r1    \<Rightarrow> exec_call sz M64 m rs (rs (IR r1))|
  Pcall_i   d     \<Rightarrow> exec_call sz M64 m rs (Vint(ucast d))|

  Prdtsc          \<Rightarrow> let rs1 = (rs#(IR RAX)<- (Val.intoflongl ((rs TSC)))) in
                     Next (nextinstr_nf sz (rs1#(IR RDX)<-(Val.intoflongh  (rs TSC)))) m |
  Pnop            \<Rightarrow> Next (nextinstr sz rs) m |
  _               \<Rightarrow> Stuck
)"

(*
  Paddq_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.add64 (rs (IR rd)) (Vlong n)))) m |
  Paddl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.add  (rs (IR rd)) (Vint n)))) m |
  Psubq_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.sub64 (rs (IR rd)) (Vlong n)))) m |
  Psubl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.sub  (rs (IR rd)) (Vint n)))) m |
  Pandq_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.andl (rs (IR rd)) (Vlong n)))) m |
  Pandl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.andd (rs (IR rd)) (Vint n)))) m |
  Porq_ri   rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.orl  (rs (IR rd)) (Vlong n)))) m |
  Porl_ri   rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.or   (rs (IR rd)) (Vint n)))) m |
  Pxorq_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.orl  (rs (IR rd)) (Vlong n)))) m |
  Pxorl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.or   (rs (IR rd)) (Vint n)))) m |
  Ppushq_m  a c   \<Rightarrow> exec_push sz M64 m rs (rs (IR r1)) |
*)

(**r
  | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1))) m
  | Pmovzb_rm rd a =>
      exec_load Mint8unsigned m a rs rd
  | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) m
  | Pmovsb_rm rd a =>
      exec_load Mint8signed m a rs rd
  | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1))) m
  | Pmovzw_rm rd a =>
      exec_load Mint16unsigned m a rs rd
  | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) m
  | Pmovsw_rm rd a =>
      exec_load Mint16signed m a rs rd
  | Pmovzl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofintu rs#r1))) m
  | Pmovsl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofint rs#r1))) m
  | Pmovls_rr rd =>
      Next (nextinstr (rs#rd <- (Val.loword rs#rd))) m
  (** Integer arithmetic *)
  | Pleal rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode32 a rs))) m
  | Pleaq rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode64 a rs))) m
| Pnegl rd =>
    Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd))) m
| Pnegq rd =>
    Next (nextinstr_nf (rs#rd <- (Val.negl rs#rd))) m
| Paddl_ri rd n =>
    Next (nextinstr_nf (rs#rd <- (Val.add rs#rd (Vint n)))) m
| Paddq_ri rd n =>
    Next (nextinstr_nf (rs#rd <- (Val.add64 rs#rd (Vlong n)))) m
| Psubl_rr rd r1 =>
    Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1))) m
| Psubq_rr rd r1 =>
    Next (nextinstr_nf (rs#rd <- (Val.sub64 rs#rd rs#r1))) m
  | Pimull_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul32 rs#rd rs#r1))) m
  | Pimulq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul64 rs#rd rs#r1))) m
  | Pimull_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul32 rs#rd (Vint n)))) m
  | Pimulq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul64 rs#rd (Vlong n)))) m
  | Pimull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul32 rs#RAX rs#r1)
                            #RDX <- (Val.mulhs rs#RAX rs#r1))) m
  | Pimulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul64 rs#RAX rs#r1)
                            #RDX <- (Val.mullhs rs#RAX rs#r1))) m
  | Pmull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul32 rs#RAX rs#r1)
                            #RDX <- (Val.mulhu rs#RAX rs#r1))) m
  | Pmulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul64 rs#RAX rs#r1)
                            #RDX <- (Val.mullhu rs#RAX rs#r1))) m
  | Pcltd =>
      Next (nextinstr_nf (rs#RDX <- (Val.shr rs#RAX (Vint (Int.repr 31))))) m
  | Pcqto =>
      Next (nextinstr_nf (rs#RDX <- (Val.shrl rs#RAX (Vint (Int.repr 63))))) m
  | Pdivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pdivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pandl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1))) m
  | Pandq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd rs#r1))) m
  | Pandl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n)))) m
  | Pandq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd (Vlong n)))) m
  | Porl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1))) m
  | Porq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd rs#r1))) m
  | Porl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n)))) m
  | Porq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd (Vlong n)))) m
  | Pxorl_r rd =>
      Next (nextinstr_nf (rs#rd <- Vzero)) m
  | Pxorq_r rd =>
      Next (nextinstr_nf (rs#rd <- (Vlong Int64.zero))) m
  | Pxorl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1))) m
  | Pxorq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd rs#r1))) m
  | Pxorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n)))) m
  | Pxorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd (Vlong n)))) m
  | Pnotl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notint rs#rd))) m
  | Pnotq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notl rs#rd))) m
  | Psall_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl32 rs#rd rs#RCX))) m
  | Psalq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl64 rs#rd rs#RCX))) m
  | Psall_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl32 rs#rd (Vint n)))) m
  | Psalq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl64 rs#rd (Vint n)))) m
  | Pshrl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#RCX))) m
  | Pshrq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd rs#RCX))) m
  | Pshrl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n)))) m
  | Pshrq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd (Vint n)))) m
  | Psarl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#RCX))) m
  | Psarq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd rs#RCX))) m
  | Psarl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n)))) m
  | Psarq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd (Vint n)))) m
  | Pshld_ri rd r1 n =>
      Next (nextinstr_nf
              (rs#rd <- (Val.or (Val.shl32 rs#rd (Vint n))
                                (Val.shru rs#r1 (Vint (Int.sub Int.iwordsize n)))))) m
  | Prorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n)))) m
  | Prorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.rorl rs#rd (Vint n)))) m
  | Pcmpl_rr r1 r2 =>
      Next (nextinstr (compare_ints (rs r1) (rs r2) rs m)) m
  | Pcmpq_rr r1 r2 =>
      Next (nextinstr (compare_longs (rs r1) (rs r2) rs m)) m
  | Pcmpl_ri r1 n =>
      Next (nextinstr (compare_ints (rs r1) (Vint n) rs m)) m
  | Pcmpq_ri r1 n =>
      Next (nextinstr (compare_longs (rs r1) (Vlong n) rs m)) m
  | Ptestl_rr r1 r2 =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs m)) m
  | Ptestq_rr r1 r2 =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (rs r2)) (Vlong Int64.zero) rs m)) m
  | Ptestl_ri r1 n =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs m)) m
  | Ptestq_ri r1 n =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (Vlong n)) (Vlong Int64.zero) rs m)) m
  | Pcmov c rd r1 =>
      let v :=
        match eval_testcond c rs with
        | Some b => if b then rs#r1 else rs#rd
        | None   => Vundef
      end in
      Next (nextinstr (rs#rd <- v)) m
  | Psetcc c rd =>
      Next (nextinstr (rs#rd <- (Val.of_optbool (eval_testcond c rs)))) m
  (** Branches and calls *)
  | Pjmp_l lbl =>
      goto_label f lbl rs m
  | Pjmp_s id sg =>
      Next (rs#PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pjmp_r r sg =>
      Next (rs#PC <- (rs r)) m
  | Pjcc cond lbl =>
      match eval_testcond cond rs with
      | Some true => goto_label f lbl rs m
      | Some false => Next (nextinstr rs) m
      | None => Stuck
      end
  | Pjcc2 cond1 cond2 lbl =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => goto_label f lbl rs m
      | Some _, Some _ => Next (nextinstr rs) m
      | _, _ => Stuck
      end
  | Pjmptbl r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs #RAX <- Vundef #RDX <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcall_r r sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (rs r)) m
  | Pret =>
      Next (rs#PC <- (rs#RA)) m
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
      exec_load (if Archi.ptr64 then Many64 else Many32) m a rs rd
  | Pmov_mr_a a r1 =>
      exec_store (if Archi.ptr64 then Many64 else Many32) m a rs r1 nil
  | Pmovsd_fm_a rd a =>
      exec_load Many64 m a rs rd
  | Pmovsd_mf_a a r1 =>
      exec_store Many64 m a rs r1 nil
  (** Pseudo-instructions *)
  | Plabel lbl =>
      Next (nextinstr rs) m


*)

end
