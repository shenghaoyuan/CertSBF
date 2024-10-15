section \<open> x64 Semantics \<close>

theory x64Semantics
imports
  Main
  rBPFCommType Val Mem x64Syntax
  x64Disassembler
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
(*
definition eval_addrmode32 :: "addrmode \<Rightarrow> regset \<Rightarrow> val" where
"eval_addrmode32 a rs = (
  case a of Addrmode base ofs const \<Rightarrow>
    Val.add32 (case base of None \<Rightarrow> (Vint 0) | Some r \<Rightarrow> (rs (IR r)) )
      (Val.add32 (
        case ofs of None \<Rightarrow> (Vint 0) | Some (r, sc) \<Rightarrow>
          Val.shl32 (rs (IR r)) (Vbyte (ucast sc))
        )
        (Vint const)
      )
)" *)


definition eval_addrmode64_val :: "addrmode \<Rightarrow> regset \<Rightarrow> val" where
"eval_addrmode64_val a rs = (
  case a of Addrmode base ofs const \<Rightarrow>
    Val.add64 (case base of None \<Rightarrow> (Vlong 0) | Some r \<Rightarrow> (rs (IR r)) )
      (Val.add64 (
        case ofs of None \<Rightarrow> (Vlong 0) | Some (r, sc) \<Rightarrow>
          Val.shl64 (rs (IR r)) (Vbyte (ucast sc))
        )
        (Vlong (scast const))
      )
)"

definition eval_addrmode64 :: "addrmode \<Rightarrow> regset \<Rightarrow> u64 option" where
"eval_addrmode64 a rs = (
  case eval_addrmode64_val a rs of
  Vlong v \<Rightarrow> Some v |
  _ \<Rightarrow> None
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
"nextinstr sz rs = (rs#PC <- (Val.add64 (rs PC) (Vlong (sz+1))))"

definition call :: "preg \<Rightarrow> regset \<Rightarrow> regset" where
"call dst rs = (rs#PC <- (rs dst))"

definition nextinstr_nf :: "u64 \<Rightarrow> regset \<Rightarrow> regset" where
"nextinstr_nf sz rs = nextinstr sz (undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] rs)"

definition exec_load :: "u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> addrmode \<Rightarrow> regset \<Rightarrow> preg \<Rightarrow> outcome" where
"exec_load sz chunk m a rs rd = (
  case eval_addrmode64 a rs of
  None \<Rightarrow> Stuck |
  Some addr \<Rightarrow> (
    case Mem.loadv chunk m addr of
      None \<Rightarrow> Stuck | 
      Some v \<Rightarrow> Next (nextinstr_nf sz (rs#rd <- v)) m
  )
)"

definition exec_store :: "u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> addrmode \<Rightarrow> regset \<Rightarrow> preg \<Rightarrow> preg list \<Rightarrow> outcome" where
"exec_store sz chunk m a rs r1 destroyed = (
  case eval_addrmode64 a rs of
  None \<Rightarrow> Stuck |
  Some addr \<Rightarrow> (
    case Mem.storev chunk m addr (rs r1) of
      None \<Rightarrow> Stuck |
      Some m' \<Rightarrow> Next (nextinstr_nf sz (undef_regs destroyed rs)) m'
  )
)"

definition exec_pop :: "u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> preg \<Rightarrow> outcome" where
"exec_pop sz chunk m rs rd = (
  let nsp = Val.add64 (rs (IR SP)) (vlong_of_memory_chunk chunk) in
    case (rs (IR SP)) of
    Vlong addr \<Rightarrow> (
      case Mem.loadv chunk m addr of
        None \<Rightarrow> Stuck |
        Some v => let rs1 = rs#rd <- v in
          Next (nextinstr_nf sz (rs1#(IR SP) <- nsp)) m
    ) |
    _ \<Rightarrow> Stuck
)"

definition exec_push :: "u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> val \<Rightarrow> outcome" where
"exec_push sz chunk m rs v = (
  let nsp = Val.sub64 (rs (IR SP)) (vlong_of_memory_chunk chunk) in
    case nsp of
    Vlong addr \<Rightarrow> (
      case Mem.storev chunk m addr v of
        None \<Rightarrow> Stuck |
        Some m' => Next (nextinstr_nf sz (rs#(IR SP) <- nsp)) m'
    ) |
    _ \<Rightarrow> Stuck
)"
  \<comment> \<open> near call \<close>
definition exec_call :: "u64  \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> val \<Rightarrow> outcome" where
"exec_call sz chunk m rs v = (
  let nsp = Val.sub64 (rs (IR SP)) (vlong_of_memory_chunk chunk) in
    case nsp of
    Vlong addr \<Rightarrow> (
      case Mem.storev M64 m addr v of
        None \<Rightarrow> Stuck |
        Some m' \<Rightarrow> let rs1 = rs#(IR SP) <- nsp in
                  Next (rs1#PC <- v) m'
    ) |
    _ \<Rightarrow> Stuck
)"

  \<comment> \<open> near ret \<close>
definition exec_ret :: "u64  \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> outcome" where
"exec_ret sz chunk m rs = (
  let nsp = Val.add64 (rs (IR SP)) (vlong_of_memory_chunk chunk) in
    case nsp of
    Vlong addr \<Rightarrow> (
      case Mem.loadv M64 m addr of
        None \<Rightarrow> Stuck |
        Some ra \<Rightarrow> let rs1 = rs#(IR SP) <- nsp in
                  Next ((rs1#PC <- ra)) m
    ) |
    _ \<Rightarrow> Stuck
)"
    
definition testVal32 :: "testcond \<Rightarrow> regset \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
"testVal32 t rs v1 v2 = (
  case v1 of
    Vint n1 \<Rightarrow> (case v2 of Vint n2 \<Rightarrow>
      let v = (case eval_testcond t rs of
        Some b \<Rightarrow> if b then (Vint n2) else (Vint n1) |
        None   \<Rightarrow> Vundef ) in
      let v1 =  (case v of Vint v1 \<Rightarrow> (Vint v1)| _ \<Rightarrow> Vundef) in
      v1
    | _ \<Rightarrow> Vundef) |
    _ \<Rightarrow> Vundef
)" 

definition testVal64 :: "testcond \<Rightarrow> regset \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
"testVal64 t rs v1 v2 = (
  case v1 of
    Vlong n1 \<Rightarrow> (case v2 of Vlong n2 \<Rightarrow>
      let v = (case eval_testcond t rs of
        Some b \<Rightarrow> if b then (Vlong n2) else (Vlong n1) |
        None   \<Rightarrow> Vundef ) in
      let v1 =  (case v of Vint v1 \<Rightarrow> (Vint v1)| _ \<Rightarrow> Vundef) in
      v1
    | _ \<Rightarrow> Vundef) |
    _ \<Rightarrow> Vundef
)" 

definition exec_instr :: "instruction \<Rightarrow> u64 \<Rightarrow> regset \<Rightarrow> mem \<Rightarrow> outcome" where
"exec_instr i sz rs m = (\<comment> \<open> sz is the binary size (n-byte) of current instruction  \<close>
  case i of
  \<comment> \<open> Moves \<close>
  Pmovl_rr rd r1  \<Rightarrow> Next (nextinstr  sz (rs#(IR rd) <- (rs (IR r1)))) m |
  Pmovq_rr rd r1  \<Rightarrow> Next (nextinstr  sz (rs#(IR rd) <- (rs (IR r1)))) m |
  Pmovl_ri rd n   \<Rightarrow> Next (nextinstr  sz (rs#(IR rd) <- (Vint n))) m |    \<comment> \<open> load imm32 to reg \<close>
  Pmovq_ri rd n   \<Rightarrow> Next (nextinstr  sz (rs#(IR rd) <- (Vlong n))) m |   \<comment> \<open> load imm64 to reg \<close>
  Pmov_rm  rd a c \<Rightarrow> exec_store  sz c m a rs (IR rd) [] |                 \<comment> \<open> load  mem to reg \<close>
  Pmov_mr  a r1 c \<Rightarrow> exec_load   sz c m a rs (IR r1) |                    \<comment> \<open> store reg to mem \<close>
  Pcmovl   t rd r1\<Rightarrow> Next (nextinstr  sz (rs#(IR rd) <- (testVal32 t rs (rs (IR rd)) (rs (IR r1))))) m |
  Pcmovq   t rd r1\<Rightarrow> Next (nextinstr  sz (rs#(IR rd) <- (testVal64 t rs (rs (IR rd)) (rs (IR r1))))) m |
  Pxchgq_rr rd r1 \<Rightarrow> let tmp = rs (IR rd) in
                     let rs1 = (rs#(IR rd)<- (rs (IR r1))) in
                       Next (nextinstr_nf sz (rs1#(IR r1)<- tmp)) m |
  Pxchgq_rm r1 a c\<Rightarrow> ((case eval_addrmode64 a rs of None \<Rightarrow> Stuck | Some addr \<Rightarrow> (
                        case Mem.loadv M64 m addr of None \<Rightarrow> Stuck | Some v \<Rightarrow> 
                         (let tmp = (rs (IR r1)) in 
                           case Mem.storev M64 m addr tmp of None \<Rightarrow> Stuck |
                            Some m' \<Rightarrow> Next (nextinstr_nf sz  (rs#(IR r1) <- v)) m')))) | 
  Pmov_mi   a n c \<Rightarrow> ((case eval_addrmode64 a rs of None \<Rightarrow> Stuck | Some addr \<Rightarrow> (
                        case Mem.storev c m addr (Vint n) of
                        None \<Rightarrow> Stuck| 
                        Some m' \<Rightarrow> Next (nextinstr_nf sz rs) m'))) |  \<comment> \<open>store imm32 to mem32/64 \<close>
  \<comment> \<open> Moves with conversion \<close>
  Pmovsq_rr rd r1 \<Rightarrow> Next (nextinstr    sz (rs#(IR rd) <- (Val.longofintu(rs (IR r1))))) m |
  Pcdq            \<Rightarrow> Next (nextinstr    sz (rs#(IR RDX)<- (Val.signex32(rs (IR RAX))))) m | \<comment> \<open>sign_extend_eax_edx \<close>
  Pcqo            \<Rightarrow> Next (nextinstr    sz (rs#(IR RDX)<- (Val.signex64(rs (IR RAX))))) m | \<comment> \<open>sign_extend_rax_rdx \<close>
  \<comment> \<open> Integer arithmetic \<close>
  Pleaq     rd a  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (eval_addrmode64_val a rs))) m |
  Pnegq     rd    \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.neg64 (rs (IR rd))))) m |
  Pnegl     rd    \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.neg32 (rs (IR rd))))) m |
  Paddq_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.add64 (rs (IR rd)) (rs (IR r1))))) m |
  Paddq_mi  a n c \<Rightarrow> ((case eval_addrmode64 a rs of None \<Rightarrow> Stuck | Some addr \<Rightarrow> (
                        case Mem.loadv c m addr of None \<Rightarrow> Stuck | Some v \<Rightarrow> 
                        (case Mem.storev c m addr (Val.add64 v (Vlong (scast n))) of None \<Rightarrow> Stuck |
                         Some m' \<Rightarrow> Next (nextinstr_nf sz rs) m')))) | 
  Paddl_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.add32 (rs (IR rd)) (rs (IR r1))))) m |
  Paddl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.add32 (rs (IR rd)) (Vint n)))) m |
  Paddw_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.add16 (rs (IR rd)) (Vshort n)))) m |
  Psubq_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.sub64 (rs (IR rd)) (rs (IR r1))))) m |
  Psubl_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.sub32 (rs (IR rd)) (rs (IR r1))))) m |
  Psubl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.sub32 (rs (IR rd)) (Vint n)))) m |
  Pandq_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.and64 (rs (IR rd)) (rs (IR r1))))) m |
  Pandl_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.and32 (rs (IR rd)) (rs (IR r1))))) m |
  Pandl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.and32 (rs (IR rd)) (Vint n)))) m |
  Porq_rr   rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.or64  (rs (IR rd)) (rs (IR r1))))) m |
  Porl_rr   rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.or32  (rs (IR rd)) (rs (IR r1))))) m |
  Porl_ri   rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.or32  (rs (IR rd)) (Vint n)))) m |
  Pxorq_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.xor64 (rs (IR rd)) (rs (IR r1))))) m |
  Pxorl_rr  rd r1 \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.xor32 (rs (IR rd)) (rs (IR r1))))) m |
  Pxorl_ri  rd n  \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.xor32 (rs (IR rd)) (Vint n)))) m |
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
                     Next (nextinstr_nf sz rs1)m) | _  \<Rightarrow> Stuck ) |
  Pdivq_r   r1    \<Rightarrow> (case Val.divmod64u (rs (IR RDX)) (rs (IR RAX)) (rs (IR r1)) of Some (Vlong q, Vlong r) \<Rightarrow> (
                         let rs1= (rs#(IR RAX) <- (Vlong q)) in 
                     Next (nextinstr_nf sz rs1)m) | _  \<Rightarrow> Stuck ) | \<comment>\<open> no need for #(IR RDX) <- (Vlong r) \<close>
  Pidivl_r  r1    \<Rightarrow> (case Val.divmod32u (rs (IR RDX)) (rs (IR RAX)) (rs (IR r1)) of Some (Vint q, Vint r) \<Rightarrow> (
                         let rs1= (rs#(IR RAX) <- (Vint q)) in 
                     Next (nextinstr_nf sz rs1)m) | _  \<Rightarrow> Stuck ) |
  Pidivq_r  r1    \<Rightarrow> (case Val.divmod64u (rs (IR RDX)) (rs (IR RAX)) (rs (IR r1)) of Some (Vlong q, Vlong r) \<Rightarrow> (
                         let rs1= (rs#(IR RAX) <- (Vlong q)) in 
                      Next (nextinstr_nf sz rs1)m) | _  \<Rightarrow> Stuck ) | \<comment>\<open> 
  Pmodq_r   r1    \<Rightarrow> (case Val.divmod64u (rs (IR RDX)) (rs (IR RAX)) (rs (IR r1)) of Some (Vlong q, Vlong r) \<Rightarrow> (
                         let rs1= (rs#(IR RDX) <- (Vlong r)) in added for ebpf correspondence
                      Next (nextinstr_nf sz rs1)m) | _  \<Rightarrow> Stuck ) | \<close>
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
  Pbswapl   rd    \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.bswap32(rs (IR rd))))) m | 
  Pbswapq   rd    \<Rightarrow> Next (nextinstr_nf sz (rs#(IR rd) <- (Val.bswap64(rs (IR rd))))) m |  

  Ppushl_r  r1    \<Rightarrow> exec_push sz M32 m rs (rs (IR r1)) |
  Ppushl_i  n     \<Rightarrow> exec_push sz M32 m rs (Vint (ucast n)) |
  Ppushq_m  a c   \<Rightarrow> ((case eval_addrmode64 a rs of None \<Rightarrow> Stuck | Some addr \<Rightarrow> (
                        case Mem.loadv M64 m addr of None \<Rightarrow> Stuck | Some v \<Rightarrow>(
                          exec_push sz M64 m rs v)))) |
  Ppopl     rd    \<Rightarrow> exec_pop  sz M32 m rs (IR rd) |

  Ptestl_rr r1 r2 \<Rightarrow> Next (nextinstr sz (compare_ints  (Val.and32 (rs (IR r1)) (rs (IR r2))) (Vint 0) rs)) m |
  Ptestq_rr r1 r2 \<Rightarrow> Next (nextinstr sz (compare_longs (Val.and64 (rs (IR r1)) (rs (IR r2))) (Vlong 0) rs)) m |
  Ptestl_ri rd n  \<Rightarrow> Next (nextinstr sz (compare_ints  (Val.and32 (rs (IR rd)) (Vint n)) (Vint 0) rs)) m |
  Ptestq_ri rd n  \<Rightarrow> Next (nextinstr sz (compare_longs (Val.and64 (rs (IR rd)) (Vlong (ucast n))) (Vlong 0) rs)) m |
  Pcmpl_rr  r1 r2 \<Rightarrow> Next (nextinstr sz (compare_ints  (rs (IR r1)) (rs (IR r2)) rs)) m |
  Pcmpq_rr  r1 r2 \<Rightarrow> Next (nextinstr sz (compare_longs (rs (IR r1)) (rs (IR r2)) rs)) m |
  Pcmpl_ri  r1 n  \<Rightarrow> Next (nextinstr sz (compare_ints  (rs (IR r1)) (Vint n) rs)) m  |
  Pcmpq_ri  r1 n  \<Rightarrow> Next (nextinstr sz (compare_longs (rs (IR r1)) (Vlong (ucast n)) rs)) m  |

  Pjcc      t d   \<Rightarrow> (case eval_testcond t rs of
                               Some b  \<Rightarrow>if b then Next (nextinstr (scast d) rs) m
                                         else      Next (nextinstr sz rs) m|
                               None    \<Rightarrow> Stuck)|
  Pjmp      d     \<Rightarrow> Next (nextinstr (scast d) rs) m |
  Pcall_r   r1    \<Rightarrow> exec_call sz M64 m rs (rs (IR r1))|
  Pcall_i   d     \<Rightarrow> exec_call sz M64 m rs (Vlong (scast d))|
  Pret            \<Rightarrow> exec_ret  sz M64 m rs|  \<comment>\<open> In 64-bit mode, the default operation size of near returns is the stack-address size, i.e., 64 bits. \<close>
  Prdtsc          \<Rightarrow> let rs1 = (rs#(IR RAX)<- (Val.intoflongl ((rs TSC)))) in
                     Next (nextinstr_nf sz (rs1#(IR RDX)<-(Val.intoflongh  (rs TSC)))) m |
  Pnop            \<Rightarrow> Next (nextinstr sz rs) m |
  _               \<Rightarrow> Stuck
)"


fun interp2 :: "nat \<Rightarrow> instruction list \<Rightarrow> outcome \<Rightarrow> outcome" where
"interp2 _ [] s = s" |
"interp2 0 _ _ = Stuck" |
"interp2 (Suc n) (ins#l) st = (
  case st of
  Stuck \<Rightarrow> Stuck |
  Next rs m \<Rightarrow> (
        interp2 n l (exec_instr ins 1 rs m)
))"


fun interp3 :: "instruction list \<Rightarrow> outcome \<Rightarrow> outcome" where
"interp3 [] s = s" |
"interp3 (ins#l) st = (
  case st of
  Stuck \<Rightarrow> Stuck |
  Next rs m \<Rightarrow> (
        interp3 l (exec_instr ins 1 rs m)
))"


definition exec_instr2::"instruction \<Rightarrow> outcome \<Rightarrow> outcome" where
"exec_instr2 ins st = st"

fun interp4 :: "instruction list \<Rightarrow> outcome \<Rightarrow> outcome" where
"interp4 [] s = s" |
"interp4 (ins#l) st = (
        interp4 l (exec_instr2 ins st)
)"

(*
value "interp2 3 [Ppushl_r x64Syntax.RCX, Ppopl x64Syntax.RCX] s"
value "interp2 0 [] s" *)


fun interp :: "nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
"interp 0 _ _ = Stuck" |
"interp (Suc n) l st = (
  case st of
  Stuck \<Rightarrow> Stuck |
  Next rs m \<Rightarrow> (
    case rs PC of
    Vlong v \<Rightarrow> (
      case x64_decode (unat v) l of
      None \<Rightarrow> Stuck |
      Some (sz, ins) \<Rightarrow>
        interp n l (exec_instr ins (of_nat sz) rs m)
      ) |
    _ \<Rightarrow> Stuck)
)"
end
