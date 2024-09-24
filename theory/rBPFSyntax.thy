theory rBPFSyntax
imports
    Main
    rBPFCommType Mem
begin

datatype bpf_ireg = BR0 | BR1 | BR2 | BR3 | BR4 | BR5 | BR6 | BR7 | BR8 | BR9 | BR10

(*
datatype bpf_preg = BR bpf_ireg | BPC *)

type_synonym off_ty = i16
type_synonym imm_ty = i32

type_synonym dst_ty = bpf_ireg  
type_synonym src_ty = bpf_ireg  

datatype snd_op = SOImm imm_ty | SOReg bpf_ireg

datatype arch = A32 | A64

fun arch2int :: "arch \<Rightarrow> int" where
"arch2int A32 = 32" |
"arch2int A64 = 64"

datatype condition = Eq | Gt | Ge | Lt | Le | SEt | Ne | SGt | SGe | SLt | SLe

datatype binop = BPF_ADD | BPF_SUB | BPF_MUL | BPF_DIV | BPF_OR | BPF_AND |
  BPF_LSH | BPF_RSH | BPF_MOD | BPF_XOR | BPF_MOV | BPF_ARSH 

datatype pqrop = BPF_LMUL | BPF_UDIV | BPF_UREM | BPF_SDIV | BPF_SREM

datatype pqrop2 = BPF_UHMUL | BPF_SHMUL

datatype chunk = Byte | HalfWord | SWord | DWord 
                                                
datatype SBPFV = V1 (* The legacy format *) |
 V2 (* The current SOImm *)(* |
 V3  The future format with BTF support *)

datatype bpf_instruction = 
  BPF_LD_IMM            dst_ty imm_ty imm_ty | 
  (* BPF_LDX class *)
  BPF_LDX memory_chunk  dst_ty src_ty off_ty |
  (* BPF_ST/BPF_STX class *)
  BPF_ST  memory_chunk  dst_ty snd_op off_ty |
  (* BPF_ALU class *)
  BPF_ADD_STK imm_ty |
  BPF_ALU     binop   dst_ty snd_op |
  BPF_NEG32_REG       dst_ty        |
  BPF_LE              dst_ty imm_ty |
  BPF_BE              dst_ty imm_ty |
  (* BPF_ALU64 class *)
  BPF_ALU64   binop   dst_ty snd_op |
  BPF_NEG64_REG       dst_ty        |
  BPF_HOR64_IMM       dst_ty imm_ty |
  (* BPF_PQR class *)
  BPF_PQR     pqrop   dst_ty snd_op |
  BPF_PQR64   pqrop   dst_ty snd_op |
  BPF_PQR2    pqrop2  dst_ty snd_op |
  (* BPF_JMP class *)
  BPF_JA off_ty |
  BPF_JUMP condition bpf_ireg snd_op off_ty |
  BPF_CALL_REG src_ty imm_ty |
  BPF_CALL_IMM src_ty imm_ty |
  
  BPF_EXIT
  
type_synonym ebpf_asm = "bpf_instruction list"
  
type_synonym bpf_bin = "u8 list"

fun bpf_ireg2u4 :: "bpf_ireg \<Rightarrow> u4" where
"bpf_ireg2u4 BR0 = 0" | 
"bpf_ireg2u4 BR1 = 1" | 
"bpf_ireg2u4 BR2 = 2" | 
"bpf_ireg2u4 BR3 = 3" | 
"bpf_ireg2u4 BR4 = 4" | 
"bpf_ireg2u4 BR5 = 5" | 
"bpf_ireg2u4 BR6 = 6" | 
"bpf_ireg2u4 BR7 = 7" | 
"bpf_ireg2u4 BR8 = 8" | 
"bpf_ireg2u4 BR9 = 9" | 
"bpf_ireg2u4 BR10 = 10" 

definition u4_to_bpf_ireg :: "u4 \<Rightarrow> bpf_ireg option" where
"u4_to_bpf_ireg dst =
  (       if dst = 0 then Some BR0
    else  if dst = 1 then Some BR1
    else  if dst = 2 then Some BR2
    else  if dst = 3 then Some BR3
    else  if dst = 4 then Some BR4
    else  if dst = 5 then Some BR5
    else  if dst = 6 then Some BR6
    else  if dst = 7 then Some BR7
    else  if dst = 8 then Some BR8
    else  if dst = 9 then Some BR9
    else  if dst = 10 then Some BR10
    else None)"

end
