theory Disassembler
imports
  Main
  "HOL.Bit_Operations" "HOL-Library.Word"
  rBPFCommType rBPFSyntax
begin

fun disassemble_lddw :: "u4 => i32 \<Rightarrow> ebpf_binary \<Rightarrow> bpf_instruction option" where
"disassemble_lddw dst imm imm_h =
  ( if (bpf_opc imm_h = 0 \<and> bpf_dst imm_h = 0 \<and> bpf_src imm_h = 0)
    then
      case u4_to_bpf_ireg dst of
        None \<Rightarrow> None |
        Some d \<Rightarrow> Some (BPF_LD_IMM d imm (bpf_imm imm_h))
    else None)"

fun disassemble_one_instruction :: "ebpf_binary \<Rightarrow> bpf_instruction option" where
"disassemble_one_instruction bi = None" (**r TODO *)   
    
fun disassemble :: "ebpf_bin \<Rightarrow> ebpf_asm option" where
"disassemble [] = Some []" |
"disassemble (h#t) = (
  if bpf_opc h = 0x18 then
    case t of
    [] \<Rightarrow> None |
    (h1#t1) \<Rightarrow> (
      case disassemble_lddw (bpf_dst h) (bpf_imm h) h1 of
      None \<Rightarrow> None |
      Some ins \<Rightarrow> (
        case disassemble t1 of
        None \<Rightarrow> None |
        Some t2 \<Rightarrow> Some (ins#t2)))
  else
    case disassemble_one_instruction h of
    None \<Rightarrow> None |
    Some ins \<Rightarrow> (
      case disassemble t of
      None \<Rightarrow> None |
      Some t2 \<Rightarrow> Some (ins#t2)) )"