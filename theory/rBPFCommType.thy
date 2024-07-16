theory rBPFCommType
imports
  Main
  "Word_Lib.Signed_Words"
begin
type_synonym u8 = "8 word"
type_synonym i16 = "16 sword"
type_synonym u16 = "16 word"
type_synonym i32 = "32 sword"
type_synonym u32 = "32 word"
type_synonym i64 = "64 sword"
type_synonym u64 = "64 word"
type_synonym u128 = "128 word"

type_synonym usize = "64 word" \<comment> \<open> Assume the hardware is 64-bit \<close>

definition i32_MIN :: "i32" where
"i32_MIN = 0x80000000"

definition i32_MAX :: "i32" where
"i32_MAX = 0x7FFFFFFF"

definition u32_MAX :: "u32" where
"u32_MAX = 0xFFFFFFFF"

definition u64_MAX :: "u64" where
"u64_MAX = 0xFFFFFFFFFFFFFFFF"


type_synonym u4 = "4 word"

record ebpf_binary =
bpf_opc :: u8
bpf_dst :: u4
bpf_src :: u4
bpf_off :: i16
bpf_imm :: i32

type_synonym ebpf_bin = "ebpf_binary list"

consts INSN_SIZE::usize

definition INSN_SIZE_def :: "usize" where
"INSN_SIZE_def = 8"

end