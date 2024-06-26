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


type_synonym u4 = "4 word"

record ebpf_binary =
bpf_opc :: u8
bpf_dst :: u4
bpf_src :: u4
bpf_off :: i16
bpf_imm :: i32

type_synonym ebpf_bin = "ebpf_binary list"

end