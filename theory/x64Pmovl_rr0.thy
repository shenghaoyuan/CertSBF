theory x64Pmovl_rr0
imports
  Main
  rBPFCommType rBPFSyntax
  x64Assembler x64Disassembler
begin

lemma pmovl_rr_lemma0: "and 3 (rop >> 6) = 3 \<Longrightarrow>
    construct_rex_to_u8 False
     (and (bitfield_insert_u8 3 (Suc 0) (and 7 (rop >> 3)) 0) 8 \<noteq> 0) False
     (and (bitfield_insert_u8 3 (Suc 0) (and 7 rop) 0) 8 \<noteq> 0) =
    0 \<longrightarrow>
    construct_modsib_to_u8 3 (bitfield_insert_u8 3 (Suc 0) (and 7 (rop >> 3)) 0)
     (bitfield_insert_u8 3 (Suc 0) (and 7 rop) 0) =
    rop"
  
  
  sorry

end