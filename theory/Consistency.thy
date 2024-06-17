theory Consistency
imports
  Main
  "HOL.Bit_Operations" "HOL-Library.Word"
  rBPFCommType rBPFSyntax Assembler Disassembler
begin

lemma assemble_disassemble_consistency: "assemble l_asm = Some l_bin \<Longrightarrow> disassemble l_bin = Some l_asm"
apply (induction l_asm)
apply simp

apply simp
(**TODO: case analysis *)
done

(**TODO: consistency between assemble and disassemble *)

end