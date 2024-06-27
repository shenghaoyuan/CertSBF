theory ConsistencyCommProof
imports
  Main
  rBPFCommType rBPFSyntax Assembler Disassembler
begin

lemma u4_breg_0 [simp]: "u4_to_bpf_ireg 0 = Some BR0"
  apply (unfold u4_to_bpf_ireg_def)
  apply auto
  done

declare if_split_asm [split] (**r register the lemma into split  *)

lemma u4_breg_i64 [simp]: "u4_to_bpf_ireg (bpf_dst x1) = Some aa \<Longrightarrow> (bpf_ireg2u4 aa) = (ucast (bpf_dst x1))"
  by (unfold u4_to_bpf_ireg_def, auto) (**r simp add: split: if_split_asm *)
(**r auto/simpl loads `split` *)


lemma  bpf_ireg_i64_same [simp]: "u4_to_bpf_ireg (bpf_ireg2u4 x1) = Some x1"
  by (cases "x1"; auto simp add: u4_to_bpf_ireg_def)
(**r auto apply to all goals, simp only apply for the first one *)

lemma bpf_ireg2u4_range [simp]: "0 \<le> bpf_ireg2u4 x2 \<and> bpf_ireg2u4 x2 \<le> 10"
  by (cases x2; auto)

lemma u4_to_bpf_ireg_dst_some_range [simp]: "u4_to_bpf_ireg (bpf_dst a) = Some ab \<Longrightarrow> 10 < bpf_dst a \<Longrightarrow> False"
  by (cases ab, auto simp add: u4_to_bpf_ireg_def)

lemma u4_to_bpf_ireg_src_some_range [simp]: "u4_to_bpf_ireg (bpf_src a) = Some ab \<Longrightarrow> 10 < bpf_src a \<Longrightarrow> False"
  by (cases ab, auto simp add: u4_to_bpf_ireg_def)

lemma bpf_opc_simp[simp]:  "(bpf_opc
                 \<lparr>bpf_opc = x1,
                    bpf_dst = x2,
                    bpf_src = x3,
                    bpf_off = x4, bpf_imm = x5\<rparr> = x1)" by fastforce

lemma bpf_dst_simp[simp]:  "(bpf_dst
                 \<lparr>bpf_opc = x1,
                    bpf_dst = x2,
                    bpf_src = x3,
                    bpf_off = x4, bpf_imm = x5\<rparr> = x2)" by fastforce

lemma bpf_src_simp[simp]:  "(bpf_src
                 \<lparr>bpf_opc = x1,
                    bpf_dst = x2,
                    bpf_src = x3,
                    bpf_off = x4, bpf_imm = x5\<rparr> = x3)" by fastforce

lemma bpf_off_simp[simp]:  "(bpf_off
                 \<lparr>bpf_opc = x1,
                    bpf_dst = x2,
                    bpf_src = x3,
                    bpf_off = x4, bpf_imm = x5\<rparr> = x4)" by fastforce

lemma bpf_imm_simp[simp]:  "(bpf_imm
                 \<lparr>bpf_opc = x1,
                    bpf_dst = x2,
                    bpf_src = x3,
                    bpf_off = x4, bpf_imm = x5\<rparr> = x5)" by fastforce

(*
lemma scast_scast_id:
  "scast (scast x :: ('a::len) signed word) = (x :: 'a word)"
  "scast (scast y :: ('a::len) word) = (y :: 'a signed word)"
  by (auto simp: is_up scast_up_scast_id)

declare scast_scast_id[simp del]

lemma "scast (scast x12::i32) = (x12::u32) "
  apply (rule scast_scast_id(1))
  
  by (auto simp add: scast_scast_id) *)
declare if_split_asm [split del]
end