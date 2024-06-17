theory Test
imports Main "HOL-Library.Word" 
begin


type_synonym u4 = "4 word"

datatype bpf_ireg = BR0 | BR1 | BR2 | BR3 | BR4 | BR5 | BR6 | BR7 | BR8 | BR9 | BR10

(* OK *)
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

(* Constructor way is OK, but if I want do case `200`, using Suc Suc ... is bad *)
definition nat_to_bpf_ireg_case :: "nat \<Rightarrow> bpf_ireg option" where
"nat_to_bpf_ireg_case dst =
  (case dst of
   0 \<Rightarrow> Some BR0 |
   (Suc 0) \<Rightarrow> Some BR1 |
   _ \<Rightarrow> None)"

(* NOT OK *)
definition u4_to_bpf_ireg_case :: "u4 \<Rightarrow> bpf_ireg option" where
"u4_to_bpf_ireg_case dst =
  (case dst of
   0 \<Rightarrow> Some BR0 |
   1 \<Rightarrow> Some BR1 |
   _ \<Rightarrow> None)"

(* NOT OK *)   
function u4_to_bpf_ireg_t :: "u4 \<Rightarrow> bpf_ireg option" where
"u4_to_bpf_ireg_t 0 = Some BR0" |
"u4_to_bpf_ireg_t 1 = Some BR1" |
"u4_to_bpf_ireg_t 2 = Some BR2" |
"u4_to_bpf_ireg_t 3 = Some BR3" |
"u4_to_bpf_ireg_t 4 = Some BR4" |
"u4_to_bpf_ireg_t 5 = Some BR5" |
"u4_to_bpf_ireg_t 6 = Some BR6" |
"u4_to_bpf_ireg_t 7 = Some BR7" |
"u4_to_bpf_ireg_t 8 = Some BR8" |
"u4_to_bpf_ireg_t 9 = Some BR9" |
"u4_to_bpf_ireg_t 10 = Some BR10" |
"u4_to_bpf_ireg_t _ = None"
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp

end