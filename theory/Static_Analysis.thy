section \<open> Static Analysis of Solana rBPF \<close>

theory Static_Analysis
imports
  Main
  rBPFCommType rBPFSyntax Assembler Disassembler
begin

text \<open> We skip this module firstly,
  as the current static analysis of Solana rBPF is just a test of JIT compiler \<close>

record TopologicalIndex =
scc_id    :: nat
discovery :: nat


record CfgNode =
label               :: string
sources             :: "nat list"
destinations        :: "nat list"
instructions        :: "nat * nat" (* low_range * high_range *)
topo_index          :: TopologicalIndex
dominator_parent    :: nat
dominated_children  :: "nat list"


end