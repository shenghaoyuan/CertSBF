theory Static_Analysis
imports
  Main
  "HOL.Bit_Operations" "HOL-Library.Word"
  rBPFCommType rBPFSyntax Assembler Disassembler
begin

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