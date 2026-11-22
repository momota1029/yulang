import Yulang.GeneralDeclarativeWitnessMixedModel352

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 19000000
namespace Yulang.GeneralDeclarativeWitnessMixedControls352
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWitnessMixedFixture352
open GeneralDeclarativeWitnessMixedForest352 (Code)
open GeneralDeclarativeWitnessTagElection352 (Ends)
open GeneralDeclarativeWitnessTagBranch352 (Wire)
open GeneralDeclarativeWitnessAllocation350 (names)
open GeneralDeclarativeWitnessOrderedFixture350 (root q0 q1)
open GeneralDeclarativeWitnessForest350 (Fixed)

def literalInstead : Ends :=
  .literal ⟨2,.order ⟨.constraint 2,.constraint 3⟩⟩ ⟨3,.order ⟨.constraint 4,.constraint 5⟩⟩

def firstTagged (update : Wire → Wire) : Code → Code
  | .node top (.cons (.node (.tagged first) children) tail) =>
    .node top (.cons (.node (.tagged (update first)) children) tail)
  | other => other

theorem accepts_no_literal_laundering :
    test answer (firstTagged (fun w => {w with currentReads := literalInstead})) = false := by decide +kernel

theorem current_read_not_replaceable_by_earlier_recipe :
    test answer (firstTagged (fun w => {w with currentBounds := ⟨.constraint 1,.constraint 0⟩})) = false := by
  decide +kernel

theorem wrong_slot_change_not_coalesced :
    test answer (firstTagged (fun w => {w with namedSlots := [(0,50,86,52)]})) = false := by
  decide +kernel

theorem no_rank_assumption_from_source :
    test answer (firstTagged (fun w => {w with rank := []})) = false := by decide +kernel

theorem genuine_separate_child_captures :
    ((childContext [0] q0 child0).map (fun c => decide (names c.spans = [(0,50,56,52)]))).getD false = true ∧
    ((childContext [1] q1 child1).map (fun c => decide (names c.spans = [(0,80,86,82)]))).getD false = true := by
  decide +kernel

def exactOrdinals : Bool := (do
  let (s,code) ← data
  let yes ← GeneralDeclarativeWitnessMixedWhole352.decode (problem s) root code answer
  pure (decide (yes.diagnostic.fixed.map Fixed.path = [[],[0],[1]] ∧
    yes.diagnostic.fixed.map (fun f => f.demand.role) = [1,3,4])) : Option Bool).getD false

theorem genuine_trace_paths : exactOrdinals = true := by decide +kernel

end Yulang.GeneralDeclarativeWitnessMixedControls352
