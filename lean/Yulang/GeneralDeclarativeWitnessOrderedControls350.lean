import Yulang.GeneralDeclarativeWitnessOrderedFixture350

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralDeclarativeWitnessOrderedControls350
open GeneralDeclarativeWitnessOrderedFixture350
open GeneralDeclarativeWitnessRecordReplay350 (Wire)
open GeneralDeclarativeWitnessForest350 (Code Codes)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeWitnessRecordWhole350 (check)

def run (changed : Code → Code) : Bool :=
  (problemAndCode.map (fun (p,w) => check p root (changed w) answer)).getD false

def atRoot (patch : Wire → Wire) : Code → Code
  | .node w rest => .node (patch w) rest

theorem wrong_reported_child_order :
    run (atRoot (fun w => {w with emitted :=
      {w.emitted with children := [printDemand q1,printDemand q0]}})) = false := by
  decide +kernel

theorem wrong_child_center :
    run (atRoot (fun w => {w with emitted := {w.emitted with children :=
      [printDemand {q0 with arguments := [⟨26,22,27⟩]},printDemand q1]}})) = false := by
  decide +kernel

theorem wrong_fixed_target :
    run (atRoot (fun w => {w with emitted := {w.emitted with outputRows := [⟨6,.variable 21⟩]}})) = false := by
  decide +kernel

/-- An equal payload in the concrete fixture is not the source
compiler's literal right-hand side. -/
theorem same_model_not_same_syntax :
    run (atRoot (fun w => {w with emitted := {w.emitted with outputRows := [⟨5,.variable 4⟩]}})) = false := by
  decide +kernel

theorem swapped_child_certificates :
    run (fun
      | .node w (.cons a (.cons b .nil)) => .node w (.cons b (.cons a .nil))
      | x => x) = false := by decide +kernel

theorem missing_required_child :
    run (fun
      | .node w (.cons a (.cons _ .nil)) => .node w (.cons a .nil)
      | x => x) = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessOrderedControls350
