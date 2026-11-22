import Yulang.GeneralDeclarativeWitnessTagCoreForest352
import Yulang.GeneralDeclarativeWitnessTaggedParentModel352
import Yulang.GeneralDeclarativeWitnessPathOrder352

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 24000000
namespace Yulang.GeneralDeclarativeWitnessTagCoreFixture352
open GeneralDeclarativeWitnessTagCoreForest352 (semantic_conclusion)
open GeneralDeclarativeWitnessTaggedParent352 (candidate root report)
open GeneralDeclarativeWitnessTaggedParentModel352 (nonvacuous model)
open GeneralDeclarativeHead320 (Models Equation)
open GeneralDeclarativeWitnessMixedForest352 (Problem Code)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)

def alsoCore : Bool :=
  (candidate.map fun (p,code) => GeneralDeclarativeWitnessTagCoreForest352.check p code report).getD false

theorem checks_original_semantic_conclusion : alsoCore = true := by decide +kernel

/-- The exact same source, report, scope and satisfying model witness
the two semantic conclusions; no equivalence of the classifiers follows. -/
theorem same_source_two_conclusions :
    ∃ (p : Problem) (code : Code) (a : GeneralDeclarativeWitnessMixedWhole352.Accepted p root report),
      candidate = some (p,code) ∧ Models p.current model ∧
      GeneralDeclarativeExactDictionary337.Evidence
        (registry a.global.table) (interpretation a.global.table.snapshot) model root
        (.node 92 [.node 93 [],.node 94 []]) ∧
      GeneralDeclarativeEvidence320.Evidence
        (registry a.global.table) (interpretation a.global.table.snapshot) model p.target
        (.node 92 [.node 93 [],.node 94 []]) := by
  obtain ⟨p,code,a,known,fit,modern,_⟩ := nonvacuous
  have good := checks_original_semantic_conclusion
  unfold alsoCore at good
  rw [known] at good
  obtain ⟨earlier,d,_,dict,_,allModels⟩ := semantic_conclusion good
  have same : earlier.global.table = a.global.table :=
    Option.some.inj (earlier.global.canonical.symm.trans a.global.canonical)
  cases (show CommonRoleOutermostResolver.Result.selected
      (.node 92 [.node 93 [],.node 94 []]) = .selected d from dict)
  have before := allModels model fit
  rw [same] at before
  exact ⟨p,code,a,known,fit,modern,before⟩

def reportsExactLocations : Bool := (do
  let (p,code) ← candidate
  let a ← GeneralDeclarativeWitnessMixedWhole352.decode p root code report
  let ordinals := a.diagnostic.fixed.map fun (f : Fixed) => (f.path,f.demand.role,f.equations.map Equation.left)
  pure (decide (ordinals = [([],1,[5]),([0],3,[]),([1],4,[])]))) |>.getD false

theorem exact_writes_at_exact_tree_positions : reportsExactLocations = true := by decide +kernel

end Yulang.GeneralDeclarativeWitnessTagCoreFixture352
