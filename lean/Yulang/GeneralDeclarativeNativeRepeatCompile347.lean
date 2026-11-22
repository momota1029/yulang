import Yulang.GeneralDeclarativeNativeRepeatStage347
import Yulang.GeneralDeclarativeNativePlacement347

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 31000
set_option maxHeartbeats 26000000
namespace Yulang.GeneralDeclarativeNativeRepeatCompile347
open GeneralDeclarativeNativeRepeatStage347 (spans fallback phase capture)
open GeneralDeclarativeNativeReplay347 (keep)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot original_targets)
open GeneralDeclarativeRootReplay344 (actualDemand)
open GeneralDeclarativeNativePlacement347 (exact_root)
open GeneralDeclarativeCurrentBarrier345 (view)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundRegistry316 (declaration sourceRegistry otherChild declaration_checked)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralDeclarativeLogicalChild343 (value targets jobs)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeClauseBatch327 (Port prepare)
open GeneralDeclarativeFreshInputs325 (prepared)
open GeneralDeclarativeFreshWhere325 (seed)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeAppliedClause327 (targetsOnly)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeEmissionForest322 (children)

noncomputable abbrev protect := stateNames phase ++ keep
noncomputable abbrev inputs := prepared phase protect capture jobs
noncomputable abbrev logicalArg := GeneralDeclarativeSparseWhere325.atPosition (seed phase protect capture jobs) jobs 0
noncomputable abbrev output := appendFacts inputs [ownerOutput]
noncomputable abbrev child : GeneralDeclarativeDemand320.Demand := ⟨1,[logicalArg],[]⟩
noncomputable abbrev port := GeneralDeclarativeClauseBatch327.make phase protect capture otherChild [value]

theorem translated : GeneralNominalCenteredHeadMatExpressions.translateMany sourceRegistry.constructors interpretation
    (otherChild.arguments.map GeneralDeclarationPatterns.normalize) = some [value] := rfl

theorem batch : prepare sourceRegistry.constructors interpretation protect capture phase declaration.requirements =
    some (inputs,[port]) := by
  change prepare sourceRegistry.constructors interpretation protect capture phase [otherChild] = _
  simp only [prepare]
  rfl

/-- This second replay uses the *literal original native declaration*,
including the repeated binder, not C319's distinct-binder prototype.
The root program and requested target are left unchanged. -/
theorem actual :
    compileBody sourceRegistry interpretation (actualDemand rootPlan view) declaration observedRoot spans keep fallback targets =
      some (output,[child]) := by
  rw [exact_root]
  unfold compileBody
  change (do
    let (prepared,ports) ← prepare sourceRegistry.constructors interpretation protect capture phase declaration.requirements
    let place := placement declaration.requirements ports targets
    let named := sourceNames declaration place capture
    let ws ← GeneralDeclarativeWhereOutputBatch327.whole sourceRegistry interpretation declaration named targets
    let rs ← collect (one sourceRegistry interpretation declaration
      GeneralDeclarativeVersionedRootGuard342.actualDemand named.input) GeneralDeclarativeVersionedRootGuard342.actualDemand.outputs
    pure (appendFacts (appendFacts prepared ws) rs,children declaration named place)) = _
  rw [batch]
  have request : GeneralDeclarativeVersionedRootGuard342.actualDemand.outputs = [⟨0,4⟩] := original_targets
  simp only [request]
  rfl

end Yulang.GeneralDeclarativeNativeRepeatCompile347
