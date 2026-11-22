import Yulang.GeneralDeclarativeReplayStage348
import Yulang.GeneralDeclarativeNativePlacement347

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 31000
set_option maxHeartbeats 26000000
namespace Yulang.GeneralDeclarativeReplayCompile348
open GeneralDeclarativeReplayStage348 (phase capture)
open GeneralDeclarativeNativeRepeatStage347 (spans fallback)
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

noncomputable abbrev protect (keep : List Nat) := stateNames (phase keep) ++ keep
noncomputable abbrev inputs (keep : List Nat) := prepared (phase keep) (protect keep) (capture keep) jobs
noncomputable abbrev logicalArg (keep : List Nat) := GeneralDeclarativeSparseWhere325.atPosition (seed (phase keep) (protect keep) (capture keep) jobs) jobs 0
noncomputable abbrev output (keep : List Nat) := appendFacts (inputs keep) [ownerOutput]
noncomputable abbrev child (keep : List Nat) : GeneralDeclarativeDemand320.Demand := ⟨1,[logicalArg keep],[]⟩
noncomputable abbrev port (keep : List Nat) := GeneralDeclarativeClauseBatch327.make (phase keep) (protect keep) (capture keep) otherChild [value]

theorem translated : GeneralNominalCenteredHeadMatExpressions.translateMany sourceRegistry.constructors interpretation
    (otherChild.arguments.map GeneralDeclarationPatterns.normalize) = some [value] := rfl

theorem batch (keep : List Nat) : prepare sourceRegistry.constructors interpretation (protect keep) (capture keep) (phase keep) declaration.requirements =
    some (inputs keep,[port keep]) := by
  change prepare sourceRegistry.constructors interpretation (protect keep) (capture keep) (phase keep) [otherChild] = _
  simp only [prepare]
  rfl

/-- This second replay uses the *literal original native declaration*,
including the repeated binder, not C319's distinct-binder prototype.
The root program and requested target are left unchanged. -/
theorem actual (keep : List Nat) :
    compileBody sourceRegistry interpretation (actualDemand rootPlan view) declaration observedRoot spans keep fallback targets =
      some (output keep,[child keep]) := by
  rw [exact_root]
  unfold compileBody
  change (do
    let (prepared,ports) ← prepare sourceRegistry.constructors interpretation (protect keep) (capture keep) (phase keep) declaration.requirements
    let place := placement declaration.requirements ports targets
    let named := sourceNames declaration place (capture keep)
    let ws ← GeneralDeclarativeWhereOutputBatch327.whole sourceRegistry interpretation declaration named targets
    let rs ← collect (one sourceRegistry interpretation declaration
      GeneralDeclarativeVersionedRootGuard342.actualDemand named.input) GeneralDeclarativeVersionedRootGuard342.actualDemand.outputs
    pure (appendFacts (appendFacts prepared ws) rs,children declaration named place)) = _
  rw [batch keep]
  have request : GeneralDeclarativeVersionedRootGuard342.actualDemand.outputs = [⟨0,4⟩] := original_targets
  simp only [request]
  rfl

end Yulang.GeneralDeclarativeReplayCompile348
