import Yulang.GeneralDeclarativeLogicalChild343

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 13300
set_option maxHeartbeats 1400000
namespace Yulang.GeneralDeclarativeOrdinary343
open GeneralDeclarativeLogicalChild343 (stage capture protect port arg child fallback targets output built batch port_zero)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot actualDemand)
open GeneralDeclarativeVersionedRootShape342 (spans)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput)
open GeneralWhereOriginSingleSource318 (sourceRegistry declaration)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralDeclarativeStableAssemble329 (merged)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeClauseBatch327 (prepare Port)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeAppliedClause327 (targetsOnly)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeEmissionForest322 (children)

theorem empty (s : State) : appendFacts s [] = s := by
  cases s
  simp [appendFacts]

theorem inputs (cap : Nat → Capture) :
    (sourceNames declaration (targetsOnly targets) cap).input = cap := rfl

theorem where_rows (cap : Nat → Capture) (ps : List Port) :
    GeneralDeclarativeWhereOutputBatch327.whole sourceRegistry interpretation declaration
      (sourceNames declaration (placement declaration.requirements ps targets) cap) targets = some [] := rfl

theorem emits (cap : Nat → Capture) (p : Port) :
    children declaration (sourceNames declaration (placement declaration.requirements [p] targets) cap)
      (placement declaration.requirements [p] targets) = [⟨1,[p.input 0],[]⟩] := rfl

theorem actual (keep : List Nat) :
    compileBody sourceRegistry interpretation actualDemand declaration observedRoot spans keep fallback targets =
      some (output keep,[child keep]) := by
  unfold compileBody
  change (do
    let (prepared,ports) ← prepare sourceRegistry.constructors interpretation (protect keep)
      (sourceNames declaration (targetsOnly targets) (capture keep)).input (stage keep) declaration.requirements
    let place := placement declaration.requirements ports targets
    let names := sourceNames declaration place (capture keep)
    let whereRows ← GeneralDeclarativeWhereOutputBatch327.whole sourceRegistry interpretation declaration names targets
    let rootRows ← GeneralDeclarativeBatch320.collect
      (GeneralDeclarativeNormalizeAssoc324.one sourceRegistry interpretation declaration actualDemand names.input) actualDemand.outputs
    pure (appendFacts (appendFacts prepared whereRows) rootRows,children declaration names place)) = _
  rw [inputs,batch]
  simp only [GeneralDeclarativeVersionedRootCompiler342.fixed_root]
  rfl

end Yulang.GeneralDeclarativeOrdinary343
