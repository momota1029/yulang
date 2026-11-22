import Yulang.GeneralDeclarativeNativeRead347
import Yulang.GeneralDeclarativeFreshValues343
import Yulang.GeneralDeclarativeInitialRoot343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 22000000
namespace Yulang.GeneralDeclarativeNativeRoot347
open GeneralLiveCompoundPost316 (raw)
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralLiveCompoundUpperSnapshot316 (desc)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot)
open GeneralDeclarativeInitialRoot343 (InputOrigin anchored support source_backed)
open GeneralDeclarativeObservedSyntax347 (nominalPoint nominal_point_sound)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (restriction backed_iff)

theorem actual_root : nominalPoint raw 0 = some publicRow := by
  have locate : sourceSlot raw.base 0 = some (0 : Fin 8) := (sourceSlot_exact ..).mpr rfl
  have saved : raw.nominals (0 : Fin 8) = some desc := rfl
  have literal : GeneralStoppedShape335.descriptorExpr raw.base desc = some publicRow.right := rfl
  simp [nominalPoint,locate,saved,literal,publicRow]

theorem actual_source (done : Nat → Prop) :
    nominalPoint raw 0 = some publicRow ∧ InputOrigin publicRow ∧
    publicRow ∈ (restriction (support done)).equations :=
  ⟨actual_root,anchored,(backed_iff _ _).mpr (source_backed done)⟩

theorem starting_model (m : Assignment) (fit : Models after m) :
    GeneralDeclarativeHead320.Models observedRoot m := by
  refine ⟨⟨(by intro _ h; cases h),(by intro _ h; cases h)⟩,?_⟩
  intro row present
  cases List.mem_singleton.mp present
  exact nominal_point_sound actual_root m fit.1.1

theorem output_holds (m : Assignment) (fit : Models after m) : Holds m ownerOutput := by
  have historical := (GeneralLiveCompoundPostFeedback316.old_valid m fit).2.1
    GeneralDictionaryCompoundObstruction238.oldPlan GeneralDictionaryCompoundPoint238.original_plan_retained
  have output := GeneralDictionaryCompoundObstruction238.associated_value m historical
  change CommonNominalFullCarrier.Equivalent (m 4).1 GeneralDictionaryOptionalOutput229.value
  exact output

end Yulang.GeneralDeclarativeNativeRoot347
