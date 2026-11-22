import Yulang.GeneralDeclarativeNativeCompound347
import Yulang.GeneralDeclarativeObservedSyntax347
import Yulang.GeneralDeclarativeNominalRevision347

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 25000000
namespace Yulang.GeneralDeclarativeNativeRead347
open GeneralLiveCompoundPost316 (raw)
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralLiveCompoundChildSite316 (childSite)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralDeclarativeObservedSyntax347 (structural)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeHead320 (Equation)
open CommonNominalFullCarrier (Equivalent Subtype variant)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)

abbrev low : Equation := ⟨lo,.variant 0 (.variable 4)⟩
abbrev high : Equation := ⟨hi,.variant 0 (.variable 2)⟩

theorem low_current_view : structural raw lo = some low := by
  have lookup : sourceSlot raw.base lo = some (5 : Fin 8) := (sourceSlot_exact ..).mpr rfl
  unfold structural
  rw [lookup]
  rfl

theorem high_current_view : structural raw hi = some high := by
  have lookup : sourceSlot raw.base hi = some (6 : Fin 8) := (sourceSlot_exact ..).mpr rfl
  unfold structural
  rw [lookup]
  rfl

theorem actual_names : childSite.occurrence.demand.arguments 0 = (lo,hi) := rfl

theorem exact_readings (m : Assignment) (fit : GeneralNominalVersionedJournal232.Models after m) :
    Holds m low ∧ Holds m high ∧
    Subtype (m lo).1 (m (childSite.center 0)).1 ∧ Subtype (m (childSite.center 0)).1 (m hi).1 := by
  obtain ⟨_,_,_,_,typed⟩ := GeneralDeclarativeNativeCompound347.exact_birth m fit
  rw [← show (m (childSite.occurrence.demand.arguments 0).1).1 = (m lo).1 from rfl,
      ← show (m (childSite.occurrence.demand.arguments 0).2).1 = (m hi).1 from rfl]
  exact ⟨GeneralDeclarativeObservedSyntax347.structural_sound low_current_view m fit.1.1,
    GeneralDeclarativeObservedSyntax347.structural_sound high_current_view m fit.1.1,typed 0⟩

/-- No endpoint equality is smuggled in via the genuine stored center.
The observed legacy lower operand still comes from source 4 and the
observed upper from 2; these remain different in every returned model. -/
theorem genuinely_nonpoint (m : Assignment) (fit : GeneralNominalVersionedJournal232.Models after m) :
    ¬ Equivalent (m lo).1 (m hi).1 := by
  intro bad
  obtain ⟨lower,upper,_,_⟩ := exact_readings m fit
  have eq : Equivalent (variant 0 (m 4).1) (variant 0 (m 2).1) :=
    eqv_trans (eqv_symm lower) (eqv_trans bad upper)
  have both := (GeneralDeclarativeExactWalk323.variant_exact 0 (m 4).1 (m 2).1).mp eq
  have legacy := GeneralLiveCompoundPostFeedback316.old_valid m fit
  have lifetime := legacy.2.1 GeneralDictionaryCompoundObstruction238.oldPlan
    GeneralDictionaryCompoundPoint238.original_plan_retained
  have value := GeneralDictionaryCompoundObstruction238.associated_value m lifetime
  have width := GeneralDictionaryJournalRefinement228Source.width_two m lifetime.1
  exact GeneralDictionaryOptionalOutput229.not_width (eqv_trans (eqv_symm value) (eqv_trans both width))

end Yulang.GeneralDeclarativeNativeRead347
