import Yulang.GeneralDeclarativeStoppedCurrent340
import Yulang.GeneralNominalIntervalLaws

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
namespace Yulang.GeneralDeclarativeStoppedNominalNoPoint340
open GeneralDictionaryCompoundVersionedModel238 (extended)
open GeneralDictionaryCompoundStep238 (installed_model)
open GeneralDeclarativeStoppedCurrent340 (fixtureView fixture_projected nonpoint_table)
open GeneralDeclarativeStoppedProjection340 (exact_models Models)
open GeneralDeclarativeStoppedIntervals340 (Holds)
open CommonNominalFullCarrier (Equivalent nominal emptyRecord nominal_regular_invariant_exact)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm)

theorem literal_values :
    (extended 0).1 = nominal 0 [.inl emptyRecord,.inl emptyRecord] ∧
    (extended 4).1 = GeneralDictionaryOptionalOutput229.value := by
  rw [GeneralDictionaryCompoundVersionedModel238.old_value 0 (by decide +kernel),
    GeneralDictionaryCompoundVersionedModel238.old_value 4 (by decide +kernel)]
  unfold GeneralDictionaryCompoundVersionedModel238.baseModel
  rw [GeneralDictionaryCompoundModel238.old_value 0 (by decide +kernel),
    GeneralDictionaryCompoundModel238.old_value 4 (by decide +kernel)]
  exact ⟨rfl,rfl⟩

/-- The actual fitting C238 installed assignment is lost if the
nonpoint invariant is arbitrarily compiled using its lower endpoint.
The symbolic side table retains it. -/
theorem lower_not_representative :
    Models fixtureView extended ∧
    Holds extended GeneralDeclarativeStoppedCurrent340.nonpoint ∧
    ¬ Equivalent (extended 0).1 (nominal 0 [.inl (extended 4).1,.inl (extended 4).1]) := by
  have yes := (exact_models _ extended fixture_projected).mpr installed_model.1.1
  refine ⟨yes,yes.2 _ nonpoint_table,?_⟩
  rw [literal_values.1,literal_values.2]
  intro wrong
  have inside := (nominal_regular_invariant_exact ..).mp wrong.1
  have different := inside.2.2 0 (.inl emptyRecord) (.inl GeneralDictionaryOptionalOutput229.value) rfl rfl
  exact GeneralDictionaryOptionalOutput229.not_width (eqv_symm different)

end Yulang.GeneralDeclarativeStoppedNominalNoPoint340
