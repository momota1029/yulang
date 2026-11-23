import Yulang.GeneralDeclarativeWitnessPlannedComparison359

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000000
namespace Yulang.GeneralDeclarativeWitnessNoInstallation359
open GeneralDeclarativeWitnessPlannedComparison359
  (Plan allFrames trial firstWrite output_descriptor_keeps_context)
open GeneralDeclarativeWitnessAssociatedFixture359 (available request)
open GeneralDeclarativeWitnessJointObservation359 (parentScope secondScope)
open GeneralDeclarativeWitnessNominalRecordFixture359
  (current exactAtoms route last genuine common_source_model generated_checks_follow_from_authored_base)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives compiled_full_exact)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open CommonNominalFullCarrier (Subtype Equivalent)
open PresenceNormalForm (Atom)

def varying (base : Inference.Base) : Assignment := fun slot =>
  if slot = 101 then (.base base,Common.rowEmpty) else genuine false true slot

theorem target_not_in_current_footprint : 101 ∉ stateNames current := by decide +kernel

theorem either_target_fits (base : Inference.Base) : Models current (varying base) := by
  apply (preserves_models current (first := genuine false true) (last := varying base) ?_).mp
    (common_source_model false true)
  intro n used
  have apart : n ≠ 101 := fun equal => target_not_in_current_footprint (equal ▸ used)
  simp [varying,apart]

theorem changed_target_is_distinguishable :
    ¬ Equivalent (varying .int 101).1 (varying .bool 101).1 := by
  intro wrong
  have seen := (CommonNominalFullModelMap.subtype_exact (.base .bool) (.base .int)).mp wrong.2
  have falseType := (CommonRigidHeadInspection.base_iff .bool .int).mp seen
  cases falseType

/-- A real compared plan fixes syntax/name/position, but not the value
at an uninstalled target. Both models fit the same state and exactly the
same executable output-description comparison, while target 101 differs. -/
theorem exact_comparison_does_not_install (negative : Bool) :
    ∃ (e : Environment) (a : Plan e table allFrames parentScope secondScope request
      (firstWrite negative) last (route negative 81)),
      available negative = some e ∧ trial e negative = some a ∧
      (∀ base,Models current (varying base) ∧
        ContextDerives table (varying base) false a.produced.endpoint a.expected.endpoint) ∧
      ¬Equivalent (varying .int 101).1 (varying .bool 101).1 := by
  have got := output_descriptor_keeps_context negative
  cases loaded : available negative with
  | none => rw [loaded] at got; cases got
  | some e =>
    rw [loaded] at got
    change (trial e negative).map (fun a => a.comparison.rows) = _ at got
    cases check : trial e negative with
    | none => simp [check] at got
    | some a =>
      have same : a.comparison.rows = exactAtoms := by simpa [check] using got
      refine ⟨e,a,rfl,check,?_,changed_target_is_distinguishable⟩
      intro base
      have state := either_target_fits base
      have every atom (used : atom ∈ a.comparison.rows) :=
        generated_checks_follow_from_authored_base _ state atom (same ▸ used)
      exact ⟨state,((compiled_full_exact table (varying base) false _ _).mp
        ⟨a.comparison.rows,a.comparison.exact,every⟩).2.2⟩

end Yulang.GeneralDeclarativeWitnessNoInstallation359
