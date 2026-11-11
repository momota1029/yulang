import Yulang.GeneralDictionaryStateEquations

/-!
# Non-vacuous shared-state equation regressions

This fixture exercises the general dictionary equation bridge. It is not a new
role classifier. The source carrier retains two named output occurrences; no
surface duplicate-annotation acceptance rule is inferred from that carrier.
-/
namespace Yulang.GeneralDictionaryEquationExamples
open GeneralSourceState
open GeneralDictionaryStateEquations
open Core.PresenceGeneration (TyTerm)

abbrev outputRole : Roles.RoleDecl :=
  ⟨1, fun name => if name = 0 then some none else none, by
    intro name rhs impossible
    split at impossible <;> cases impossible⟩
abbrev roles : Roles.RoleDecls := fun _ => outputRole

abbrev state : State where
  slots := 1
  source := fun _ => 10
  source_injective := by intro _ _ _; exact Subsingleton.elim _ _
  rowSource := fun _ => 20
  ordinary := equationAtoms 0 (.base .int)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := [(0, 0)]
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by
    intro assignment _ pair member
    have same := List.mem_singleton.mp member
    subst pair
    exact Common.subtype_refl _

abbrev demand : Demand roles where
  role := 0
  arguments := fun _ => (10, 10)
  outputs := List.replicate 2 ⟨0, 10⟩
  declared := by
    intro output member
    have same : output = ⟨0, 10⟩ := (List.mem_replicate.mp member).2
    subst output
    exact ⟨none, rfl⟩

private theorem output_target (index : Fin demand.outputs.length) :
    (demand.outputs[index]).target = 10 := by
  change ((List.replicate 2 (⟨0, 10⟩ : Output))[index.val]'_).target = 10
  simp only [List.getElem_replicate]

abbrev located : Located state demand where
  lower := fun _ => 0
  upper := fun _ => 0
  head := fun _ => .base .int
  target := fun _ => 0
  output := fun _ => .base .int
  arguments := fun _ => rfl
  targets := by intro index; exact output_target index

theorem recorded : Recorded located := by
  constructor <;> intro index <;> simp [state, equationAtoms]

abbrev assignment : Assignment := fun _ => (.base .int, Common.rowEmpty)

theorem models : Models state assignment := by
  apply (models_ordinary state assignment).mpr
  apply (equationAtoms_exact 0 (.base .int) (state.assignment assignment)).mpr
  exact Common.equivalent_refl _

/-- The universal theorem has a concrete satisfying instance, rather than only
an inconsistent ordinary state. Both repeated output occurrences are covered. -/
theorem all_model_outputs (model : Assignment) (valid : Models state model)
    (index : Fin demand.outputs.length) :
    Common.Equivalent (model 10).1 (.base .int) := by
  have equality := (recorded_holds located recorded model valid).2 index
  change Common.Equivalent (model (demand.outputs[index]).target).1 (.base .int) at equality
  rw [output_target] at equality
  exact equality

theorem duplicate_outputs_retained :
    demand.outputs.length = 2 ∧ located.equations.atoms.length = 6 := by
  constructor <;> rfl

/-- Reusing a local index in an arrow's type and effect positions does not
confuse global source IDs 10 and 20. -/
theorem separate_type_and_row_ids :
    liftType state (.arrow (.var 0) (.var 0) (.var 0) (.var 0)) =
      .arrow (.var 10) (.var 20) (.var 10) (.var 20) := rfl

end Yulang.GeneralDictionaryEquationExamples
