import Yulang.CommonRoleOrdinaryKnownness
import Yulang.CommonRoleAssociatedParentGround

/-! A composed finite entry: actual associated declaration -> ordinary state
solver -> evidence-based receiver materialization -> actual parent dictionary.
The explicit output-to-parent binding is part of this small entry, not an
automatic parser/lowering theorem for arbitrary Parent where annotations. -/
namespace Yulang.CommonRoleAssociatedParentPipeline
open CommonRoleAssociatedParentGround
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

/-- The source binding connects Right.value to the Parent parameter slot 0.
Generated ordinary atoms are internal; the caller supplies only the old state. -/
def run (s : State 1) : Option (State 1 × Roles.Term × RoleDictionaries.Answer) :=
  match CommonRoleAssociatedStateFlow.fromSourceStore
    rightEnvironment rightRoles right_wellFormed request s with
  | none => none
  | some out =>
      if CommonRoleOpenPropagation.consistent out then
        match CommonRoleOrdinaryKnownness.materialize out.atoms 0 with
        | none => none
        | some argument => some (out, argument,
            RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal argument))
      else none

/-- Every successful entry preserves all original constraints and has a real
ordinary model. Materialization is sound in EVERY such model, not a chosen one. -/
theorem run_models (s out : State 1) (argument : Roles.Term) (answer : RoleDictionaries.Answer)
    (result : run s = some (out, argument, answer)) :
    out.Models ∧
    (∀ valuation : Fin 1 → Comp Common.model,
      All Common.model valuation out.atoms →
        All Common.model valuation s.atoms ∧
        Common.Equivalent (valuation (0 : Fin 1)).1 (.base .int) ∧
        ∃ base, CommonRoleAssociatedStateFlow.scalar argument = some base ∧
          Common.Equivalent (valuation (0 : Fin 1)).1 (.base base)) := by
  unfold run at result
  cases produced : CommonRoleAssociatedStateFlow.fromSourceStore
      rightEnvironment rightRoles right_wellFormed request s with
  | none => simp [produced] at result
  | some next =>
    simp only [produced] at result
    by_cases yes : CommonRoleOpenPropagation.consistent next = true
    · simp only [yes, ↓reduceIte] at result
      cases materialized : CommonRoleOrdinaryKnownness.materialize next.atoms (0 : Fin 1) with
      | none => simp [materialized] at result
      | some value =>
        simp only [materialized, Option.some.injEq, Prod.mk.injEq] at result
        obtain ⟨rfl, rfl, rfl⟩ := result
        refine ⟨(CommonRoleOpenPropagation.consistent_exact _).mp yes, ?_⟩
        intro valuation model
        have source := produced
        rw [CommonRoleAssociatedStateFlow.source_store_agrees] at source
        have exactness := CommonRoleAssociatedStateFlow.models_exact rightEnvironment rightRoles
          right_wellFormed request s next .int equation_from_declaration source valuation
        exact ⟨(exactness.mp model).1, (exactness.mp model).2,
          CommonRoleOrdinaryKnownness.materialize_sound next.atoms 0 value materialized valuation model⟩
    · have no := Bool.eq_false_iff.mpr yes
      simp [no] at result

/-- Generated state in the concrete empty-source example; not a caller-provided atom list. -/
def resultState : State 1 := CommonRoleCandidateStateFrontier.extend State.empty 0 .int

theorem produced_state : CommonRoleAssociatedStateFlow.fromSourceStore
    rightEnvironment rightRoles right_wellFormed request State.empty = some resultState := by
  rw [CommonRoleAssociatedStateFlow.source_store_agrees]
  have value := (CommonRoleAssociatedStateFlow.value_exact ..).mpr equation_from_declaration
  simp only [CommonRoleAssociatedStateFlow.produce, value, Option.map_some]
  rfl

theorem result_consistent : CommonRoleOpenPropagation.consistent resultState = true := by
  apply (CommonRoleOpenPropagation.consistent_exact _).mpr
  refine ⟨fun _ => Comp.pure Common.model (.base .int), ?_⟩
  apply (CommonRoleCandidateStateFrontier.extend_exact ..).mpr
  exact ⟨PresenceNormalForm.all_nil _ _, Common.equivalent_refl _⟩

theorem result_materialized :
    CommonRoleOrdinaryKnownness.materialize resultState.atoms (0 : Fin 1) = some Roles.Examples.int := by
  unfold CommonRoleOrdinaryKnownness.materialize
  rw [show CommonRoleOrdinaryKnownness.detect resultState.atoms (0 : Fin 1) = some .int from
    CommonRoleOrdinaryKnownness.explicit_pair_detected 0 .int]
  rfl

/-- Real declaration-generated equations, solver, and dictionary at one outer entry.
The example has a known Right-str receiver; it is not the unspecified Right-a example. -/
theorem empty_source_result :
    ∃ plan, run State.empty = some (resultState, Roles.Examples.int, .resolved plan) ∧
      (∀ implementation ∈ plan.declarations, implementation ∈ visible) ∧
      (∀ valuation : Fin 1 → Comp Common.model,
        All Common.model valuation resultState.atoms →
          Common.Equivalent (valuation (0 : Fin 1)).1 (.base .int)) := by
  let dictionary := RoleDictionaries.buildResolved visible declarations_wellFormed
    (parentGoal Roles.Examples.int) parent_int_resolved
  have answer := (RoleDictionaries.elaborate_success_iff visible declarations_wellFormed
    (parentGoal Roles.Examples.int) dictionary.erase).mpr ⟨dictionary, rfl⟩
  refine ⟨dictionary.erase, ?_, dictionary.all_visible, ?_⟩
  · simp only [run, produced_state, result_consistent, ↓reduceIte, result_materialized, answer]
  · intro valuation models
    exact ((CommonRoleCandidateStateFrontier.extend_exact ..).mp models).2

end Yulang.CommonRoleAssociatedParentPipeline
