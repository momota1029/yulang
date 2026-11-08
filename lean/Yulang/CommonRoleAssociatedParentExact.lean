import Yulang.CommonRoleAssociatedParentSuccess

/-! Exact success domain of the fixed declaration-driven Parent example.
This is not general source inference or a final classification of none. -/
namespace Yulang.CommonRoleAssociatedParentExact
open CommonRoleAssociatedParentPipeline
open CommonRoleAssociatedParentGround
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

abbrev extended (s : State 1) : State 1 := CommonRoleCandidateStateFrontier.extend s 0 .int

theorem source_generated (s : State 1) :
    CommonRoleAssociatedStateFlow.fromSourceStore
      rightEnvironment rightRoles right_wellFormed request s = some (extended s) := by
  rw [CommonRoleAssociatedStateFlow.source_store_agrees]
  have value := (CommonRoleAssociatedStateFlow.value_exact ..).mpr equation_from_declaration
  simp only [CommonRoleAssociatedStateFlow.produce, value, Option.map_some]
  rfl

theorem materialized_int (s : State 1) (models : (extended s).Models) :
    CommonRoleOrdinaryKnownness.materialize (extended s).atoms (0 : Fin 1) =
      some Roles.Examples.int := by
  have evidence : CommonRoleOrdinaryKnownness.Evidence (extended s).atoms (0 : Fin 1) .int := by
    constructor <;> simp [extended, CommonRoleCandidateStateFrontier.extend,
      CommonRoleCandidateStateFrontier.equality]
  obtain ⟨base, found⟩ := (CommonRoleOrdinaryKnownness.detect_exists (extended s).atoms 0).mpr
    ⟨.int, evidence⟩
  obtain ⟨valuation, models⟩ := models
  have same := CommonRoleOrdinaryKnownness.evidence_unique (extended s).atoms 0 valuation models
    base .int (CommonRoleOrdinaryKnownness.detect_evidence _ _ _ found) evidence
  subst base
  simp [CommonRoleOrdinaryKnownness.materialize, found, CommonRoleOrdinaryKnownness.encode,
    Roles.Examples.int]

theorem run_of_models (s : State 1) (models : (extended s).Models) :
    run s = some (extended s, Roles.Examples.int,
      RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal Roles.Examples.int)) := by
  have yes := (CommonRoleOpenPropagation.consistent_exact _).mpr models
  simp only [run, source_generated, yes, ↓reduceIte, materialized_int s models]

/-- No success/knownness premise: existence of a compatible original model
is exactly the success domain of this fixed actual entry. -/
theorem success_exact (s : State 1) :
    (∃ out argument answer, run s = some (out, argument, answer)) ↔
      ∃ valuation : Fin 1 → Comp Common.model,
        All Common.model valuation s.atoms ∧
        Common.Equivalent (valuation (0 : Fin 1)).1 (.base .int) := by
  constructor
  · rintro ⟨out, argument, answer, result⟩
    obtain ⟨⟨valuation, model⟩, sound⟩ := run_models s out argument answer result
    obtain ⟨original, equal, _⟩ := sound valuation model
    exact ⟨valuation, original, equal⟩
  · rintro ⟨valuation, original, equal⟩
    have models : (extended s).Models :=
      ⟨valuation, (CommonRoleCandidateStateFrontier.extend_exact ..).mpr ⟨original, equal⟩⟩
    exact ⟨_, _, _, run_of_models s models⟩

theorem successful_state (s out : State 1) (argument : Roles.Term)
    (answer : RoleDictionaries.Answer) (result : run s = some (out, argument, answer)) :
    out = extended s := by
  obtain ⟨valuation, original, equal⟩ := (success_exact s).mp ⟨out, argument, answer, result⟩
  have models : (extended s).Models :=
    ⟨valuation, (CommonRoleCandidateStateFrontier.extend_exact ..).mpr ⟨original, equal⟩⟩
  have same := (run_of_models s models).symm.trans result
  exact (Prod.mk.inj (Option.some.inj same)).1.symm

end Yulang.CommonRoleAssociatedParentExact
