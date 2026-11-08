import Yulang.CommonRoleAssociatedParentPipeline

/-! Every successful result of the concrete declaration-driven Parent entry
has the int argument and a resolved dictionary using visible declarations.
No classification is assigned to the none branch. -/
namespace Yulang.CommonRoleAssociatedParentSuccess
open CommonRoleAssociatedParentPipeline
open CommonRoleAssociatedParentGround
open CommonRoleSettledConstraints (State)

private theorem scalar_int (term : Roles.Term)
    (decoded : CommonRoleAssociatedStateFlow.scalar term = some .int) :
    term = Roles.Examples.int := by
  cases term with
  | var => cases decoded
  | app name args =>
    cases name with
    | zero => cases args <;> simp_all [CommonRoleAssociatedStateFlow.scalar, Roles.Examples.int]
    | succ name =>
      cases name <;> cases args <;> simp_all [CommonRoleAssociatedStateFlow.scalar]

/-- The real model witness provided by run_models excludes scalar disagreement. -/
theorem argument_int (s out : State 1) (argument : Roles.Term) (answer : RoleDictionaries.Answer)
    (result : run s = some (out, argument, answer)) : argument = Roles.Examples.int := by
  obtain ⟨⟨valuation, models⟩, sound⟩ := run_models s out argument answer result
  obtain ⟨_, isInt, base, decoded, isBase⟩ := sound valuation models
  have equal : Inference.Base.int = base :=
    (CommonRigidHeadInspection.base_iff _ _).mp
      (Common.equivalent_trans (Common.equivalent_symm isInt) isBase).1
  subst base
  exact scalar_int argument decoded

theorem answer_elaborate (s out : State 1) (argument : Roles.Term) (answer : RoleDictionaries.Answer)
    (result : run s = some (out, argument, answer)) :
    answer = RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal argument) := by
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
        rfl
    · have no := Bool.eq_false_iff.mpr yes
      simp [no] at result

/-- Arbitrary starting ordinary states: success implies actual visible
Parent/Left/Right dictionary construction, not just a postulated answer tag. -/
theorem success_resolved (s out : State 1) (argument : Roles.Term)
    (answer : RoleDictionaries.Answer) (result : run s = some (out, argument, answer)) :
    argument = Roles.Examples.int ∧
      ∃ plan, answer = .resolved plan ∧
        ∀ implementation ∈ plan.declarations, implementation ∈ visible := by
  have argumentEq := argument_int s out argument answer result
  refine ⟨argumentEq, ?_⟩
  subst argument
  let dictionary := RoleDictionaries.buildResolved visible declarations_wellFormed
    (parentGoal Roles.Examples.int) parent_int_resolved
  have resolved := (RoleDictionaries.elaborate_success_iff visible declarations_wellFormed
    (parentGoal Roles.Examples.int) dictionary.erase).mpr ⟨dictionary, rfl⟩
  exact ⟨dictionary.erase, (answer_elaborate s out _ answer result).trans resolved,
    dictionary.all_visible⟩

end Yulang.CommonRoleAssociatedParentSuccess
