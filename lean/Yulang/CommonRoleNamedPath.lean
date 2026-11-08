import Yulang.CommonRoleStatefulPathParent
import Yulang.CommonRoleSourceDescent

/-! A finite named path computes its occurrence slots and identity constraints.
The input is not a general source program or a dynamically generated graph. -/
namespace Yulang.CommonRoleNamedPath
open CommonRoleSourceIdentity (Table Slot Coherent)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

def table (seed : Nat) (names : List Nat) : Table := seed :: names

def receiver (seed : Nat) (names : List Nat) : Slot (table seed names) := ⟨0, by simp [table]⟩

def outputs (seed : Nat) (names : List Nat) : List (Slot (table seed names)) :=
  (List.finRange (table seed names).length).filter fun slot => slot.val != 0

theorem output_exact (seed : Nat) (names : List Nat) (slot : Slot (table seed names)) :
    slot ∈ outputs seed names ↔ slot.val ≠ 0 := by simp [outputs]

theorem slot_covered (seed : Nat) (names : List Nat) (slot : Slot (table seed names)) :
    slot = receiver seed names ∨ slot ∈ outputs seed names := by
  by_cases zero : slot.val = 0
  · exact Or.inl (Fin.ext zero)
  · exact Or.inr ((output_exact seed names slot).mpr zero)

theorem seed_identity (seed : Nat) (names : List Nat) :
    CommonRoleSourceIdentity.source (table seed names) (receiver seed names) = seed := rfl

def expected (seed : Nat) (names : List Nat) (s : State (table seed names).length) :
    State (table seed names).length :=
  CommonRoleStatefulIndexPath.expected (outputs seed names)
    (CommonRoleCandidateStateFrontier.extend (CommonRoleSourceIdentity.extend (table seed names) s)
      (receiver seed names) .str)

theorem expected_models (seed : Nat) (names : List Nat) (s : State (table seed names).length)
    (values : Slot (table seed names) → Comp Common.model) :
    All Common.model values (expected seed names s).atoms ↔
      All Common.model values s.atoms ∧ Coherent (table seed names) values ∧
        ∀ slot, Common.Equivalent (values slot).1 (.base .str) := by
  unfold expected
  rw [CommonRoleStatefulIndexPath.expected_models,
    CommonRoleCandidateStateFrontier.extend_exact, CommonRoleSourceIdentity.extend_exact]
  constructor
  · rintro ⟨⟨⟨old, coherent⟩, root⟩, rest⟩
    refine ⟨old, coherent, ?_⟩
    intro slot
    rcases slot_covered seed names slot with eq | member
    · simpa [eq] using root
    · exact rest slot member
  · rintro ⟨old, coherent, all⟩
    exact ⟨⟨⟨old, coherent⟩, all _⟩, fun slot _ => all slot⟩

def run (seed : Nat) (names : List Nat) (s : State (table seed names).length) :=
  CommonRoleStatefulPathParent.run (outputs seed names) (receiver seed names)
    (CommonRoleSourceIdentity.extend (table seed names) s)

def Final (seed : Nat) (names : List Nat) (s out : State (table seed names).length)
    (argument : Roles.Term) (answer : RoleDictionaries.Answer) : Prop :=
  out = expected seed names s ∧ out.Models ∧ argument = Roles.Examples.str ∧
    ∃ dictionary : RoleDictionaries.Dictionary CommonRoleStatefulParentExample.visible
        (CommonRoleStatefulParentExample.parentGoal Roles.Examples.str),
      answer = .resolved dictionary.erase

/-- Actual computed slots and identity atoms; no caller-supplied allocation map. -/
theorem outer_exact (seed : Nat) (names : List Nat) (s out : State (table seed names).length)
    (argument : Roles.Term) (answer : RoleDictionaries.Answer) :
    run seed names s = some (out, argument, answer) ↔ Final seed names s out argument answer :=
  CommonRoleStatefulPathParent.outer_exact ..

/-- The final ordinary model genuinely descends to source names, not just occurrence slots. -/
theorem source_factorization (seed : Nat) (names : List Nat)
    (s out : State (table seed names).length) (argument : Roles.Term)
    (answer : RoleDictionaries.Answer) (result : run seed names s = some (out, argument, answer))
    (values : Slot (table seed names) → Comp Common.model)
    (model : All Common.model values out.atoms) :
    All Common.model values s.atoms ∧
      ∃ sourceValues, CommonRoleSourceDescent.Factors (table seed names) values sourceValues ∧
        ∀ slot, Common.Equivalent (sourceValues (CommonRoleSourceIdentity.source (table seed names) slot))
          (.base .str) := by
  obtain ⟨rfl, _, _, _⟩ := (outer_exact ..).mp result
  obtain ⟨old, coherent, all⟩ := (expected_models seed names s values).mp model
  let sourceValues := CommonRoleSourceDescent.descend (table seed names) values (.base .int)
  have factor := CommonRoleSourceDescent.descend_factors (table seed names) values (.base .int) coherent
  refine ⟨old, sourceValues, factor, ?_⟩
  intro slot
  exact Common.equivalent_trans (Common.equivalent_symm (factor slot)) (all slot)

/-- The independent success domain mentions only old constraints and constant type equations.
Effects in the old constraints remain unconstrained by the path. -/
theorem success_domain (seed : Nat) (names : List Nat) (s : State (table seed names).length) :
    (∃ out argument answer, run seed names s = some (out, argument, answer)) ↔
      ∃ values : Slot (table seed names) → Comp Common.model,
        All Common.model values s.atoms ∧
        ∀ slot, Common.Equivalent (values slot).1 (.base .str) := by
  constructor
  · rintro ⟨out, argument, answer, result⟩
    obtain ⟨rfl, ⟨values, model⟩, _, _⟩ := (outer_exact ..).mp result
    obtain ⟨old, _, all⟩ := (expected_models seed names s values).mp model
    exact ⟨values, old, all⟩
  · rintro ⟨values, old, all⟩
    have coherent : Coherent (table seed names) values := by
      intro a b _
      exact Common.equivalent_trans (all a) (Common.equivalent_symm (all b))
    have model := (expected_models seed names s values).mpr ⟨old, coherent, all⟩
    exact ⟨_, _, _, CommonRoleStatefulPathParent.run_of_models _ _ _ ⟨values, model⟩⟩

/-- Every finite named path from an empty ordinary state succeeds; repeated names are allowed. -/
theorem empty_success (seed : Nat) (names : List Nat) :
    ∃ out argument answer, run seed names (State.empty) = some (out, argument, answer) := by
  apply (success_domain seed names State.empty).mpr
  refine ⟨CommonRoleStatefulIndexPath.strAssignment, PresenceNormalForm.all_nil _ _, ?_⟩
  intro slot
  exact Common.equivalent_refl _

/-- Old inconsistency is not hidden by materialization or the final dictionary. -/
theorem rejects_inconsistent (seed : Nat) (names : List Nat)
    (s : State (table seed names).length) (bad : ¬ s.Models) : run seed names s = none := by
  cases result : run seed names s with
  | none => rfl
  | some resultValue =>
    rcases resultValue with ⟨out, argument, answer⟩
    obtain ⟨values, old, _⟩ := (success_domain seed names s).mp ⟨out, argument, answer, result⟩
    exact False.elim (bad ⟨values, old⟩)

end Yulang.CommonRoleNamedPath
