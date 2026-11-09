import Yulang.CommonRoleDirectedDiagnostic

/-! A directed sandwich with no direct scalar-equality seed. This regression
is an instance of the general directed-bound derivation, not a new language rule. -/
namespace Yulang.CommonRoleDirectedBoundsCheck
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (All Atom)
open CommonRoleSettledConstraints (State)
open CommonRoleDirectedBounds

def atoms : List (Atom (Fin 3)) :=
  [.tyLe (.base .int) (.var 0), .tyLe (.var 0) (.var 1),
   .tyLe (.var 1) (.var 2), .tyLe (.var 2) (.base .int)]
def sandwich : State 3 where
  atoms := atoms
  child := by
    intro a h
    simp only [atoms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> trivial
  width := by
    intro a b h tail ht
    simp only [atoms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;> cases h <;> cases ht
  rows := by
    intro a h
    simp only [atoms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> trivial

theorem old_empty : CommonRoleEvidenceSaturation.saturate sandwich = [] := by decide

theorem upper_middle : Derived sandwich (true,1,.int) := by
  apply Derived.transfer (j := 2)
  · simp [Linked, sandwich, atoms]
  · apply Derived.seed
    simp [atom, sandwich, atoms]

theorem lower_middle : Derived sandwich (false,1,.int) := by
  apply Derived.transfer (j := 0)
  · simp [Linked, sandwich, atoms]
  · apply Derived.seed
    simp [atom, sandwich, atoms]

theorem middle_forced (a : Fin 3 → Comp Common.model)
    (models : All Common.model a sandwich.atoms) :
    Common.Equivalent (a 1).1 (.base .int) :=
  ⟨derived_models sandwich _ upper_middle a models,
    derived_models sandwich _ lower_middle a models⟩

theorem consistent : All Common.model
    (fun (_ : Fin 3) => Comp.pure Common.model (.base .int)) sandwich.atoms := by
  intro a h
  simp only [sandwich, atoms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> exact Common.subtype_refl _

theorem middle_materialized :
    CommonRoleOrdinaryKnownness.materialize (normalize sandwich).atoms 1 = some Roles.Examples.int :=
  materializes_int sandwich 1 upper_middle lower_middle _ consistent

end Yulang.CommonRoleDirectedBoundsCheck
