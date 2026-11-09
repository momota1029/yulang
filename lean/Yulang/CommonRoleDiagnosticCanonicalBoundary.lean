import Yulang.CommonRoleDiagnosticCanonical

/-! Model equivalence alone cannot justify the current direct-evidence decoder.
A transitive scalar equality and an explicit one have the same ordinary models,
but only the explicit presentation materializes the first slot. -/
namespace Yulang.CommonRoleDiagnosticCanonicalBoundary
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (All Atom)
open CommonRoleSettledConstraints (State)
open CommonRoleCandidateStateFrontier (extend extend_exact)

def linkedAtoms : List (Atom (Fin 2)) :=
  [.tyLe (.var 0) (.var 1), .tyLe (.var 1) (.var 0)]

def linked : State 2 where
  atoms := linkedAtoms
  child := by
    intro a h
    simp only [linkedAtoms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> trivial
  width := by
    intro a b h tail ht
    simp only [linkedAtoms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h <;> cases h <;> cases ht
  rows := by
    intro a h
    simp only [linkedAtoms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> trivial

def indirect : State 2 := extend linked 1 .int
def direct : State 2 := extend (extend State.empty 0 .int) 1 .int

theorem linked_models (a : Fin 2 → Comp Common.model) :
    All Common.model a linked.atoms ↔ Common.Equivalent (a 0).1 (a 1).1 := by
  simp [linked, linkedAtoms, All, Atom.Holds, TyTerm.eval, Common.model, Common.Equivalent]

/-- Ordinary model sets agree for every assignment, not just satisfiability. -/
theorem same_models (a : Fin 2 → Comp Common.model) :
    All Common.model a indirect.atoms ↔ All Common.model a direct.atoms := by
  simp only [indirect, direct, extend_exact, linked_models]
  have empty : All Common.model a (State.empty (n := 2)).atoms := by intro _ h; cases h
  constructor
  · rintro ⟨ab,bi⟩
    exact ⟨⟨empty,Common.equivalent_trans ab bi⟩,bi⟩
  · rintro ⟨⟨_,ai⟩,bi⟩
    exact ⟨Common.equivalent_trans ai (Common.equivalent_symm bi),bi⟩

/-- The shared model is concrete, so inconsistency cannot explain the mismatch. -/
theorem consistent : ∃ a : Fin 2 → Comp Common.model,
    All Common.model a indirect.atoms ∧ All Common.model a direct.atoms := by
  let a : Fin 2 → Comp Common.model := fun _ => Comp.pure Common.model (.base .int)
  have h : All Common.model a direct.atoms := by
    simp only [direct, extend_exact]
    exact ⟨⟨(by intro _ h; cases h),Common.equivalent_refl _⟩,Common.equivalent_refl _⟩
  exact ⟨a,(same_models a).mpr h,h⟩

theorem indirect_unmaterialized :
    CommonRoleOrdinaryKnownness.materialize indirect.atoms 0 = none := by decide

theorem direct_materialized :
    CommonRoleOrdinaryKnownness.materialize direct.atoms 0 = some Roles.Examples.int := by decide

/-- Equal, nonempty model sets do not imply equal materialized endpoints. -/
theorem endpoint_difference :
    (CommonRoleMaterializedDomain.Endpoint.slot (0 : Fin 2)).eval indirect ≠
      (CommonRoleMaterializedDomain.Endpoint.slot (0 : Fin 2)).eval direct := by decide

end Yulang.CommonRoleDiagnosticCanonicalBoundary
