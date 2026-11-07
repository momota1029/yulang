import Yulang.CommonEffectBoundExtraction

/-! Actual finite scoped witness templates computed from extracted bounds.
The finite candidate list is chosen before operation-local universals; only
selection among those finite candidates may vary locally. Captured values
and rows remain identical. Universal comparisons remaining after this step
are still real obligations, not conditions on solved-scheme parameters. -/
namespace Yulang.CommonEffectBoundTemplates
open Common (Ty)
open Core.PresenceGeneration (CompTerm TyTerm)
open CommonEffectRequestGeneration (Computation localEnv)
open CommonEffectFormula (Formula)
open CommonEffectBoundExtraction (Summary Accepts inspect)

variable {scopes count : Nat}

def values (summary : Summary scopes count α) (assignment : α → Computation) : Fin count → Ty :=
  fun index => (CommonEffectScopedBounds.witnesses summary.bounds index).eval Common.model assignment

theorem canonical_exact (summary : Summary scopes count α) (assignment : α → Computation) :
    (∃ types : Fin count → Ty, summary.Holds assignment types) ↔ summary.Holds assignment (values summary assignment) := by
  change (∃ types, CommonBoundCoalescing.Models _ _ types ∧ _) ↔ CommonBoundCoalescing.Models _ _ _ ∧ _
  exact exists_and_right.trans
    (and_congr (CommonEffectScopedBounds.canonical_witness_exact summary.bounds assignment) Iff.rfl)

def substitution (summary : Summary scopes count α) : α ⊕ Fin count → CompTerm α
  | .inl name => CompTerm.var name
  | .inr index => CompTerm.pure (CommonEffectScopedBounds.witnesses summary.bounds index)

theorem substitution_eval (summary : Summary scopes count α) (assignment : α → Computation) :
    (fun name => (substitution summary name).eval Common.model assignment) = localEnv assignment (values summary assignment) := by
  funext name
  cases name <;> rfl

def candidate (summary : Summary scopes count α) (body : Formula scopes (α ⊕ Fin count)) : Formula scopes α :=
  body.subst (substitution summary)

theorem candidate_exact (summary : Summary scopes count α) (body : Formula scopes (α ⊕ Fin count)) (assignment : α → Computation) :
    (candidate summary body).Holds assignment ↔ body.Holds (localEnv assignment (values summary assignment)) := by
  simp only [candidate, Formula.holds_subst, substitution_eval]

/-- A finite list of actual term substitutions suffices. No arbitrary
Skolem function, altered capture, or infinite family is supplied. -/
theorem finite_candidates_exact (body : Formula scopes (α ⊕ Fin count)) (summaries : List (Summary scopes count α))
    (found : inspect body = some summaries) (assignment : α → Computation) :
    (∃ types : Fin count → Ty, body.Holds (localEnv assignment types)) ↔
      ∃ summary ∈ summaries, (candidate summary body).Holds assignment := by
  constructor
  · rintro ⟨types, accepted⟩
    obtain ⟨summary, member, summaryHolds⟩ := (CommonEffectBoundExtraction.inspect_exact body summaries found assignment types).mpr accepted
    have canonical := (canonical_exact summary assignment).mp ⟨types, summaryHolds⟩
    have bodyHolds := (CommonEffectBoundExtraction.inspect_exact body summaries found assignment (values summary assignment)).mp
      ⟨summary, member, canonical⟩
    exact ⟨summary, member, (candidate_exact summary body assignment).mpr bodyHolds⟩
  · rintro ⟨summary, _, accepted⟩
    exact ⟨values summary assignment, (candidate_exact summary body assignment).mp accepted⟩

/-- Outer input/result/environment live in the unchanged ambient assignment.
The finite candidate syntax precedes the universal local interpretation. -/
theorem universal_finite_candidates_exact
    (body : Formula scopes ((α ⊕ Fin locals) ⊕ Fin count))
    (summaries : List (Summary scopes count (α ⊕ Fin locals))) (found : inspect body = some summaries)
    (assignment : α → Computation) :
    (∀ localTypes : Fin locals → Ty, ∃ types : Fin count → Ty,
      body.Holds (localEnv (localEnv assignment localTypes) types)) ↔
    ∀ localTypes : Fin locals → Ty, ∃ summary ∈ summaries,
      (candidate summary body).Holds (localEnv assignment localTypes) :=
  forall_congr' (fun localTypes => finite_candidates_exact body summaries found (localEnv assignment localTypes))

end Yulang.CommonEffectBoundTemplates
