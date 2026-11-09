import Yulang.CommonRoleEvidenceNormalization
import Yulang.CommonRoleDiagnosticCanonical

/-! Observational closure of the finite scalar evidence normalization. Ordinary
consistency is explicit; no arbitrary semantic entailment or role feedback
convergence is asserted. Source endpoints still use the existing int-only view. -/
namespace Yulang.CommonRoleNormalizedDiagnostic
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleSettledConstraints (State)
open CommonRoleEvidenceNormalization (normalize normalize_models normalize_evidence normalize_derived)
open CommonRoleEvidenceSaturation (Derived)
open CommonRoleMaterializedDomain (Endpoint SourceRequest)
open CommonRoleOrdinaryKnownness (materialize detect_evidence encode)
open CommonRoleOpenProducer (Registry)
open CommonRoleSettledSyntax (Declaration)
open CommonRoleGuardedEquations (Candidate)

/-- Every normalized int observation has an independently derived scalar fact.
The reverse direction requires a model to rule out conflicting scalar witnesses. -/
theorem materialize_exact (s : State n) (i : Fin n)
    (a : Fin n → Comp Common.model) (models : All Common.model a s.atoms) :
    materialize (normalize s).atoms i = some Roles.Examples.int ↔ Derived s (i,.int) := by
  constructor
  · intro h
    obtain ⟨b,hb,he⟩ := Option.bind_eq_some_iff.mp h
    have eq : b = Inference.Base.int := by
      cases b <;> simp [encode, Roles.Examples.int] at he ⊢
    subst b
    exact (normalize_evidence s i .int).mp (detect_evidence _ _ _ hb)
  · exact fun h => CommonRoleEvidenceNormalization.materializes_int s i h a models

/-- Derived scalar evidence equality, not merely model-set equality, is the
interface needed by this conservative decoder. -/
theorem endpoint_derived (s t : State n)
    (same : ∀ i, Derived s (i,.int) ↔ Derived t (i,.int))
    (a b : Fin n → Comp Common.model)
    (hs : All Common.model a s.atoms) (ht : All Common.model b t.atoms)
    (e : Endpoint n) : e.eval (normalize s) = e.eval (normalize t) := by
  induction e with
  | fixed v => rfl
  | slot i =>
    have eqv : materialize (normalize s).atoms i = some Roles.Examples.int ↔
        materialize (normalize t).atoms i = some Roles.Examples.int :=
      (materialize_exact s i a hs).trans ((same i).trans (materialize_exact t i b ht).symm)
    simp only [Endpoint.eval, eqv]
  | wrap c e ih => simp only [Endpoint.eval, ih]

/-- Normalizing twice leaves every source endpoint observation unchanged. -/
theorem endpoint_fixedpoint (s : State n) (a : Fin n → Comp Common.model)
    (hs : All Common.model a s.atoms) (e : Endpoint n) :
    e.eval (normalize (normalize s)) = e.eval (normalize s) :=
  endpoint_derived (normalize s) s (fun i => normalize_derived s (i,.int)) a a
    ((normalize_models s a).mpr hs) hs e

/-- Candidate guards are closed under re-normalization, for every declaration. -/
theorem candidate_fixedpoint (s : State n) (a : Fin n → Comp Common.model)
    (hs : All Common.model a s.atoms) (p : SourceRequest n) (d : Declaration) :
    Candidate (normalize (normalize s)) p d ↔ Candidate (normalize s) p d := by
  simp only [Candidate, endpoint_fixedpoint s a hs]

/-- Whole ordered diagnostic trees, including child multiplicity, are fixed
under re-normalization. This is not a fixed point of role equation generation. -/
theorem tree_fixedpoint (registry : Registry) (root : SourceRequest n)
    (table : CommonRoleGlobalChoices.Table registry root)
    (s : State n) (a : Fin n → Comp Common.model) (hs : All Common.model a s.atoms) :
    CommonRoleDiagnosticTree.diagnose registry root table (normalize (normalize s)) =
      CommonRoleDiagnosticTree.diagnose registry root table (normalize s) := by
  apply CommonRoleDiagnosticCanonical.diagnose_eq
  intro r d _
  exact and_congr Iff.rfl (candidate_fixedpoint s a hs r.2.val d)

/-- Equal derived scalar observations and table membership imply literal equality
of the full ordered tree, even when original ordinary atom sets differ. -/
theorem tree_derived (registry : Registry) (root : SourceRequest n)
    (left right : CommonRoleGlobalChoices.Table registry root)
    (tables : ∀ p, p ∈ left ↔ p ∈ right)
    (s t : State n) (same : ∀ i, Derived s (i,.int) ↔ Derived t (i,.int))
    (a b : Fin n → Comp Common.model)
    (hs : All Common.model a s.atoms) (ht : All Common.model b t.atoms) :
    CommonRoleDiagnosticTree.diagnose registry root left (normalize s) =
      CommonRoleDiagnosticTree.diagnose registry root right (normalize t) := by
  apply CommonRoleDiagnosticCanonical.diagnose_eq
  intro r d _
  apply and_congr (tables (r,d))
  simp only [Candidate, endpoint_derived s t same a b hs ht]
end Yulang.CommonRoleNormalizedDiagnostic
