import Yulang.CommonRoleDirectedDiagnostic
import Yulang.CommonRoleStructuralGlobalChoices

/-! Directed scalar propagation is subsumed by the structural rule closure.
This does not equate the two raw normalizers or decide semantic subtyping. -/
namespace Yulang.CommonRoleScalarStructuralAbsorption
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)
open CommonRoleSettledConstraints (State)
open CommonRoleStructuralCarrierCoverage (Derives normalize_membership derives_cut)

abbrev S (s : State n) : State n := CommonRoleStructuralGlobalChoices.normalize s
abbrev D (s : State n) : State n := CommonRoleDirectedBounds.normalize s

theorem directed_derives (s : State n) (f : CommonRoleDirectedBounds.Fact n)
    (h : CommonRoleDirectedBounds.Derived s f) :
    Derives s.atoms (CommonRoleDirectedBounds.atom f) := by
  induction h with
  | seed h => exact .seed _ h
  | @transfer side i j b linked _ ih =>
    cases side
    · exact .trans _ _ _ ih (.seed _ linked) (by simp [CommonRoleFiniteStructuralClosure.compose, CommonRoleDirectedBounds.atom])
    · exact .trans _ _ _ (.seed _ linked) ih (by simp [CommonRoleFiniteStructuralClosure.compose, CommonRoleDirectedBounds.atom])

theorem directed_subset (s : State n) (a : Atom (Fin n))
    (h : a ∈ (D s).atoms) : a ∈ (S s).atoms := by
  apply (normalize_membership s.atoms a).mpr
  rcases List.mem_append.mp h with hs | hd
  · exact .seed a hs
  · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hd
    exact directed_derives s f ((CommonRoleDirectedBounds.saturate_exact s f).mp hf)

theorem structural_after_directed (s : State n) (a : Atom (Fin n)) :
    a ∈ (S (D s)).atoms ↔ a ∈ (S s).atoms := by
  change a ∈ CommonRoleFiniteStructuralClosure.normalize (D s).atoms ↔
    a ∈ CommonRoleFiniteStructuralClosure.normalize s.atoms
  rw [normalize_membership, normalize_membership]
  constructor
  · exact derives_cut (fun b hb => (normalize_membership s.atoms b).mp (directed_subset s b hb))
  · exact derives_cut (fun b hb => .seed b (List.mem_append_left _ hb))

theorem directed_after_structural (s : State n) (a : Atom (Fin n)) :
    a ∈ (D (S s)).atoms ↔ a ∈ (S s).atoms := by
  constructor
  · intro h
    exact (CommonRoleStructuralCarrierCoverage.normalize_idempotent s.atoms a).mp
      (directed_subset (S s) a h)
  · intro h; exact List.mem_append_left _ h

/-- A directed scalar fact remains visible after structural closure. -/
theorem structural_evidence (s : State n) (i : Fin n) (b : Inference.Base)
    (hu : CommonRoleDirectedBounds.Derived s (true,i,b))
    (hl : CommonRoleDirectedBounds.Derived s (false,i,b)) :
    CommonRoleOrdinaryKnownness.Evidence (S s).atoms i b := by
  exact ⟨(normalize_membership ..).mpr (directed_derives s _ hu),
    (normalize_membership ..).mpr (directed_derives s _ hl)⟩

theorem materializes_int (s : State n) (i : Fin n)
    (hu : CommonRoleDirectedBounds.Derived s (true,i,.int))
    (hl : CommonRoleDirectedBounds.Derived s (false,i,.int))
    (a : Fin n → Comp Common.model) (hm : All Common.model a s.atoms) :
    CommonRoleOrdinaryKnownness.materialize (S s).atoms i = some Roles.Examples.int :=
  CommonRoleMaterializedDomain.evidence_int_materializes _ i a
    ((CommonRoleStructuralGlobalChoices.normalize_models s a).mpr hm)
    (structural_evidence s i .int hu hl)

/-- Both schedules preserve all models, including the empty-model case. -/
theorem models_pre (s : State n) (a : Fin n → Comp Common.model) :
    All Common.model a (S (D s)).atoms ↔ All Common.model a s.atoms :=
  (CommonRoleStructuralGlobalChoices.normalize_models (D s) a).trans
    (CommonRoleDirectedBounds.normalize_models s a)

theorem models_post (s : State n) (a : Fin n → Comp Common.model) :
    All Common.model a (D (S s)).atoms ↔ All Common.model a s.atoms :=
  (CommonRoleDirectedBounds.normalize_models (S s) a).trans
    (CommonRoleStructuralGlobalChoices.normalize_models s a)

open CommonRoleMaterializedDomain (Endpoint SourceRequest)
open CommonRoleOpenProducer (Registry)
open CommonRoleSettledSyntax (Declaration)

/-- Inserting the cheaper scalar pass before the structural pass does not change
endpoint observations on a state with an ordinary model. -/
theorem endpoint_pre (s : State n) (a : Fin n → Comp Common.model)
    (hm : All Common.model a s.atoms) (e : Endpoint n) :
    e.eval (S (D s)) = e.eval (S s) := by
  apply CommonRoleDiagnosticCanonical.endpoint_atoms
  · exact structural_after_directed s
  · exact (CommonRoleStructuralGlobalChoices.normalize_models (D s) a).mpr
      ((CommonRoleDirectedBounds.normalize_models s a).mpr hm)

/-- Inserting the scalar pass after the structural pass is also absorbed. -/
theorem endpoint_post (s : State n) (a : Fin n → Comp Common.model)
    (hm : All Common.model a s.atoms) (e : Endpoint n) :
    e.eval (D (S s)) = e.eval (S s) := by
  apply CommonRoleDiagnosticCanonical.endpoint_atoms
  · exact directed_after_structural s
  · exact (CommonRoleDirectedBounds.normalize_models (S s) a).mpr
      ((CommonRoleStructuralGlobalChoices.normalize_models s a).mpr hm)

theorem candidate_pre (s : State n) (a : Fin n → Comp Common.model)
    (hm : All Common.model a s.atoms) (p : SourceRequest n) (d : Declaration) :
    CommonRoleGuardedEquations.Candidate (S (D s)) p d ↔
      CommonRoleGuardedEquations.Candidate (S s) p d := by
  simp only [CommonRoleGuardedEquations.Candidate, endpoint_pre s a hm]

theorem candidate_post (s : State n) (a : Fin n → Comp Common.model)
    (hm : All Common.model a s.atoms) (p : SourceRequest n) (d : Declaration) :
    CommonRoleGuardedEquations.Candidate (D (S s)) p d ↔
      CommonRoleGuardedEquations.Candidate (S s) p d := by
  simp only [CommonRoleGuardedEquations.Candidate, endpoint_post s a hm]

/-- Whole ordered trees and repeated children agree; registry/source order is fixed. -/
theorem tree_pre (registry : Registry) (root : SourceRequest n)
    (table : CommonRoleGlobalChoices.Table registry root)
    (s : State n) (a : Fin n → Comp Common.model) (hm : All Common.model a s.atoms) :
    CommonRoleDiagnosticTree.diagnose registry root table (S (D s)) =
      CommonRoleDiagnosticTree.diagnose registry root table (S s) := by
  apply CommonRoleDiagnosticCanonical.diagnose_eq
  intro r d _
  exact and_congr Iff.rfl (candidate_pre s a hm r.2.val d)

theorem tree_post (registry : Registry) (root : SourceRequest n)
    (table : CommonRoleGlobalChoices.Table registry root)
    (s : State n) (a : Fin n → Comp Common.model) (hm : All Common.model a s.atoms) :
    CommonRoleDiagnosticTree.diagnose registry root table (D (S s)) =
      CommonRoleDiagnosticTree.diagnose registry root table (S s) := by
  apply CommonRoleDiagnosticCanonical.diagnose_eq
  intro r d _
  exact and_congr Iff.rfl (candidate_post s a hm r.2.val d)

section SelfOutput
open CommonRoleCorrelatedPaths (Route)
open CommonRoleAssociatedStateFlow (Request)
variable (registry : Registry) (root : SourceRequest n)
  (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
  (annotations : Route registry root → Declaration → List (Request n))
  (seed : State n) (table : CommonRoleGlobalChoices.Table registry root)

/-- Concrete associated-batch output, before either normalizer. -/
abbrev raw := CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed table

/-- Inserting scalar saturation before the actual structural self-output state
preserves every assignment, without a consistency or Stable premise. -/
theorem self_output_models_pre (a : Fin n → Comp Common.model) :
    All Common.model a (S (D (raw registry root env roles wf annotations seed table))).atoms ↔
      All Common.model a
        (CommonRoleStructuralGlobalChoices.output registry root env roles wf annotations seed table).atoms :=
  (models_pre _ a).trans (CommonRoleStructuralGlobalChoices.output_models_raw
    registry root env roles wf annotations seed table a).symm

theorem self_output_models_post (a : Fin n → Comp Common.model) :
    All Common.model a
      (D (CommonRoleStructuralGlobalChoices.output registry root env roles wf annotations seed table)).atoms ↔
      All Common.model a
        (CommonRoleStructuralGlobalChoices.output registry root env roles wf annotations seed table).atoms :=
  CommonRoleDirectedBounds.normalize_models _ a

/-- The actual self-output diagnostic tree absorbs a preliminary scalar pass.
The explicit model is of the generated batch, not merely of the original seed. -/
theorem self_tree_pre (a : Fin n → Comp Common.model)
    (hm : All Common.model a (raw registry root env roles wf annotations seed table).atoms) :
    CommonRoleDiagnosticTree.diagnose registry root table
      (S (D (raw registry root env roles wf annotations seed table))) =
    CommonRoleDiagnosticTree.diagnose registry root table
      (CommonRoleStructuralGlobalChoices.output registry root env roles wf annotations seed table) :=
  tree_pre registry root table _ a hm

/-- A subsequent scalar pass is also observationally redundant at actual output. -/
theorem self_tree_post (a : Fin n → Comp Common.model)
    (hm : All Common.model a (raw registry root env roles wf annotations seed table).atoms) :
    CommonRoleDiagnosticTree.diagnose registry root table
      (D (CommonRoleStructuralGlobalChoices.output registry root env roles wf annotations seed table)) =
    CommonRoleDiagnosticTree.diagnose registry root table
      (CommonRoleStructuralGlobalChoices.output registry root env roles wf annotations seed table) :=
  tree_post registry root table _ a hm
end SelfOutput

end Yulang.CommonRoleScalarStructuralAbsorption
