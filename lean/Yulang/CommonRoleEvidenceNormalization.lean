import Yulang.CommonRoleEvidenceSaturation

/-! Materialize the finite reciprocal-variable evidence closure into ordinary
atoms. Models are unchanged, and the cache is a semantic-membership fixed point.
This is the scalar equality fragment, not a general role feedback driver. -/
namespace Yulang.CommonRoleEvidenceNormalization
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All Atom)
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (Evidence)
open CommonRoleCandidateStateFrontier (extend extend_exact equality)
open CommonRoleEvidenceSaturation

def emit (s : State n) : List (Fact n) → State n
  | [] => s
  | f :: fs => extend (emit s fs) f.1 f.2

theorem emit_atoms (s : State n) (fs : List (Fact n)) (atom : Atom (Fin n)) :
    atom ∈ (emit s fs).atoms ↔ atom ∈ s.atoms ∨ ∃ f ∈ fs, atom ∈ equality f.1 f.2 := by
  induction fs with
  | nil => simp [emit]
  | cons f fs ih =>
    simp only [emit, extend, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro ((h | ⟨g,h,hg⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨g,Or.inr h,hg⟩
      · exact Or.inr ⟨f,Or.inl rfl,h⟩
    · rintro (h | ⟨g,(rfl | h),hg⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr hg
      · exact Or.inl (Or.inr ⟨g,h,hg⟩)

theorem emit_models (s : State n) (fs : List (Fact n))
    (valid : ∀ f ∈ fs, Derived s f) (a : Fin n → Comp Common.model) :
    All Common.model a (emit s fs).atoms ↔ All Common.model a s.atoms := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [emit, extend_exact, ih (fun g h => valid g (List.mem_cons_of_mem _ h))]
    exact ⟨And.left,fun h => ⟨h,derived_models s f (valid f List.mem_cons_self) a h⟩⟩

def normalize (s : State n) : State n := emit s (saturate s)

theorem normalize_models (s : State n) (a : Fin n → Comp Common.model) :
    All Common.model a (normalize s).atoms ↔ All Common.model a s.atoms :=
  emit_models s _ (fun f h => (saturate_exact s f).mp h) a

theorem normalize_linked (s : State n) (i j : Fin n) :
    Linked (normalize s) i j ↔ Linked s i j := by
  simp [Linked, normalize, emit_atoms, equality]

theorem normalize_evidence (s : State n) (i : Fin n) (b : Inference.Base) :
    Evidence (normalize s).atoms i b ↔ Derived s (i,b) := by
  have upper : Atom.tyLe (.var i) (.base b) ∈ (normalize s).atoms ↔
      Atom.tyLe (.var i) (.base b) ∈ s.atoms ∨ (i,b) ∈ saturate s := by
    simp only [normalize, emit_atoms]
    apply or_congr_right
    constructor
    · rintro ⟨⟨j,c⟩,h,he⟩
      simp only [equality, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with he | he <;> cases he
      exact h
    · intro h
      exact ⟨(i,b),h,by simp [equality]⟩
  have lower : Atom.tyLe (.base b) (.var i) ∈ (normalize s).atoms ↔
      Atom.tyLe (.base b) (.var i) ∈ s.atoms ∨ (i,b) ∈ saturate s := by
    simp only [normalize, emit_atoms]
    apply or_congr_right
    constructor
    · rintro ⟨⟨j,c⟩,h,he⟩
      simp only [equality, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with he | he <;> cases he
      exact h
    · intro h
      exact ⟨(i,b),h,by simp [equality]⟩
  rw [Evidence, upper, lower]
  constructor
  · rintro ⟨hu,hl⟩
    rcases hu with hu | hu
    · rcases hl with hl | hl
      · exact .seed ⟨hu,hl⟩
      · exact (saturate_exact ..).mp hl
    · exact (saturate_exact ..).mp hu
  · intro h
    exact ⟨Or.inr ((saturate_exact ..).mpr h),Or.inr ((saturate_exact ..).mpr h)⟩

theorem normalize_derived (s : State n) (f : Fact n) :
    Derived (normalize s) f ↔ Derived s f := by
  constructor
  · intro h
    induction h with
    | seed h => exact (normalize_evidence ..).mp h
    | transfer h _ ih => exact .transfer ((normalize_linked ..).mp h) ih
  · intro h
    exact .seed ((normalize_evidence ..).mpr h)

/-- Resaturating the normalized state adds no new fact, including on cycles.
This is membership equality, not literal atom-list idempotence. -/
theorem saturate_fixedpoint (s : State n) (f : Fact n) :
    f ∈ saturate (normalize s) ↔ f ∈ saturate s := by
  rw [saturate_exact, normalize_derived, saturate_exact]

theorem materializes_int (s : State n) (i : Fin n) (derived : Derived s (i,.int))
    (a : Fin n → Comp Common.model) (models : All Common.model a s.atoms) :
    CommonRoleOrdinaryKnownness.materialize (normalize s).atoms i = some Roles.Examples.int :=
  CommonRoleMaterializedDomain.evidence_int_materializes _ i a
    ((normalize_models s a).mpr models) ((normalize_evidence ..).mpr derived)

end Yulang.CommonRoleEvidenceNormalization
