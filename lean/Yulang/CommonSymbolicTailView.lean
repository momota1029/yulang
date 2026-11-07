import Yulang.CommonRecord

/-!
# A finite, assignment-independent encoding of remaining record demands

An unknown shared slot can contain labels absent from the input syntax. Its
remaining field demands therefore cannot be tested by the concrete type's
finite label inventory at inference time. This view retains every such label.

The finite syntax wraps the hidden labels with equal payloads and uses two
different record heads. Each head hides one label; the other component still
observes it. The resulting ordinary common subtype comparison is exactly the
original tail relation. No source assignment is inspected to choose labels.

This is an exact encoding, not a saturation algorithm: repeatedly expanding
the view back into the same tail obligation would make no progress. Its role
is to expose tail constraints in the shared type grammar, preserving all
unknown labels and negative occurrences.
-/

namespace Yulang.CommonSymbolicTailView

namespace Finite

open CommonFinite

universe u
variable {Row : Type u} {leRow : Row → Row → Prop}

theorem tail_record_both_iff (hidden : List Nat) (label : Nat)
    (payload source target : Ty Row) :
    RecordTailLe leRow hidden (.record label payload source) (.record label payload target) ↔
      RecordTailLe leRow (label :: hidden) source target := by
  constructor
  · intro below
    constructor
    · intro rank env current visible obs accepted
      have different : current ≠ label := fun same => visible (List.mem_cons.mpr (Or.inl same))
      have previous : current ∉ hidden := fun member => visible (List.mem_cons_of_mem label member)
      have comparison := below.1 rank env current previous obs
      simp only [probeAt_record_field, different, ↓reduceIte] at comparison
      exact comparison accepted
    · intro rank env current visible obs nontrivial accepted
      have different : current ≠ label := fun same => visible (List.mem_cons.mpr (Or.inl same))
      have previous : current ∉ hidden := fun member => visible (List.mem_cons_of_mem label member)
      have comparison := below.2 rank env current previous obs nontrivial
      simp only [probeAt_record_optional, different, ↓reduceIte, nontrivial, or_false] at comparison
      exact comparison accepted
  · intro below
    constructor
    · intro rank env current visible obs accepted
      by_cases same : current = label
      · subst current
        simpa only [probeAt_record_field, ↓reduceIte] using accepted
      · have next : current ∉ label :: hidden := by simp [same, visible]
        simp only [probeAt_record_field, same, ↓reduceIte] at accepted ⊢
        exact below.1 rank env current next obs accepted
    · intro rank env current visible obs nontrivial accepted
      by_cases same : current = label
      · subst current
        simpa only [probeAt_record_optional, ↓reduceIte] using accepted
      · have next : current ∉ label :: hidden := by simp [same, visible]
        simp only [probeAt_record_optional, same, ↓reduceIte, nontrivial, or_false] at accepted ⊢
        exact below.2 rank env current next obs nontrivial accepted

theorem tail_two_heads_iff (hidden : List Nat) (first last : Nat)
    (different : first ≠ last) (source target : Ty Row) :
    RecordTailLe leRow hidden source target ↔
      RecordTailLe leRow (hidden ++ [first]) source target ∧
      RecordTailLe leRow (hidden ++ [last]) source target := by
  constructor
  · intro below
    have weaken (head : Nat) : RecordTailLe leRow (hidden ++ [head]) source target := by
      constructor
      · intro rank env label visible obs accepted
        exact below.1 rank env label
          (fun member => visible (List.mem_append.mpr (Or.inl member))) obs accepted
      · intro rank env label visible obs nontrivial accepted
        exact below.2 rank env label
          (fun member => visible (List.mem_append.mpr (Or.inl member))) obs nontrivial accepted
    exact ⟨weaken first, weaken last⟩
  · rintro ⟨before, after⟩
    constructor
    · intro rank env label visible obs accepted
      by_cases same : label = first
      · have other : label ≠ last := fun equal => different (same.symm.trans equal)
        exact after.1 rank env label (by simpa [List.mem_append, other] using visible) obs accepted
      · exact before.1 rank env label (by simpa [List.mem_append, same] using visible) obs accepted
    · intro rank env label visible obs nontrivial accepted
      by_cases same : label = first
      · have other : label ≠ last := fun equal => different (same.symm.trans equal)
        exact after.2 rank env label (by simpa [List.mem_append, other] using visible) obs nontrivial accepted
      · exact before.2 rank env label (by simpa [List.mem_append, same] using visible) obs nontrivial accepted

end Finite

open Common

theorem tail_record_both_iff (hidden : List Nat) (label : Nat)
    (payload source target : Ty) :
    RecordTailLe hidden (record label payload source) (record label payload target) ↔
      RecordTailLe (label :: hidden) source target := by
  apply forall_congr'
  intro depth
  exact Finite.tail_record_both_iff hidden label _ _ _

/-- Only the supplied finite hidden list is traversed, never the type. -/
def cover : List Nat → Ty → Ty
  | [] , source => source
  | label :: rest, source => cover rest (record label .top source)

theorem tail_cover_iff (hidden labels : List Nat) (source target : Ty) :
    RecordTailLe hidden (cover labels source) (cover labels target) ↔
      RecordTailLe (labels ++ hidden) source target := by
  induction labels generalizing source target hidden with
  | nil => rfl
  | cons label rest ih =>
      rw [cover, cover, ih, tail_record_both_iff]
      rfl

theorem tail_two_heads_iff (hidden : List Nat) (first last : Nat)
    (different : first ≠ last) (source target : Ty) :
    RecordTailLe hidden source target ↔
      RecordTailLe (hidden ++ [first]) source target ∧
      RecordTailLe (hidden ++ [last]) source target := by
  constructor
  · intro below
    exact ⟨fun depth => (Finite.tail_two_heads_iff hidden first last different _ _).mp (below depth) |>.1,
      fun depth => (Finite.tail_two_heads_iff hidden first last different _ _).mp (below depth) |>.2⟩
  · rintro ⟨before, after⟩ depth
    exact (Finite.tail_two_heads_iff hidden first last different _ _).mpr ⟨before depth, after depth⟩

def view (hidden : List Nat) (source : Ty) : Ty :=
  pair (record 0 .top (cover hidden source)) (record 1 .top (cover hidden source))

/-- All common types, including unknown labels and arbitrary regular graphs.
The encoding is fixed by the hidden labels, with no semantic input. -/
theorem tail_view_exact (hidden : List Nat) (source target : Ty) :
    RecordTailLe hidden source target ↔ Subtype (view hidden source) (view hidden target) := by
  change RecordTailLe hidden source target ↔ model.subTy
    (pair (record 0 .top (cover hidden source)) (record 1 .top (cover hidden source)))
    (pair (record 0 .top (cover hidden target)) (record 1 .top (cover hidden target)))
  rw [common_pair_iff]
  change RecordTailLe hidden source target ↔
    Subtype (record 0 .top (cover hidden source)) (record 0 .top (cover hidden target)) ∧
    Subtype (record 1 .top (cover hidden source)) (record 1 .top (cover hidden target))
  rw [common_record_iff, common_record_iff]
  simp only [subtype_refl, true_and, tail_cover_iff]
  exact tail_two_heads_iff hidden 0 1 (by decide) source target

theorem view_equivalent_iff (hidden : List Nat) (source target : Ty) :
    Equivalent (view hidden source) (view hidden target) ↔
      RecordTailLe hidden source target ∧ RecordTailLe hidden target source := by
  simp only [Equivalent, ← tail_view_exact]

open Core.PresenceGeneration (TyTerm Comp CompTerm)

/-- The same encoding in the actual source type grammar. Shared variables
are copied by identifier, without inspecting their assigned common types. -/
def termCover (hidden : List Nat) (source : TyTerm α) : TyTerm α :=
  match hidden with
  | [] => source
  | label :: rest => termCover rest (.record label .top source)

def termView (hidden : List Nat) (source : TyTerm α) : TyTerm α :=
  .pair (.record 0 .top (termCover hidden source))
    (.record 1 .top (termCover hidden source))

theorem termCover_eval (hidden : List Nat) (source : TyTerm α)
    (assignment : α → Comp Common.model) :
    (termCover hidden source).eval Common.model assignment =
      cover hidden (source.eval Common.model assignment) := by
  induction hidden generalizing source with
  | nil => rfl
  | cons label rest ih => exact ih (.record label .top source)

theorem termView_eval (hidden : List Nat) (source : TyTerm α)
    (assignment : α → Comp Common.model) :
    (termView hidden source).eval Common.model assignment =
      view hidden (source.eval Common.model assignment) := by
  change pair (record 0 .top ((termCover hidden source).eval Common.model assignment))
    (record 1 .top ((termCover hidden source).eval Common.model assignment)) = _
  rw [termCover_eval]
  rfl

theorem termCover_rename (hidden : List Nat) (source : TyTerm α) (mapping : α → β) :
    (termCover hidden source).rename mapping = termCover hidden (source.rename mapping) := by
  induction hidden generalizing source with
  | nil => rfl
  | cons label rest ih => exact ih (.record label .top source)

theorem termView_rename (hidden : List Nat) (source : TyTerm α) (mapping : α → β) :
    (termView hidden source).rename mapping = termView hidden (source.rename mapping) := by
  simp only [termView, TyTerm.rename, termCover_rename]

theorem termCover_subst (hidden : List Nat) (source : TyTerm α) (mapping : α → CompTerm β) :
    (termCover hidden source).subst mapping = termCover hidden (source.subst mapping) := by
  induction hidden generalizing source with
  | nil => rfl
  | cons label rest ih => exact ih (.record label .top source)

theorem termView_subst (hidden : List Nat) (source : TyTerm α) (mapping : α → CompTerm β) :
    (termView hidden source).subst mapping = termView hidden (source.subst mapping) := by
  simp only [termView, TyTerm.subst, termCover_subst]

/-- Exact for every source-slot assignment, including types with labels
absent from both source terms and the finite hidden list. -/
theorem symbolic_tail_exact (hidden : List Nat) (source target : TyTerm α)
    (assignment : α → Comp Common.model) :
    RecordTailLe hidden (source.eval Common.model assignment) (target.eval Common.model assignment) ↔
      Subtype ((termView hidden source).eval Common.model assignment)
        ((termView hidden target).eval Common.model assignment) := by
  rw [termView_eval, termView_eval]
  exact tail_view_exact hidden _ _

end Yulang.CommonSymbolicTailView
