import Yulang.StructuralRowResolution

/-!
# Resolving exactly the row occurrences of a finite ground type

The total traversal returns `none` exactly when at least one occurring row is
unsupported by the supplied resolver. It never enumerates an ambient slot type
or requires rows which do not occur in the given type. The returned type has
the identical structural shape and the exact decoded rows.
-/

namespace Yulang.StructuralRowResolution

open StructuralBase

variable {A : Type u} {B : Type v} {C : Type w}

def rows : Ty A → List A
  | .base _ | .bottom | .emptyRecord => []
  | .union left right | .inter left right | .pair left right => rows left ++ rows right
  | .record _ value rest => rows value ++ rows rest
  | .variant _ value => rows value
  | .arrow input inputRow output outputRow => inputRow :: outputRow :: (rows input ++ rows output)

def traverseRows (choose : A → Option B) : Ty A → Option (Ty B)
  | .base base => some (.base base)
  | .bottom => some .bottom
  | .union left right =>
      (traverseRows choose left).bind fun left' =>
      (traverseRows choose right).bind fun right' =>
      some (.union left' right')
  | .inter left right =>
      (traverseRows choose left).bind fun left' =>
      (traverseRows choose right).bind fun right' =>
      some (.inter left' right')
  | .pair left right =>
      (traverseRows choose left).bind fun left' =>
      (traverseRows choose right).bind fun right' =>
      some (.pair left' right')
  | .emptyRecord => some .emptyRecord
  | .record label value rest =>
      (traverseRows choose value).bind fun value' =>
      (traverseRows choose rest).bind fun rest' =>
      some (.record label value' rest')
  | .variant label value =>
      (traverseRows choose value).bind fun value' =>
      some (.variant label value')
  | .arrow input inputRow output outputRow =>
      (traverseRows choose input).bind fun input' =>
      (choose inputRow).bind fun inputRow' =>
      (traverseRows choose output).bind fun output' =>
      (choose outputRow).bind fun outputRow' =>
      some (.arrow input' inputRow' output' outputRow')

theorem traverseRows_exact (choose : A → Option B) (decode : B → C) (meaning : A → C)
    (rowExact : ∀ row resolved, choose row = some resolved → decode resolved = meaning row)
    (type : Ty A) (resolved : Ty B) (returned : traverseRows choose type = some resolved) :
    mapRows decode resolved = mapRows meaning type := by
  induction type generalizing resolved with
  | base base => cases returned; rfl
  | bottom => cases returned; rfl
  | emptyRecord => cases returned; rfl
  | union left right ihl ihr =>
      simp only [traverseRows, Option.bind_eq_some_iff, Option.some.injEq] at returned
      rcases returned with ⟨left', hl, right', hr, rfl⟩
      simp only [mapRows, ihl left' hl, ihr right' hr]
  | inter left right ihl ihr =>
      simp only [traverseRows, Option.bind_eq_some_iff, Option.some.injEq] at returned
      rcases returned with ⟨left', hl, right', hr, rfl⟩
      simp only [mapRows, ihl left' hl, ihr right' hr]
  | pair left right ihl ihr =>
      simp only [traverseRows, Option.bind_eq_some_iff, Option.some.injEq] at returned
      rcases returned with ⟨left', hl, right', hr, rfl⟩
      simp only [mapRows, ihl left' hl, ihr right' hr]
  | record label value rest ihv ihr =>
      simp only [traverseRows, Option.bind_eq_some_iff, Option.some.injEq] at returned
      rcases returned with ⟨value', hv, rest', hr, rfl⟩
      simp only [mapRows, ihv value' hv, ihr rest' hr]
  | variant label value ih =>
      simp only [traverseRows, Option.bind_eq_some_iff, Option.some.injEq] at returned
      rcases returned with ⟨value', hv, rfl⟩
      simp only [mapRows, ih value' hv]
  | arrow input inputRow output outputRow ihi iho =>
      simp only [traverseRows, Option.bind_eq_some_iff, Option.some.injEq] at returned
      rcases returned with ⟨input', hi, inputRow', hri, output', ho, outputRow', hro, rfl⟩
      simp only [mapRows, ihi input' hi, iho output' ho,
        rowExact inputRow inputRow' hri, rowExact outputRow outputRow' hro]

theorem traverseRows_supported_iff (choose : A → Option B) (type : Ty A) :
    (∃ resolved, traverseRows choose type = some resolved) ↔
      ∀ row ∈ rows type, ∃ result, choose row = some result := by
  induction type with
  | base base => simp [traverseRows, rows]
  | bottom => simp [traverseRows, rows]
  | emptyRecord => simp [traverseRows, rows]
  | union left right ihl ihr =>
      simp only [traverseRows, Option.bind_eq_some_iff, Option.some.injEq, rows,
        List.mem_append, or_imp, forall_and]
      simp only [← ihl, ← ihr]
      constructor
      · rintro ⟨_, left', hl, right', hr, _⟩
        exact ⟨⟨left', hl⟩, ⟨right', hr⟩⟩
      · rintro ⟨⟨left', hl⟩, ⟨right', hr⟩⟩
        exact ⟨_, left', hl, right', hr, rfl⟩
  | inter left right ihl ihr =>
      simp only [traverseRows, Option.bind_eq_some_iff, Option.some.injEq, rows,
        List.mem_append, or_imp, forall_and]
      simp only [← ihl, ← ihr]
      constructor
      · rintro ⟨_, left', hl, right', hr, _⟩
        exact ⟨⟨left', hl⟩, ⟨right', hr⟩⟩
      · rintro ⟨⟨left', hl⟩, ⟨right', hr⟩⟩
        exact ⟨_, left', hl, right', hr, rfl⟩
  | pair left right ihl ihr =>
      simp only [traverseRows, Option.bind_eq_some_iff, Option.some.injEq, rows,
        List.mem_append, or_imp, forall_and]
      simp only [← ihl, ← ihr]
      constructor
      · rintro ⟨_, left', hl, right', hr, _⟩
        exact ⟨⟨left', hl⟩, ⟨right', hr⟩⟩
      · rintro ⟨⟨left', hl⟩, ⟨right', hr⟩⟩
        exact ⟨_, left', hl, right', hr, rfl⟩
  | record label value rest ihv ihr =>
      simp only [traverseRows, Option.bind_eq_some_iff, Option.some.injEq, rows,
        List.mem_append, or_imp, forall_and]
      simp only [← ihv, ← ihr]
      constructor
      · rintro ⟨_, value', hv, rest', hr, _⟩
        exact ⟨⟨value', hv⟩, ⟨rest', hr⟩⟩
      · rintro ⟨⟨value', hv⟩, ⟨rest', hr⟩⟩
        exact ⟨_, value', hv, rest', hr, rfl⟩
  | variant label value ih =>
      simp only [traverseRows, Option.bind_eq_some_iff, Option.some.injEq, rows, ← ih]
      constructor
      · rintro ⟨_, value', hv, _⟩; exact ⟨value', hv⟩
      · rintro ⟨value', hv⟩; exact ⟨_, value', hv, rfl⟩
  | arrow input inputRow output outputRow ihi iho =>
      simp only [traverseRows, Option.bind_eq_some_iff, Option.some.injEq, rows,
        List.mem_cons, List.mem_append, or_imp, forall_and, forall_eq]
      simp only [← ihi, ← iho]
      constructor
      · rintro ⟨_, input', hi, inputRow', hri, output', ho, outputRow', hro, _⟩
        exact ⟨⟨inputRow', hri⟩, ⟨outputRow', hro⟩, ⟨input', hi⟩, ⟨output', ho⟩⟩
      · rintro ⟨⟨inputRow', hri⟩, ⟨outputRow', hro⟩, ⟨input', hi⟩, ⟨output', ho⟩⟩
        exact ⟨_, input', hi, inputRow', hri, output', ho, outputRow', hro, rfl⟩

end Yulang.StructuralRowResolution
