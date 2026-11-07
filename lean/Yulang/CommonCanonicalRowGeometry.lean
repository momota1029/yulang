import Yulang.CommonCanonicalRowSyntax

/-! # Exact finite row binders in arbitrary finite dimension -/

namespace Yulang.CommonCanonicalRowGeometry

open Directed RowInference
open CommonCanonicalRowSyntax (ClosedRow)

def point (values : Fin n → Nat) : Occurrence n Nat :=
  ⟨0, fun coordinate => values coordinate⟩

def write (values : Fin n → Nat) (scope : Fin n) (value : Nat) : Fin n → Nat :=
  fun coordinate => if coordinate = scope then value else values coordinate

/-- The actual finite binder body denotes precisely its nonnegative
coordinate subspace. Duplicates in enabled and dimension zero are allowed. -/
theorem closed_row_exact (closed : ClosedRow n) (occurrence : Occurrence n Nat) :
    closed.binder.Meaning occurrence ↔ occurrence.key = 0 ∧
      (∀ coordinate, 0 ≤ occurrence.weights coordinate) ∧
      (∀ coordinate, coordinate ∉ closed.enabled → occurrence.weights coordinate = 0) := by
  let steps : List (Fin n) → RowExpr Nat (Fin n) Unit := fun enabled =>
    enabled.foldr (fun coordinate rest =>
      .union (.protect coordinate allowNone (.var ())) rest) .empty
  let grid (enabled : List (Fin n)) := (ClosedRow.mk enabled).binder
  have stepsExact (enabled : List (Fin n)) (rows : Unit → RecursiveRows.SetRow n Nat)
      (current : Occurrence n Nat) :
      (steps enabled).eval (RecursiveRows.algebra n Nat) rows current ↔
        ∃ scope ∈ enabled, ∃ before, rows () before ∧ protect scope allowNone before = current := by
    induction enabled with
    | nil => simp [steps, RowExpr.eval, RecursiveRows.algebra]
    | cons scope rest ih =>
        change ((∃ before, rows () before ∧ protect scope allowNone before = current) ∨
          (steps rest).eval (RecursiveRows.algebra n Nat) rows current) ↔ _
        rw [ih]
        simp [or_and_right, exists_or]
  have unfoldGrid (enabled : List (Fin n)) (current : Occurrence n Nat) :
      (grid enabled).Meaning current ↔ current = raw 0 ∨
        ∃ scope ∈ enabled, ∃ before,
          (grid enabled).Meaning before ∧ protect scope allowNone before = current := by
    rw [(grid enabled).unfold]
    change (current = raw 0 ∨ _) ↔ _
    rw [stepsExact]
  have mono (first last : List (Fin n)) (subset : ∀ scope ∈ first, scope ∈ last)
      (current : Occurrence n Nat) : (grid first).Meaning current → (grid last).Meaning current := by
    apply (grid first).least (grid last).Meaning
    intro current member
    change current = raw 0 ∨
      (steps first).eval (RecursiveRows.algebra n Nat) (fun _ => (grid last).Meaning) current at member
    rw [stepsExact] at member
    apply (unfoldGrid last current).mpr
    rcases member with head | ⟨scope, present, before, previous, same⟩
    · exact Or.inl head
    · exact Or.inr ⟨scope, subset scope present, before, previous, same⟩
  have shiftPoint (values : Fin n → Nat) (scope : Fin n) (value : Nat) :
      protect scope allowNone (point (write values scope value)) =
        point (write values scope (value + 1)) := by
    apply Occurrence.ext
    · rfl
    intro coordinate
    by_cases same : coordinate = scope <;> simp [protect, shift, point, write, allowNone, same]
  have fill (enabled : List (Fin n)) (scope : Fin n) (present : scope ∈ enabled)
      (values : Fin n → Nat) (initial : (grid enabled).Meaning (point (write values scope 0)))
      (count : Nat) : (grid enabled).Meaning (point (write values scope count)) := by
    induction count with
    | zero => exact initial
    | succ count ih =>
        apply (unfoldGrid enabled _).mpr
        exact Or.inr ⟨scope, present, _, ih, shiftPoint values scope count⟩
  have points (enabled : List (Fin n)) (values : Fin n → Nat)
      (supported : ∀ scope, scope ∉ enabled → values scope = 0) :
      (grid enabled).Meaning (point values) := by
    induction enabled generalizing values with
    | nil =>
        apply (unfoldGrid [] _).mpr
        left
        apply Occurrence.ext
        · rfl
        intro coordinate
        simp [point, raw, supported coordinate (by simp)]
    | cons scope rest ih =>
        have residual : ∀ coordinate, coordinate ∉ rest → write values scope 0 coordinate = 0 := by
          intro coordinate absent
          by_cases same : coordinate = scope
          · simp [write, same]
          · simp [write, same, supported coordinate (by simp [same, absent])]
        have previous := ih (write values scope 0) residual
        have lifted := mono rest (scope :: rest) (fun coordinate member => by simp [member]) _ previous
        have final := fill (scope :: rest) scope (by simp) values lifted (values scope)
        have same : write values scope (values scope) = values := by
          funext coordinate
          by_cases same : coordinate = scope <;> simp [write, same]
        simpa only [same] using final
  change (grid closed.enabled).Meaning occurrence ↔ _
  constructor
  · apply (grid closed.enabled).least (fun current => current.key = 0 ∧
      (∀ coordinate, 0 ≤ current.weights coordinate) ∧
      (∀ coordinate, coordinate ∉ closed.enabled → current.weights coordinate = 0))
    intro current member
    change current = raw 0 ∨
      (steps closed.enabled).eval (RecursiveRows.algebra n Nat) _ current at member
    rw [stepsExact] at member
    rcases member with rfl | ⟨scope, present, before, ⟨key, positive, supported⟩, rfl⟩
    · simp [raw]
    · refine ⟨key, ?_, ?_⟩
      · intro coordinate
        by_cases same : coordinate = scope
        · simp [protect, shift, allowNone, same]
          exact Int.add_nonneg (positive scope) (by omega)
        · simpa [protect, shift, allowNone, same] using positive coordinate
      · intro coordinate absent
        have different : coordinate ≠ scope := fun same => absent (same ▸ present)
        simpa [protect, shift, allowNone, different] using supported coordinate absent
  · rintro ⟨key, positive, supported⟩
    let values : Fin n → Nat := fun coordinate => (occurrence.weights coordinate).toNat
    have support : ∀ coordinate, coordinate ∉ closed.enabled → values coordinate = 0 := by
      intro coordinate absent
      simp [values, supported coordinate absent]
    have present := points closed.enabled values support
    have same : point values = occurrence := by
      apply Occurrence.ext key.symm
      intro coordinate
      exact Int.toNat_of_nonneg (positive coordinate)
    exact same ▸ present

def commonPoint (values : Fin n → Nat) : Common.Occurrence :=
  CommonSignedRows.encodeOccurrence (point values)

/-- The interpretation in the full Common occurrence carrier contains
exactly natural counter vectors supported on the finite enabled list. -/
theorem closed_meaning_exact (closed : ClosedRow n) (occurrence : Common.Occurrence) :
    closed.meaning occurrence ↔ ∃ values : Fin n → Nat,
      (∀ coordinate, coordinate ∉ closed.enabled → values coordinate = 0) ∧
      commonPoint values = occurrence := by
  constructor
  · rintro ⟨source, present, encoded⟩
    obtain ⟨key, positive, supported⟩ := (closed_row_exact closed source).mp present
    let values : Fin n → Nat := fun coordinate => (source.weights coordinate).toNat
    have sourceSame : point values = source := by
      apply Occurrence.ext key.symm
      intro coordinate
      exact Int.toNat_of_nonneg (positive coordinate)
    refine ⟨values, ?_, ?_⟩
    · intro coordinate absent
      simp [values, supported coordinate absent]
    · exact (congrArg CommonSignedRows.encodeOccurrence sourceSame).trans encoded
  · rintro ⟨values, supported, rfl⟩
    refine ⟨point values, (closed_row_exact closed (point values)).mpr ?_, rfl⟩
    refine ⟨rfl, ?_, ?_⟩
    · intro coordinate
      exact Int.natCast_nonneg _
    · intro coordinate absent
      simp [point, supported coordinate absent]

theorem commonPoint_injective (first last : Fin n → Nat)
    (same : commonPoint first = commonPoint last) : first = last := by
  have signed := CommonSignedRows.encodeOccurrence_injective same
  funext coordinate
  exact Int.ofNat.inj (congrArg (fun occurrence : Occurrence n Nat => occurrence.weights coordinate) signed)

end Yulang.CommonCanonicalRowGeometry
