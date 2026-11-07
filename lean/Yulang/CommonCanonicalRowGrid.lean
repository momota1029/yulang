import Yulang.RecursiveRowDisplay
import Yulang.CommonEffectRequestGeneration

/-!
# Fixed finite signed-row descriptions for counter configurations

The quadrant and axes are closed `AsRow` syntax, with their existing least
fixed-point meaning. They are not arbitrary row predicates supplied as input
constants. Their Common interpretation retains the key and both coordinates.
-/

namespace Yulang.CommonCanonicalRowGrid

open Directed

def point (first last : Nat) : Occurrence 2 Nat :=
  ⟨0, fun coordinate => if coordinate = 0 then first else last⟩

def quadrant : RecursiveRowDisplay.AsRow 2 Nat :=
  ⟨"quadrant", .union (.head 0) (.union
    (.protect 0 allowNone (.var ())) (.protect 1 allowNone (.var ())))⟩

def axis (scope : Fin 2) : RecursiveRowDisplay.AsRow 2 Nat :=
  ⟨"axis", .union (.head 0) (.protect scope allowNone (.var ()))⟩

def axisPoint (scope : Fin 2) (count : Nat) : Occurrence 2 Nat :=
  ⟨0, fun coordinate => if coordinate = scope then count else 0⟩

/-- The existing least-row binder for two positive shifts denotes exactly
the nonnegative two-counter configurations, with key zero. -/
theorem quadrant_exact (occurrence : Occurrence 2 Nat) :
    quadrant.Meaning occurrence ↔ ∃ first last : Nat, occurrence = point first last := by
  have shiftFirst (first last : Nat) :
      protect 0 allowNone (point first last) = point (first + 1) last := by
    apply Occurrence.ext
    · rfl
    intro coordinate
    by_cases same : coordinate = 0 <;> simp [protect, shift, point, allowNone, same]
  have shiftLast (first last : Nat) :
      protect 1 allowNone (point first last) = point first (last + 1) := by
    apply Occurrence.ext
    · rfl
    intro coordinate
    by_cases same : coordinate = 0
    · simp [protect, shift, point, allowNone, same]
    · have other : coordinate = (1 : Fin 2) := by omega
      simp [protect, shift, point, allowNone, other]
  have present (first last : Nat) : quadrant.Meaning (point first last) := by
    induction first with
    | zero =>
      induction last with
      | zero =>
        apply (quadrant.unfold _).mpr
        left
        apply Occurrence.ext
        · rfl
        intro coordinate
        simp [point, raw]
      | succ last ih =>
        apply (quadrant.unfold _).mpr
        right; right
        exact ⟨point 0 last, ih, shiftLast 0 last⟩
    | succ first ih =>
      apply (quadrant.unfold _).mpr
      right; left
      exact ⟨point first last, ih, shiftFirst first last⟩
  constructor
  · apply quadrant.least (fun occurrence => ∃ first last, occurrence = point first last)
    intro current member
    change current = raw 0 ∨
      (∃ before, (∃ first last, before = point first last) ∧ protect 0 allowNone before = current) ∨
      (∃ before, (∃ first last, before = point first last) ∧ protect 1 allowNone before = current) at member
    rcases member with same | ⟨before, ⟨first, last, same⟩, moved⟩ |
      ⟨before, ⟨first, last, same⟩, moved⟩
    · refine ⟨0, 0, ?_⟩
      rw [same]
      apply Occurrence.ext
      · rfl
      intro coordinate
      simp [raw, point]
    · subst before
      exact ⟨first + 1, last, moved.symm.trans (shiftFirst first last)⟩
    · subst before
      exact ⟨first, last + 1, moved.symm.trans (shiftLast first last)⟩
  · rintro ⟨first, last, rfl⟩
    exact present first last

/-- A single positive-shift binder denotes exactly its nonnegative axis. -/
theorem axis_exact (scope : Fin 2) (occurrence : Occurrence 2 Nat) :
    (axis scope).Meaning occurrence ↔ ∃ count : Nat, occurrence = axisPoint scope count := by
  have shiftAxis (count : Nat) :
      protect scope allowNone (axisPoint scope count) = axisPoint scope (count + 1) := by
    apply Occurrence.ext
    · rfl
    intro coordinate
    by_cases same : coordinate = scope <;> simp [protect, shift, axisPoint, allowNone, same]
  have zero : raw 0 = axisPoint scope 0 := by
    apply Occurrence.ext
    · rfl
    intro coordinate
    simp [raw, axisPoint]
  have present (count : Nat) : (axis scope).Meaning (axisPoint scope count) := by
    induction count with
    | zero =>
        apply ((axis scope).unfold _).mpr
        exact Or.inl zero.symm
    | succ count ih =>
        apply ((axis scope).unfold _).mpr
        exact Or.inr ⟨axisPoint scope count, ih, shiftAxis count⟩
  constructor
  · apply (axis scope).least (fun occurrence => ∃ count, occurrence = axisPoint scope count)
    intro current member
    change current = raw 0 ∨
      ∃ before, (∃ count, before = axisPoint scope count) ∧ protect scope allowNone before = current at member
    rcases member with same | ⟨before, ⟨count, rfl⟩, moved⟩
    · exact ⟨0, same.trans zero⟩
    · exact ⟨count + 1, moved.symm.trans (shiftAxis count)⟩
  · rintro ⟨count, rfl⟩
    exact present count

def embedSet (row : RecursiveRows.SetRow n Nat) : Common.Row :=
  fun occurrence => ∃ source, row source ∧ CommonSignedRows.encodeOccurrence source = occurrence

/-- The fixed signed-to-Common representation preserves and reflects row
inclusion even for infinite least sets and arbitrary signed-set assignments. -/
theorem embedSet_le_iff (first last : RecursiveRows.SetRow n Nat) :
    (∀ occurrence, first occurrence → last occurrence) ↔
      Common.rowLe (embedSet first) (embedSet last) := by
  constructor
  · intro below occurrence member
    obtain ⟨source, present, rfl⟩ := member
    exact ⟨source, below source present, rfl⟩
  · intro below occurrence present
    obtain ⟨source, member, same⟩ := below (CommonSignedRows.encodeOccurrence occurrence)
      ⟨occurrence, present, rfl⟩
    exact CommonSignedRows.encodeOccurrence_injective same ▸ member

end Yulang.CommonCanonicalRowGrid
