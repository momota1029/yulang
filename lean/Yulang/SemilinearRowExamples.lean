import Yulang.SemilinearRows

/-!
# Several cycles, several coordinates, and a genuine seed

One cycle raises the first coordinate. A mutually recursive two-slot cycle
lowers the second coordinate. Their semilinear presentation contains every
`(positive, -negative)` pair, with no bound on either count. An unrelated head
does not change the fixed-key interpretation. The checked entry point also
retains the boundary of the theorem: a remaining residual point guard does not
receive an unguarded presentation.
-/

namespace Yulang.SemilinearRowExamples

open Directed
open RecursiveRows (Problem Derives)
open SemilinearRows

def system : Problem 2 Nat (Fin 2) :=
  [⟨0, .head 7⟩, ⟨0, .head 8⟩,
   ⟨0, .protect 0 allowNone (.var 0)⟩,
   ⟨1, .release 1 allowNone (.var 0)⟩,
   ⟨0, .var 1⟩]

def weights (positive negative : Nat) : SemilinearWeights.Weight 2 :=
  fun coordinate => if coordinate = 0 then (positive : Int) else -(negative : Int)

def point (positive negative : Nat) : Occurrence 2 Nat := occurrence 7 (weights positive negative)

theorem two_coordinates (coordinate : Fin 2) : coordinate = 0 ∨ coordinate = 1 := by
  have values : coordinate.val = 0 ∨ coordinate.val = 1 := by omega
  exact values.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))

theorem protect_point (positive negative : Nat) :
    protect 0 allowNone (point positive negative) = point (positive + 1) negative := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  rcases two_coordinates coordinate with rfl | rfl <;>
    simp [protect, shift, allowNone, point, occurrence, weights, Int.natCast_add]

theorem release_point (positive negative : Nat) :
    release 1 allowNone (point positive negative) = point positive (negative + 1) := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  rcases two_coordinates coordinate with rfl | rfl <;>
    simp [release, shift, allowNone, point, occurrence, weights, Int.natCast_add]
  omega

theorem positive_axis (positive : Nat) : Derives system 0 (point positive 0) := by
  induction positive with
  | zero =>
      have zeroPoint : point 0 0 = raw 7 := by
        apply Occurrence.ext
        · rfl
        intro coordinate
        simp [point, occurrence, weights, raw]
      rw [zeroPoint]
      exact .rule (rule := ⟨0, .head 7⟩) (by simp [system]) (.head 7)
  | succ positive ih =>
      rw [← protect_point]
      exact .rule (rule := ⟨0, .protect 0 allowNone (.var 0)⟩) (by simp [system]) (.protect (.var ih))

/-- Both cycle counters range over all natural numbers, and the second
coordinate is negative. The statement is not a bounded search result. -/
theorem whole_quadrant_derived (positive negative : Nat) : Derives system 0 (point positive negative) := by
  induction negative with
  | zero => exact positive_axis positive
  | succ negative ih =>
      rw [← release_point]
      apply Derives.rule (rule := ⟨0, .var 1⟩) (by simp [system])
      apply RecursiveRows.ExprDerives.var
      exact .rule (rule := ⟨1, .release 1 allowNone (.var 0)⟩) (by simp [system]) (.release (.var ih))

theorem all_slots : ∀ slot : Fin 2, slot ∈ [0, 1] := by
  intro slot
  rcases two_coordinates slot with rfl | rfl <;> simp

theorem system_unguarded : Unguarded 7 (RecursiveRowGraph.compile system) :=
  (checkUnguarded_exact 7 _).mp (by decide)

theorem whole_quadrant_in_presentation (positive negative : Nat) :
    SemilinearWeights.Meaning (presentation 7 [0, 1] system 0) (weights positive negative) :=
  (presentation_exact 7 [0, 1] all_slots system system_unguarded 0 _).mpr
    (whole_quadrant_derived positive negative)

theorem summarized_system : summarize 7 [0, 1] system 0 = some (presentation 7 [0, 1] system 0) := by
  have checked := (checkUnguarded_exact 7 _).mpr system_unguarded
  simp [summarize, checked]

def guarded : Problem 1 Nat Unit :=
  [⟨(), .residual [7] (.protect 0 allowNone (.var ()))⟩, ⟨(), .head 7⟩]

/-- Even a guard after a nonzero shift must be retained. Its excluded input
is a negative occurrence; looking only at zero or net displacement would miss it. -/
theorem residual_is_not_silently_erased : summarize 7 [()] guarded () = none := by decide

end Yulang.SemilinearRowExamples
