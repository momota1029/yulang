import Yulang.SemilinearDecisions

/-!
# Executable semilinear-membership regressions

The checks exercise the actual finite-state decision procedure: cancellation
between positive and negative periods, divisibility obstructions, independent
coordinates, empty support, zero periods and zero-dimensional weights.
-/

namespace Yulang.SemilinearDecisions.Examples

open SemilinearWeights

def scalar (value : Int) : Weight 1 := fun _ => value

def plane (first second : Int) : Weight 2 := fun coordinate =>
  if coordinate.val = 0 then first else second

set_option maxRecDepth 100000 in
theorem signed_cancellation_accepted : checkSpan [scalar 2, scalar (-3)] (scalar 1) = true := by
  decide

set_option maxRecDepth 100000 in
theorem divisibility_obstruction_rejected : checkSpan [scalar 2, scalar (-4)] (scalar 1) = false := by
  decide

set_option maxRecDepth 100000 in
theorem one_sided_negative_rejected : checkSpan [scalar 1] (scalar (-1)) = false := by
  decide

set_option maxRecDepth 100000 in
theorem two_coordinate_periods_accepted :
    checkSpan [plane 1 0, plane 0 (-1)] (plane 1 (-1)) = true := by
  decide

set_option maxRecDepth 100000 in
theorem wrong_coordinate_sign_rejected :
    checkSpan [plane 1 0, plane 0 (-1)] (plane (-1) 1) = false := by
  decide

theorem empty_generators_contain_zero : checkSpan ([] : List (Weight 1)) zero = true := by decide
theorem empty_generators_reject_nonzero : checkSpan [] (scalar 1) = false := by decide
theorem zero_periods_contain_zero : checkSpan [scalar 0, scalar 0] zero = true := by decide
theorem zero_periods_reject_nonzero : checkSpan [scalar 0, scalar 0] (scalar 1) = false := by decide
theorem empty_semilinear_rejects : check ([] : Semi 1) zero = false := by decide
theorem zero_dimension_point_accepted : check [Linear.point (zero : Weight 0)] zero = true := by decide

set_option maxRecDepth 100000 in
theorem finite_union_uses_second_component :
    check [⟨scalar 0, [scalar 2]⟩, ⟨scalar 1, [scalar 2]⟩] (scalar 3) = true := by
  decide

theorem cancellation_has_unbounded_coefficient_witnesses (count : Nat) :
    checkSpan [scalar 2, scalar (-3)] (scalar (count : Int)) = true := by
  apply (checkSpan_exact _ _).mpr
  have combination := BinaryCarries.combine_span [scalar 2, scalar (-3)] [2 * count, count]
  have same : BinaryCarries.combine [scalar 2, scalar (-3)] [2 * count, count] = scalar count := by
    funext coordinate
    simp only [BinaryCarries.combine, BinaryCarries.scale, scalar, add, zero, Int.natCast_mul]
    omega
  rw [same] at combination
  exact combination

end Yulang.SemilinearDecisions.Examples
