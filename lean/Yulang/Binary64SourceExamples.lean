import Yulang.Binary64SourceDecimal

/-!
# Answered Q11 boundary regressions

All examples retain either sign. The closed arithmetic proofs below use
kernel reduction on exact natural numbers; no host floating-point result
or native decision is used as evidence. The legacy partial converter is
explicitly checked alongside the source converter.
-/

namespace Yulang.Binary64SourceExamples

open LiteralValues

set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

/-- The literal `1.7976931348623158e308`, with either sign. -/
def nearMax (negative : Bool) : DecimalToken := ⟨negative, 17976931348623158, 292⟩

def midpointMagnitude : Nat := 2 ^ 1024 - 2 ^ 970

def justBelowMidpoint (negative : Bool) : DecimalToken := ⟨negative, midpointMagnitude - 1, 0⟩

def atMidpoint (negative : Bool) : DecimalToken := ⟨negative, midpointMagnitude, 0⟩

def justAboveMidpoint (negative : Bool) : DecimalToken := ⟨negative, midpointMagnitude + 1, 0⟩

theorem nearMax_outside_old_range (negative : Bool) : ¬ Binary64Decimal.WithinFiniteRange (nearMax negative) := by
  cases negative <;> decide

theorem nearMax_keeps_old_boundary (negative : Bool) :
    Binary64Decimal.convert (nearMax negative) = .error .outsideFiniteRange :=
  (Binary64Decimal.convert_boundary_iff _).mpr (nearMax_outside_old_range negative)

theorem nearMax_rounds_to_largest (negative : Bool) :
    Binary64SourceDecimal.convert (nearMax negative) = .ok (Binary64Overflow.largestFinite negative) := by
  apply Binary64SourceDecimal.convert_above_max
  · cases negative <;> decide
  · cases negative <;> decide

theorem justBelowMidpoint_rounds_to_largest (negative : Bool) :
    Binary64SourceDecimal.convert (justBelowMidpoint negative) =
      .ok (Binary64Overflow.largestFinite negative) := by
  apply Binary64SourceDecimal.convert_above_max
  · cases negative <;> decide
  · cases negative <;> decide

theorem atMidpoint_rejected (negative : Bool) :
    Binary64SourceDecimal.convert (atMidpoint negative) = .error .overflow := by
  apply (Binary64SourceDecimal.convert_overflow_threshold _).mpr
  cases negative <;> decide

theorem justAboveMidpoint_rejected (negative : Bool) :
    Binary64SourceDecimal.convert (justAboveMidpoint negative) = .error .overflow := by
  apply (Binary64SourceDecimal.convert_overflow_threshold _).mpr
  cases negative <;> decide

theorem nextDecimal_rejected (negative : Bool) :
    Binary64SourceDecimal.convert ⟨negative, 17976931348623159, 292⟩ = .error .overflow := by
  apply (Binary64SourceDecimal.convert_overflow_threshold _).mpr
  cases negative <;> decide

theorem huge_rejected (negative : Bool) :
    Binary64SourceDecimal.convert ⟨negative, 1, 309⟩ = .error .overflow := by
  apply (Binary64SourceDecimal.convert_overflow_threshold _).mpr
  cases negative <;> decide

end Yulang.Binary64SourceExamples
