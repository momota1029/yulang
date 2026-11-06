import Yulang.Binary64Decimal
import Yulang.Binary64Overflow

/-!
# Source decimal literals with exact static overflow rejection

Spec §3.1 and answered Q11 choose A: accept every literal whose nearest-even
binary64 result is finite, including the interval above the largest finite
exact value; reject rounding to infinity as a static error. The older
`Binary64Decimal.convert` remains the partial converter on exact magnitudes
at most the largest finite value, with all its statements unchanged.

The input here is a decoded DecimalToken. Lexical parsing, diagnostic text,
source spans and the names of infinity constants are separate boundaries.
-/

namespace Yulang.Binary64SourceDecimal

open LiteralValues
open Binary64Decimal (scaledNumerator denominator denominator_positive)

inductive Error where
  | overflow
  deriving DecidableEq, Repr

def Accepted (token : DecimalToken) : Prop :=
  Binary64Overflow.FiniteRounding (scaledNumerator token) (denominator token)

instance (token : DecimalToken) : Decidable (Accepted token) :=
  Binary64Overflow.instDecidableFiniteRounding (scaledNumerator token) (denominator token)

/-- A source elaboration result. `overflow` is a static rejection, not a
runtime effect, and accepted conversion never produces infinity or NaN. -/
def convert (token : DecimalToken) : Except Error Binary64.Value :=
  if accepted : Accepted token then
    .ok (Binary64Overflow.round token.negative (scaledNumerator token) (denominator token)
      (denominator_positive token) accepted)
  else .error .overflow

/-- Independent all-grid nearest-even semantics, including the overflow
boundary, with the token's sign retained even for an underflowed zero. -/
def Rounds (token : DecimalToken) (value : Binary64.Value) : Prop :=
  Binary64Overflow.Rounds token.negative (scaledNumerator token) (denominator token) value

theorem accepted_iff_below_midpoint (token : DecimalToken) :
    Accepted token ↔ scaledNumerator token < Binary64Overflow.midpointUnits * denominator token :=
  Binary64Overflow.finiteRounding_iff_below_midpoint _ _

theorem accepted_iff_rounds (token : DecimalToken) :
    Accepted token ↔ ∃ value, Rounds token value :=
  Binary64Overflow.finiteRounding_iff_exists_value _ _ _ (denominator_positive token)

theorem convert_success_iff (token : DecimalToken) :
    (∃ value, convert token = .ok value) ↔ Accepted token := by
  unfold convert
  split <;> simp_all

theorem convert_overflow_iff (token : DecimalToken) :
    convert token = .error .overflow ↔ ¬ Accepted token := by
  unfold convert
  split <;> simp_all

/-- Acceptance is complete for all decoded tokens, not only exact values
below the largest finite magnitude. -/
theorem convert_success_exact (token : DecimalToken) :
    (∃ value, convert token = .ok value) ↔ ∃ value, Rounds token value :=
  (convert_success_iff token).trans (accepted_iff_rounds token)

theorem convert_overflow_exact (token : DecimalToken) :
    convert token = .error .overflow ↔ ¬ ∃ value, Rounds token value := by
  rw [convert_overflow_iff, accepted_iff_rounds]

theorem convert_overflow_threshold (token : DecimalToken) :
    convert token = .error .overflow ↔
      Binary64Overflow.midpointUnits * denominator token ≤ scaledNumerator token := by
  rw [convert_overflow_iff, accepted_iff_below_midpoint]
  omega

theorem convert_correct (token : DecimalToken) (value : Binary64.Value)
    (converted : convert token = .ok value) : Rounds token value := by
  unfold convert at converted
  split at converted
  · rename_i accepted
    cases converted
    exact Binary64Overflow.round_correct _ _ _ _ accepted
  · cases converted

theorem convert_finite_contract (token : DecimalToken) (value : Binary64.Value)
    (converted : convert token = .ok value) : Binary64Decimal.Rounds token value :=
  Binary64Overflow.Rounds.finite_contract _ _ _ _ (convert_correct token value converted)

theorem convert_retains_sign (token : DecimalToken) (value : Binary64.Value)
    (converted : convert token = .ok value) : value.negative = token.negative :=
  (convert_correct token value converted).1

theorem convert_is_finite (token : DecimalToken) (value : Binary64.Value)
    (converted : convert token = .ok value) : Binary64.IsFinite value :=
  (convert_correct token value converted).2.1

theorem convert_never_nan (token : DecimalToken) (value : Binary64.Value)
    (converted : convert token = .ok value) : ¬ Binary64.IsNaN value := by
  have finite := convert_is_finite token value converted
  unfold Binary64.IsFinite Binary64.IsNaN at *
  omega

theorem accepted_of_old_range (token : DecimalToken) (within : Binary64Decimal.WithinFiniteRange token) :
    Accepted token :=
  Binary64Overflow.inFiniteRange_implies _ _ (denominator_positive token) within

/-- Every old successful conversion is retained bit for bit. The old
out-of-range boundary is not reinterpreted as the new overflow error. -/
theorem convert_agrees_with_old (token : DecimalToken) (value : Binary64.Value)
    (converted : Binary64Decimal.convert token = .ok value) : convert token = .ok value := by
  have within := (Binary64Decimal.convert_success_iff token).mp ⟨value, converted⟩
  have accepted := accepted_of_old_range token within
  simp only [Binary64Decimal.convert, dite_eq_left within, Except.ok.injEq] at converted
  simp only [convert, dite_eq_left accepted, Except.ok.injEq]
  exact (Binary64Overflow.round_agrees_with_finite _ _ _ (denominator_positive token) within).trans converted

theorem convert_above_max (token : DecimalToken) (accepted : Accepted token)
    (above : Binary64Rounding.maxUnits * denominator token ≤ scaledNumerator token) :
    convert token = .ok (Binary64Overflow.largestFinite token.negative) := by
  simp only [convert, dite_eq_left accepted, Except.ok.injEq]
  exact Binary64Overflow.round_above_max _ _ _ (denominator_positive token) accepted above

def word (token : DecimalToken) : Except Error Nat :=
  (convert token).map (fun value => (Binary64.toWord value).val)

end Yulang.Binary64SourceDecimal

namespace Yulang.LiteralValues

def binary64SourceOfDecimal (token : DecimalToken) : Except Binary64SourceDecimal.Error Binary64Literal :=
  (Binary64SourceDecimal.convert token).map Literal.float

private theorem source_map_ok {E A B : Type} (f : A → B) (input : Except E A) (output : B)
    (mapped : input.map f = .ok output) : ∃ value, input = .ok value ∧ f value = output := by
  cases input with
  | error error => cases mapped
  | ok value =>
      simp only [Except.map, Except.ok.injEq] at mapped
      exact ⟨value, rfl, mapped⟩

private theorem source_map_error_iff {E A B : Type} (f : A → B) (input : Except E A) (error : E) :
    input.map f = .error error ↔ input = .error error := by
  cases input <;> simp [Except.map]

theorem binary64SourceOfDecimal_correct (token : DecimalToken) (literal : Binary64Literal)
    (converted : binary64SourceOfDecimal token = .ok literal) :
    ∃ value, literal = .float value ∧ Binary64SourceDecimal.Rounds token value := by
  obtain ⟨value, result, same⟩ := source_map_ok Literal.float (Binary64SourceDecimal.convert token) literal converted
  exact ⟨value, same.symm, Binary64SourceDecimal.convert_correct token value result⟩

theorem binary64SourceOfDecimal_kind (token : DecimalToken) (literal : Binary64Literal)
    (converted : binary64SourceOfDecimal token = .ok literal) : literal.kind = .float := by
  obtain ⟨value, rfl, _⟩ := binary64SourceOfDecimal_correct token literal converted
  rfl

theorem binary64SourceOfDecimal_overflow_exact (token : DecimalToken) :
    binary64SourceOfDecimal token = .error .overflow ↔
      ¬ ∃ value, Binary64SourceDecimal.Rounds token value := by
  unfold binary64SourceOfDecimal
  rw [source_map_error_iff, Binary64SourceDecimal.convert_overflow_exact]

end Yulang.LiteralValues
