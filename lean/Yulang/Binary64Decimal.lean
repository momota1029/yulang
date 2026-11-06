import Yulang.Binary64Rounding

/-!
# Decimal tokens to finite binary64 values

This is an executable, integer-only conversion, with a nearest/ties-even
proof over every finite binary64 magnitude. Decimal digits and exponents
are arbitrary-precision input data. The binary search is over the fixed
64-bit representation and is structurally terminating by interval width.

This partial converter deliberately retains its original exact-magnitude
domain. `outsideFiniteRange` is an internal boundary, not a static rejection:
some larger exact values still round to the largest finite binary64 value.
The complete source policy from spec §3.1 and answered Q11 is implemented
separately in `Binary64SourceDecimal`, preserving this converter's contract.
-/

namespace Yulang.Binary64Decimal

open LiteralValues Binary64Rounding

structure Fraction where
  numerator : Nat
  denominator : Nat
  positive : 0 < denominator

/-- Exact nonnegative magnitude of a decoded decimal. Zero is short-circuited
before exponentiation, while the token's sign is retained by conversion. -/
def magnitudeFraction (token : DecimalToken) : Fraction :=
  if token.significand = 0 then ⟨0, 1, by decide⟩ else
  match token.exponent with
  | .ofNat exponent => ⟨token.significand * 10 ^ exponent, 1, by decide⟩
  | .negSucc exponent => ⟨token.significand, 10 ^ (exponent + 1), Nat.pow_pos (by decide)⟩

/-- Numerator at the common binary64 scale; division is never rounded here. -/
def scaledNumerator (token : DecimalToken) : Nat := (magnitudeFraction token).numerator * 2 ^ 1074

def denominator (token : DecimalToken) : Nat := (magnitudeFraction token).denominator

theorem denominator_positive (token : DecimalToken) : 0 < denominator token :=
  (magnitudeFraction token).positive

/-- Independent exact-rational meaning of a nonnegative decimal magnitude. -/
def RepresentsMagnitude (token : DecimalToken) (numerator denominator : Nat) : Prop :=
  0 < denominator ∧ match token.exponent with
    | .ofNat exponent => numerator = token.significand * 10 ^ exponent * denominator
    | .negSucc exponent => numerator * 10 ^ (exponent + 1) = token.significand * denominator

theorem magnitudeFraction_exact (token : DecimalToken) :
    RepresentsMagnitude token (magnitudeFraction token).numerator (magnitudeFraction token).denominator := by
  refine ⟨(magnitudeFraction token).positive, ?_⟩
  by_cases zero : token.significand = 0
  · cases token.exponent <;> simp [magnitudeFraction, zero]
  · cases exponent : token.exponent <;> simp [magnitudeFraction, zero, exponent]

def WithinFiniteRange (token : DecimalToken) : Prop :=
  InFiniteRange (scaledNumerator token) (denominator token)

instance (token : DecimalToken) : Decidable (WithinFiniteRange token) :=
  Binary64Rounding.instDecidableInFiniteRange (scaledNumerator token) (denominator token)

inductive Boundary where
  | outsideFiniteRange
  deriving DecidableEq, Repr

/-- A partial conversion result; `outsideFiniteRange` is not equivalent to
source overflow. No host `Float`, external solver or supplied interpretation
function participates in the finite-range result. -/
def convert (token : DecimalToken) : Except Boundary Binary64.Value :=
  if within : WithinFiniteRange token then
    .ok (roundFinite token.negative (scaledNumerator token) (denominator token)
      (denominator_positive token) within)
  else .error .outsideFiniteRange

def Rounds (token : DecimalToken) (value : Binary64.Value) : Prop :=
  RoundsToEven token.negative (scaledNumerator token) (denominator token) value

theorem convert_success_iff (token : DecimalToken) :
    (∃ value, convert token = .ok value) ↔ WithinFiniteRange token := by
  unfold convert
  split <;> simp_all

theorem convert_boundary_iff (token : DecimalToken) :
    convert token = .error .outsideFiniteRange ↔ ¬ WithinFiniteRange token := by
  unfold convert
  split <;> simp_all

theorem convert_correct (token : DecimalToken) (value : Binary64.Value)
    (converted : convert token = .ok value) : Rounds token value := by
  unfold convert at converted
  split at converted
  · rename_i within
    cases converted
    exact roundFinite_correct _ _ _ _ within
  · cases converted

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

/-- Storage words make concrete conversion regressions readable while leaving
the public result as a binary64 value. -/
def word (token : DecimalToken) : Except Boundary Nat :=
  (convert token).map (fun value => (Binary64.toWord value).val)

end Yulang.Binary64Decimal

namespace Yulang.LiteralValues

def binary64OfDecimal (token : DecimalToken) : Except Binary64Decimal.Boundary Binary64Literal :=
  (Binary64Decimal.convert token).map Literal.float

private theorem map_ok {E A B : Type} (f : A → B) (input : Except E A) (output : B)
    (mapped : input.map f = .ok output) : ∃ value, input = .ok value ∧ f value = output := by
  cases input with
  | error error => cases mapped
  | ok value =>
      simp only [Except.map, Except.ok.injEq] at mapped
      exact ⟨value, rfl, mapped⟩

theorem binary64OfDecimal_correct (token : DecimalToken) (literal : Binary64Literal)
    (converted : binary64OfDecimal token = .ok literal) :
    ∃ value, literal = .float value ∧ Binary64Decimal.Rounds token value := by
  obtain ⟨value, result, same⟩ := map_ok Literal.float (Binary64Decimal.convert token) literal converted
  exact ⟨value, same.symm, Binary64Decimal.convert_correct token value result⟩

theorem binary64OfDecimal_kind (token : DecimalToken) (literal : Binary64Literal)
    (converted : binary64OfDecimal token = .ok literal) : literal.kind = .float := by
  obtain ⟨value, rfl, _⟩ := binary64OfDecimal_correct token literal converted
  rfl

end Yulang.LiteralValues
