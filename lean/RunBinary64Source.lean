import Yulang.Binary64SourceExamples

open Yulang Yulang.LiteralValues Yulang.Binary64SourceExamples

private def checkWord (label : String) (token : DecimalToken) (expected : Nat) : IO Unit := do
  match Binary64SourceDecimal.word token with
  | .ok actual =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected word {expected}, got {actual}")
  | .error .overflow => throw (IO.userError s!"{label}: unexpected static overflow")
  IO.println s!"{label}: passed"

private def checkOverflow (label : String) (token : DecimalToken) : IO Unit := do
  match Binary64SourceDecimal.convert token with
  | .error .overflow => IO.println s!"{label}: passed"
  | .ok value =>
      throw (IO.userError s!"{label}: expected static overflow, got word {(Binary64.toWord value).val}")

def main : IO Unit := do
  checkWord "source positive zero with huge exponent" ⟨false, 0, 1000000000⟩ 0
  checkWord "source negative zero with huge exponent" ⟨true, 0, -1000000000⟩ 0x8000000000000000
  checkWord "source decimal 0.1" ⟨false, 1, -1⟩ 0x3fb999999999999a
  checkWord "negative underflow retains the zero sign" ⟨true, 5 ^ 1075, -1075⟩ 0x8000000000000000
  for negative in [false, true] do
    let label := if negative then "negative" else "positive"
    let expected := (if negative then 2 ^ 63 else 0) + 0x7fefffffffffffff
    checkWord s!"{label} largest finite source literal"
      ⟨negative, (2 ^ 53 - 1) * 2 ^ 971, 0⟩ expected
    checkWord s!"{label} 1.7976931348623158e308 rounds to largest finite" (nearMax negative) expected
    checkWord s!"{label} one below the exact overflow midpoint" (justBelowMidpoint negative) expected
    checkOverflow s!"{label} exact midpoint rounds outward to even" (atMidpoint negative)
    checkOverflow s!"{label} one above the exact overflow midpoint" (justAboveMidpoint negative)
    checkOverflow s!"{label} 1.7976931348623159e308" ⟨negative, 17976931348623159, 292⟩
    checkOverflow s!"{label} 1.0e309" ⟨negative, 1, 309⟩
    match Binary64Decimal.convert (nearMax negative) with
    | .error .outsideFiniteRange =>
        IO.println s!"{label} legacy partial-converter boundary is unchanged: passed"
    | .ok _ => throw (IO.userError s!"{label}: legacy exact-magnitude boundary changed")
  IO.println "All source binary64 finite-rounding and static-overflow regressions passed."
