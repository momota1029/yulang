import Yulang.Binary64Decimal

open Yulang Yulang.LiteralValues Yulang.Binary64Decimal

private def checkWord (label : String) (token : DecimalToken) (expected : Nat) : IO Unit := do
  match word token with
  | .ok actual =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected word {expected}, got {actual}")
  | .error boundary => throw (IO.userError s!"{label}: unexpected conversion boundary {repr boundary}")
  IO.println s!"{label}: passed"

private def check (label : String) (actual : Bool) : IO Unit := do
  if !actual then throw (IO.userError s!"{label}: failed")
  IO.println s!"{label}: passed"

def main : IO Unit := do
  -- Zero must not expand an arbitrarily large decimal exponent.
  checkWord "positive zero" ⟨false, 0, 1000000000⟩ 0
  checkWord "negative zero" ⟨true, 0, -1000000000⟩ 0x8000000000000000
  checkWord "decimal 0.1 rounds to binary64" ⟨false, 1, -1⟩ 0x3fb999999999999a
  checkWord "integer midpoint chooses lower even significand"
    ⟨false, 9007199254740993, 0⟩ 0x4340000000000000
  checkWord "integer midpoint chooses upper even significand"
    ⟨false, 9007199254740995, 0⟩ 0x4340000000000002
  checkWord "least positive subnormal" ⟨false, 5 ^ 1074, -1074⟩ 1
  checkWord "half a subnormal rounds to even zero" ⟨false, 5 ^ 1075, -1075⟩ 0
  checkWord "one and a half subnormals round to even two" ⟨false, 3 * 5 ^ 1075, -1075⟩ 2
  checkWord "largest finite binary64" ⟨false, (2 ^ 53 - 1) * 2 ^ 971, 0⟩ 0x7fefffffffffffff
  let quietNaN := Binary64.ofWord ⟨0x7ff8000000000001, by decide⟩
  check "signed zeros compare equal" (Binary64.eqCheck (Binary64.zero false) (Binary64.zero true))
  check "NaN does not compare equal to itself" (!(Binary64.eqCheck quietNaN quietNaN))
  check "positive infinity compares equal to itself"
    (Binary64.eqCheck (Binary64.infinity false) (Binary64.infinity false))
  check "opposite infinities remain distinct"
    (!(Binary64.eqCheck (Binary64.infinity false) (Binary64.infinity true)))
  match convert ⟨false, 1, 309⟩ with
  | .error .outsideFiniteRange => pure ()
  | .ok _ => throw (IO.userError "outside-finite-range token: missing policy boundary")
  IO.println "out-of-range source policy remains an explicit boundary"
  IO.println "All binary64 conversion and comparison regressions passed."
