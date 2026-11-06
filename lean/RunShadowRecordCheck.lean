import Yulang.ShadowRecordCheckerExamples

/-!
Execute the decision-40 ground checker and actual quotient equality:

    lake env lean --trust=0 --run RunShadowRecordCheck.lean
-/

open Yulang ShadowRecordCheckerExamples

def main : IO Unit := do
  for (name, source, target, expected) in cases do
    let result := ShadowRecordChecker.check pureRows source target
    if result != expected then
      throw (IO.userError (name ++ ": unexpected shadow-record subtype result"))
    IO.println (name ++ " => " ++ toString result)
  let equal := ShadowRecordQuotientDecisions.equal pureRows pureRows_exact pureRows_refl pureRows_trans
    (ShadowRecordQuotient.mk hidden) (ShadowRecordQuotient.mk flat)
  if !equal then
    throw (IO.userError "opaque hidden-field quotient equality failed")
  IO.println "opaque hidden-field quotient equality => true"
  IO.println "shadow record ground checker tour passed"
