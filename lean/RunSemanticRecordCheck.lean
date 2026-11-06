import Yulang.SemanticRecordCheckerExamples

/-!
Run the actual semantic record ground checker:

    lake env lean --trust=0 --run RunSemanticRecordCheck.lean

The final boundary case belongs to the minimum congruence relation. It is
not a source-language type-error expectation for arbitrary record tails.
-/

open Yulang SemanticRecordCheckerExamples

def main : IO Unit := do
  for (name, source, target, expected) in cases do
    let result := SemanticRecordChecker.check pureRows source target
    if result != expected then
      throw (IO.userError (name ++ ": unexpected subtype result"))
    IO.println (name ++ " => " ++ toString result)
  let before : StructuralBase.Ty Bool := .arrow (.base .int) true (.base .int) false
  let after : StructuralBase.Ty Bool := .arrow (.base .int) false (.base .int) false
  if !SemanticRecordChecker.check boolRows before after || SemanticRecordChecker.check boolRows after before then
    throw (IO.userError "contravariant input row comparison changed")
  IO.println "contravariant input rows => forward accepted, reverse rejected"
  if !quotientEqual (SemanticRecordQuotient.mk proper) (SemanticRecordQuotient.mk redundant) ||
      !quotientCheck (SemanticRecordQuotient.mk shadowed) (SemanticRecordQuotient.mk proper) ||
      quotientEqual (SemanticRecordQuotient.mk integer) (SemanticRecordQuotient.mk string) then
    throw (IO.userError "quotient equality or order differs from semantic representatives")
  IO.println "quotient equality and order => all three checks passed"
  IO.println "semantic record checker tour passed"
