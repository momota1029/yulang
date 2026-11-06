import Yulang.LiteralValueExamples
import Yulang.NominalConstructionExamples
import Yulang.NominalDataConstructionExamples

open Yulang.LiteralValues

private def noFloat : Empty → Empty → Bool := fun impossible => Empty.elim impossible

def main : IO Unit := do
  IO.println s!"large integer literal: {matchCheck noFloat (.int 184467440737095516170000000000000000001) (.int 184467440737095516170000000000000000001)}"
  IO.println s!"integer and string remain distinct: {!matchCheck noFloat (.int 42) (.str "42")}"
  IO.println s!"closed range lower bound: {intRangeCheck (some (-7)) (some 3) (.int (-7) : Literal Empty)}"
  IO.println s!"closed range upper bound: {intRangeCheck (some (-7)) (some 3) (.int 3 : Literal Empty)}"
  match (Yulang.CaseDataTerms.eval [] (Yulang.NominalDataConstructionExamples.point 3 4 99)).result with
  | .ok (.nominal 10 0 (.record [(0, .literal (.int 3)), (1, .literal (.int 4))])) => pure ()
  | _ => throw (IO.userError "computed struct construction: wrong value")
  match (Yulang.CaseDataTerms.eval [] (Yulang.NominalDataConstructionExamples.justValue 77)).result with
  | .ok (.nominal 20 1 (.literal (.int 77))) => pure ()
  | _ => throw (IO.userError "computed enum construction: wrong value")
  match (Yulang.CaseDataTerms.eval [] (Yulang.NominalDataConstructionExamples.listValue 11 20)).result with
  | .ok (.list [.literal (.int 11), .literal (.int 20)]) => pure ()
  | _ => throw (IO.userError "computed list construction: wrong value")
  IO.println "computed struct, enum and list payloads evaluated successfully"
  IO.println "Nominal construction, cast suppression, EOF and list-view equalities checked by Lean."
