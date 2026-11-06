import Yulang.SourceDataSafetyExamples

/-! Execute original source expressions. No typing plan or shape annotation
is passed to the evaluator. Kernel theorems establish the accompanying safety
and inference results separately. -/

open Yulang Inference SourceDataRuntime SourceDataSafetyExamples

def main : IO Unit := do
  match eval [] repeated with
  | .ok (.record [(0, .base .int), (1, .base .bool)]) =>
      IO.println "first-field-wins => hidden string erased from stored record"
  | _ => throw (IO.userError "incorrect stored record after shadowing")
  match eval [] selected, eval [] (.field 1 repeated) with
  | .ok (.base .int), .ok (.base .bool) =>
      IO.println "let and field lookup => integer and retained boolean"
  | _, _ => throw (IO.userError "field lookup or let result is wrong")
  match eval [] (.record 0 (.lit .int) (.lit .str)), eval [] (.fst (.lit .int)) with
  | .error .expectedRecord, .error .expectedPair =>
      IO.println "untyped invalid shapes => explicit runtime errors"
  | _, _ => throw (IO.userError "invalid runtime shapes were accepted")
  match eval [] (.letE (.field 7 repeated) (.lit .unit)) with
  | .error (.missingField 7) =>
      IO.println "strict let => unused right-hand side is still evaluated"
  | _ => throw (IO.userError "strict let incorrectly skipped its right-hand side")
  match eval [] (.lam (.var 0)) with
  | .error .unsupported => IO.println "function => outside this data evaluator"
  | _ => throw (IO.userError "unsupported function received a fabricated result")
  IO.println "source data safety tour passed"
