import Yulang.SourceDataOrderExamples

open Yulang.Inference Yulang.SourceDataRuntime Yulang.SourceDataOrder
open Yulang.SourceDataOrderExamples

private def checkedTrace (name : String) (expression : Expr) (expected : Trace) : IO Observation := do
  let observed := run [] expression
  unless decide (observed.trace = expected) do
    throw (IO.userError s!"{name}: unexpected evaluation trace")
  pure observed

private def checkedError (name : String) (expression : Expr) (expected : Trace) (error : Error) : IO Unit := do
  let observed ← checkedTrace name expression expected
  match observed.result with
  | .error actual =>
      unless decide (actual = error) do throw (IO.userError s!"{name}: wrong runtime error")
  | .ok _ => throw (IO.userError s!"{name}: unexpected success")

def main : IO Unit := do
  let hidden ← checkedTrace "hidden field" hiddenRecord hiddenOrder
  match hidden.result with
  | .ok (.record [(0, .base .int), (1, .base .bool)]) => pure ()
  | _ => throw (IO.userError "hidden field: wrong stored record")
  IO.println "hidden field: string visited in order, erased from stored fields"
  let present ← checkedTrace "present default" presentDefault
    [presentDefault, baseRecord, .lit .int, .emptyRecord, .lit .str]
  match present.result with
  | .ok (.record [(0, .base .int)]) => pure ()
  | _ => throw (IO.userError "present default: existing field did not win")
  let absent ← checkedTrace "absent default" absentDefault
    [absentDefault, baseRecord, .lit .int, .emptyRecord, .lit .bool]
  match absent.result with
  | .ok (.record [(0, .base .int), (1, .base .bool)]) => pure ()
  | _ => throw (IO.userError "absent default: fallback was not appended")
  IO.println "record defaults: base then fallback, for both present and absent fields"
  checkedError "hidden failure" failingHidden
    [failingHidden, .lit .int, failingHiddenTail, .var 7] (.unboundVariable 7)
  checkedError "fallback failure" failingFallback
    [failingFallback, baseRecord, .lit .int, .emptyRecord, .var 9] (.unboundVariable 9)
  checkedError "base failure" failingBase [failingBase, .var 3] (.unboundVariable 3)
  checkedError "fallback before shape check" invalidBaseFailingFallback
    [invalidBaseFailingFallback, .lit .int, .var 4] (.unboundVariable 4)
  checkedError "unused definition" unusedLet [unusedLet, .var 7] (.unboundVariable 7)
  checkedError "left pair failure" failingPair [failingPair, .var 5] (.unboundVariable 5)
  IO.println "failures: preserve the evaluated prefix and stop before later expressions"
  checkedError "unsupported application" unsupportedApplication [unsupportedApplication] .unsupported
  IO.println "source data evaluation-order tour passed"
