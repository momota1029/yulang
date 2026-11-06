import Yulang.RigidRecordValueInferenceExamples

/-!
Run the actual source-data inference entry:

    lake env lean --trust=0 --run RunRigidRecordInference.lean

Each successful result is a finite scheme with unconstrained parameters.
General source functions and variables are explicitly outside this entry.
-/

open Yulang RigidRecordValueInference RigidRecordValueInferenceExamples

def main : IO Unit := do
  for (name, expression, expected) in cases do
    let result := infer expression
    if result.status != expected then
      throw (IO.userError (name ++ ": unexpected inference status"))
    match result with
    | .unsupported => IO.println (name ++ " => unsupported")
    | .rejected => IO.println (name ++ " => rejected; no original typing")
    | .inferred plan =>
        IO.println (name ++ " => inferred; " ++ toString plan.parameterCount ++ " free value parameters")
  IO.println "nested record retains the widened non-rigid tail instance (kernel theorem)"
  IO.println "rigid record data inference tour passed"
