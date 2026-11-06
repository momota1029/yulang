import Yulang.RigidRecordCheckerExamples

/-!
Run the exact ground reference checker and the separate rigid-demand entry:

    lake env lean --trust=0 --run RunRigidRecordCheck.lean

Opaque-target negatives below document a boundary of the specified relation;
they are not rejection expectations for source-language record expressions.
-/

open Yulang RigidRecordCheckerExamples

def main : IO Unit := do
  for (name, source, target, expected) in cases do
    let result := RigidRecordChecker.check pureRows source target
    if result != expected then
      throw (IO.userError (name ++ ": unexpected reference subtype result"))
    IO.println (name ++ " => " ++ toString result)
  for (name, result, expected) in demandCases do
    if result != expected then
      throw (IO.userError (name ++ ": unexpected rigid-demand result"))
    IO.println (name ++ " => " ++ toString result)
  let before : StructuralBase.Ty Bool := .arrow (.base .int) true (.base .int) false
  let after : StructuralBase.Ty Bool := .arrow (.base .int) false (.base .int) false
  if !RigidRecordChecker.check boolRows before after || RigidRecordChecker.check boolRows after before then
    throw (IO.userError "contravariant input row comparison changed")
  IO.println "contravariant input rows => forward accepted, reverse rejected"
  IO.println "rigid record checker tour passed"
