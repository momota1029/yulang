import Yulang.ErrorEffectExamples
import Yulang.JunctionEffectExamples

open Yulang SignatureRequests

private def returned? (action : Tree n signature Value) : Option Value :=
  match action with
  | .pure value => some value
  | .request _ _ _ => none

private def sameResult [DecidableEq Error] [DecidableEq Value] :
    Option (Except Error Value) → Option (Except Error Value) → Bool
  | some (.ok left), some (.ok right) => decide (left = right)
  | some (.error left), some (.error right) => decide (left = right)
  | none, none => true
  | _, _ => false

private def check (label : String) (accepted : Bool) : IO Unit := do
  if accepted then IO.println s!"pass: {label}"
  else throw (IO.userError s!"failed: {label}")

def main : IO Unit := do
  check "wrap normal result"
    (sameResult (returned? (ErrorEffects.wrap ErrorEffectExamples.pathCases
      (.pure 7 : Tree 1 ErrorEffectExamples.signature Nat))) (some (.ok 7)))
  check "wrap directly declared path source"
    (sameResult (returned? (ErrorEffects.wrap ErrorEffectExamples.inclusiveCases
      (ErrorEffects.raise (n := 1) (Value := Nat) ErrorEffectExamples.pathEncoding
        (.missing "sample")))) (some (.error (.path (.missing "sample")))))
  check "wrap second directly declared source"
    (sameResult (returned? (ErrorEffects.wrap ErrorEffectExamples.inclusiveCases
      (ErrorEffects.raise (n := 1) (Value := Nat) ErrorEffectExamples.parseEncoding 9)))
        (some (.error (.parse 9))))
  check "up rethrows to the target error"
    (sameResult (returned? (ErrorEffects.wrap ErrorEffectExamples.appCases
      (ErrorEffects.up ErrorEffectExamples.pathCases ErrorEffectExamples.appEncoding
        ErrorEffectExamples.AppError.path
        (ErrorEffects.raise (n := 1) (Value := Nat) ErrorEffectExamples.pathEncoding
          (.denied "sample"))))) (some (.error (.path (.denied "sample")))))
  check "all [1,2,3] < any [2,3,4]"
    (returned? (JunctionEffects.run JunctionEffectExamples.external JunctionEffectExamples.comparison) ==
      some true)
  check "or stops after successful true branch"
    (JunctionEffectExamples.observe
      (JunctionEffects.run JunctionEffectExamples.external JunctionEffectExamples.disjoinStops) ==
        (["true branch"], some true))
  check "or tries true then false using the same resumption"
    (JunctionEffectExamples.observe
      (JunctionEffects.run JunctionEffectExamples.external JunctionEffectExamples.disjoinUsesBoth) ==
        (["true branch", "false branch"], some true))
  check "and stops after failed true branch"
    (JunctionEffectExamples.observe
      (JunctionEffects.run JunctionEffectExamples.external JunctionEffectExamples.conjoinStops) ==
        (["true branch"], some false))
  check "ret aborts remaining computation"
    (JunctionEffectExamples.observe
      (JunctionEffects.run JunctionEffectExamples.external JunctionEffectExamples.earlyFinish) ==
        ([], some false))
  check "protected junction remains unresolved"
    (JunctionEffectExamples.observe
      (JunctionEffects.run JunctionEffectExamples.external JunctionEffectExamples.protectedChoice) ==
        ([], none))
