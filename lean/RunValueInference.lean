import Yulang.ValueInference
import Yulang.ValueBoundExamples
import Yulang.ValueBoundEliminationExamples

/-!
A small executable tour of the proved inference entry points.

Run from `lean/` with:

    lake env lean --trust=0 --run RunValueInference.lean

The compact output below only suppresses bottom in unions for readability.
It is not the complete display canonicalizer required by spec 7.4b.
-/

open Yulang

private def typeText : StructuralBase.Ty Row → String
  | .base .int => "int"
  | .base .str => "str"
  | .base .bool => "bool"
  | .base .unit => "()"
  | .bottom => "never"
  | .top => "any"
  | .union .bottom right => typeText right
  | .union left .bottom => typeText left
  | .union left right => "(" ++ typeText left ++ " | " ++ typeText right ++ ")"
  | .inter left right => "(" ++ typeText left ++ " & " ++ typeText right ++ ")"
  | .pair left right => "(" ++ typeText left ++ ", " ++ typeText right ++ ")"
  | .emptyRecord => "{}"
  | .record label value rest => "{" ++ toString label ++ ": " ++ typeText value ++
      ", .." ++ typeText rest ++ "}"
  | .variant label value => ":tag" ++ toString label ++ " " ++ typeText value
  | .arrow input _ output _ => "(" ++ typeText input ++ " -> " ++ typeText output ++ ")"

private def resultText : ValueInference.Result 1 Nat → String
  | .unsupported => "unsupported"
  | .unsat => "no type"
  | .solved type => typeText type

private def runExample (name : String) (expression : Inference.Expr) (expected : String) : IO Unit := do
  let actual := resultText (ValueInference.solve ([] : List (ValueInference.ValueType 1 Nat)) expression)
  if actual != expected then
    throw (IO.userError (name ++ ": expected " ++ expected ++ ", got " ++ actual))
  IO.println (name ++ " => " ++ actual)

def main : IO Unit := do
  runExample "integer literal" (.lit .int) "int"
  runExample "if bool then int else str" (.branch (.lit .bool) (.lit .int) (.lit .str)) "(int | str)"
  runExample "let x = (if bool then int else str); (x, int)"
    (.letE (.branch (.lit .bool) (.lit .int) (.lit .str)) (.pair (.var 0) (.lit .int)))
    "((int | str), int)"
  runExample "tag carrying a pair" (.variant 7 (.pair (.lit .int) (.lit .str))) ":tag7 (int, str)"
  runExample "if int then int else str" (.branch (.lit .int) (.lit .int) (.lit .str)) "no type"
  runExample "unbound variable" (.var 0) "no type"
  runExample "lambda in the ValueInference entry" (.lam (.var 0)) "unsupported"
  let cycle := ValueBoundSolvers.Examples.cycle
  match ValueBoundSolvers.solveSigned cycle with
  | none => throw (IO.userError "cyclic bounds unexpectedly failed")
  | some value => IO.println ("cyclic unknown bounds, exit => " ++ typeText (value 2))
  if (ValueBoundSolvers.solveSigned ValueBoundSolvers.Examples.debtBounds).isSome then
    throw (IO.userError "negative latent effect was erased")
  IO.println "negative latent effect against an empty upper row => no assignment"
  if !(ValueBoundSolvers.solveSemilinear ValueBoundSolvers.Examples.infiniteBounds).isSome then
    throw (IO.userError "infinite latent-row bounds unexpectedly failed")
  IO.println "unknown function type with an infinite latent row => solved"
  let identityExpected : StructuralBase.Ty ValueBoundSolvers.Examples.Row :=
    .arrow (.base .str) ValueBoundSolvers.Examples.debt (.base .str) ValueBoundSolvers.Examples.debt
  match ValueBoundEliminationExamples.inferIdentity StructuralDecisions.checkSigned
      (.base .str) ValueBoundSolvers.Examples.debt with
  | none => throw (IO.userError "identity instance unexpectedly failed")
  | some type =>
      if !StructuralDecisions.equivalentSigned type identityExpected then
        throw (IO.userError "identity lost its argument/result type or row correlation")
      IO.println "identity instance at str with a negative-effect row => same str and same row returned"
