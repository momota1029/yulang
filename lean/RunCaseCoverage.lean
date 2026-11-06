import Yulang.CaseCoverageExamples

open Yulang Yulang.CaseValues Yulang.CasePatterns Yulang.CaseCoverage
open Yulang.CaseCoverageExamples

private def require (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"{name}: unexpected result")

private def eventLabel : CaseEvaluation.Event (CaseDataTerms.Expr Empty) → String
  | .source _ => "source"
  | .scrutinee => "scrutinee"
  | .arm index => s!"arm:{index}"
  | .guard index => s!"guard:{index}"
  | .body index => s!"body:{index}"

def main : IO Unit := do
  require "boolean partition" (check Examples.noDefaults Examples.booleanArms (.base .bool))
  require "guard excluded" (!check (F := Empty) Examples.noDefaults [⟨.wildcard, true⟩] (.base .bool))
  require "tuple product" (check Examples.noDefaults Examples.tupleArms (.pair (.base .bool) (.base .unit)))
  require "list nil/cons" (check Examples.noDefaults Examples.listArms (.list (.base .int)))
  IO.println "coverage: boolean, tuple product, list nil/cons; guarded wildcard contributes nothing"

  require "missing tag" (!checkVariants (F := Empty) Examples.noDefaults [⟨.variant 0 .wildcard, false⟩] twoTags)
  let merged := Variants.Merged.normalize Domain.union [(0, .base .int), (0, .base .str)]
  require "whole merged payload" (checkVariants (F := Empty) Examples.noDefaults [⟨.variant 0 .wildcard, false⟩] merged)
  require "partial merged payload" (!checkVariants (F := Empty) Examples.noDefaults [⟨.variant 0 (.literal (.int 0)), false⟩] merged)
  IO.println "variants: missing tag rejected by fragment check; whole merged payload accepted; partial payload retained"

  let ordered := CaseDataProgram.eval floatCheck [] booleanProgram
  require "written arm and guard order" (decide (ordered.trace.map eventLabel =
    ["scrutinee", "source", "arm:0", "guard:0", "source", "arm:1", "arm:2", "body:2", "source"]))
  match ordered.result with
  | .ok (some (.literal (.int 3))) => pure ()
  | _ => throw (IO.userError "ordered boolean case: wrong value")
  IO.println "case: false guard skips its body; later arms run in written order and select 3"

  let present := CasePatterns.run floatCheck (CaseDataTerms.defaultEval []) defaultPattern
    (.record [(0, .literal (.int 9))])
  require "present default visit" present.trace.isEmpty
  match present.result with
  | .ok (some [(1, .literal (.int 9))]) => pure ()
  | _ => throw (IO.userError "present default: wrong bindings")
  let absent := CasePatterns.run floatCheck (CaseDataTerms.defaultEval []) defaultPattern (.record [])
  require "absent default visit" (decide (absent.trace.map eventLabel = ["source"]))
  match absent.result with
  | .ok (some [(1, .literal (.int 41))]) => pure ()
  | _ => throw (IO.userError "absent default: wrong bindings")
  match (CaseDataProgram.eval floatCheck [] defaultProgram).result with
  | .ok (some (.literal (.int 41))) => pure ()
  | _ => throw (IO.userError "typed default program: wrong value")
  IO.println "pattern defaults: present field has no fallback visit; absent field evaluates fallback and binds 41"

  require "known interval completeness boundary" (!check Examples.noDefaults integerSplit (.base .int))
  IO.println "known limit: integer ..0 | 1.. is proved exhaustive but not yet recognized by this checker"
  match (CaseDataProgram.eval floatCheck [] enumProgram).result with
  | .ok (some (.literal (.int 77))) => pure ()
  | _ => throw (IO.userError "typed two-constructor enum program: wrong payload")
  IO.println "nominal enum: full two-constructor input typed; selected constructor preserves payload 77"
  IO.println "case coverage and concrete evaluation tour passed"
