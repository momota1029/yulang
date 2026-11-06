import Yulang.SourceInferenceExamples
import Yulang.JointConstraintInferenceExamples

/-!
An executable tour beginning at the original closed `Inference.Expr`.

    lake env lean --trust=0 --run RunSourceInference.lean

Every case runs the actual generator, clause compiler, type/row solver, and
scheme construction. The small finite observations in `canonicalInstance`
exercise scheme instantiation; the all-depth, all-instance results are the
independent theorems in `SourcePrincipalInference` and `SourceInferenceExamples`.
No parsed surface syntax or display normalization is claimed here.
-/

open Yulang Inference

private abbrev rows := RowFlowSchemes.Examples.boolAlgebra
private def rowCheck (left right : Bool) : Bool := !left || right

private def runSource (name : String) (expression : Expr)
    (expected : SourcePrincipalInference.Status) : IO SourcePrincipalInference.Result := do
  let result := SourcePrincipalInference.infer expression
  if result.status != expected then
    throw (IO.userError (name ++ ": expected " ++ reprStr expected ++ ", got " ++ reprStr result.status))
  match result with
  | .unsupported => IO.println (name ++ " => unsupported; not a type error")
  | .rejected => IO.println (name ++ " => rejected; no original typing")
  | .inferred alternatives =>
      let obligations := alternatives.foldl (fun total item => total + item.scheme.cache.length) 0
      IO.println (name ++ " => inferred; " ++ toString alternatives.length ++
        " alternative(s), " ++ toString obligations ++ " saturated type obligations")
  (← IO.getStdout).flush
  return result

private def canonicalInstance (name : String) (result : SourcePrincipalInference.Result)
    (parameterType : RegularInferenceModel.Ty Bool) (expected : StructuralBase.Ty Bool) : IO Unit := do
  let .inferred alternatives := result | throw (IO.userError (name ++ ": no scheme to instantiate"))
  let mut found := false
  for alternative in alternatives do
    -- Search only a small concrete parameter family for this execution check.
    -- Universal exactness does not depend on this finite search.
    for valueIndex in List.finRange alternative.scheme.size do
      for rowIndex in List.finRange alternative.slots do
        let parameter := fun index => if index == valueIndex then parameterType else .bottom
        let rowParameter := fun index => index == rowIndex
        let value := alternative.scheme.values rows rowParameter parameter alternative.output
        let observed := value.eval (RegularValueTypes.observe (RegularInferenceModel.graph Bool) 3)
        if StructuralDecisions.check rowCheck observed expected &&
            StructuralDecisions.check rowCheck expected observed then
          found := true
  if !found then throw (IO.userError (name ++ ": canonical parameter instance was not constructed"))
  IO.println (name ++ " => free parameters construct the expected value/row correlation")
  (← IO.getStdout).flush

def main : IO Unit := do
  let identity := SourceInferenceExamples.identity
  let _ ← runSource "integer literal" (.lit .int) .inferred
  let identityResult ← runSource "identity lambda" identity .inferred
  canonicalInstance "identity at int with a live input/output row" identityResult (.base .int)
    (.arrow (.base .int) true (.base .int) true)
  let constantResult ← runSource "constant integer lambda" SourceInferenceExamples.constantInt .inferred
  canonicalInstance "constant at any with a live input row" constantResult .top
    (.arrow .top true (.base .int) false)
  let _ ← runSource "self application lambda" (.lam (.app (.var 0) (.var 0))) .inferred
  let _ ← runSource "identity applied to integer" (.app identity (.lit .int)) .inferred
  let usesIdentity : Expr :=
    .branch (.app (.var 0) (.lit .bool)) (.app (.var 0) (.lit .int)) (.lit .int)
  let polymorphic ← runSource "value-let used at bool and int" (.letE identity usesIdentity) .inferred
  match polymorphic with
  | .inferred alternatives =>
      if alternatives.length != 1 then
        throw (IO.userError "value-let should retain the polymorphic alternative and reject the inconsistent monomorphic one")
  | _ => throw (IO.userError "value-let unexpectedly has no inferred alternative")
  let _ ← runSource "same uses through a monomorphic lambda argument"
    (.app (.lam usesIdentity) identity) .rejected
  let _ ← runSource "pair projection" (.fst (.pair (.lit .int) (.lit .str))) .inferred
  let _ ← runSource "variant with a function payload" (.variant 7 identity) .inferred
  let _ ← runSource "missing field" (.field 0 .emptyRecord) .rejected
  let _ ← runSource "non-Boolean condition" (.branch (.lit .int) (.lit .int) (.lit .str)) .rejected
  let _ ← runSource "unbound variable" (.var 0) .rejected
  let _ ← runSource "record construction boundary" (.record 0 (.lit .int) .emptyRecord) .unsupported
  IO.println "source inference tour passed"
