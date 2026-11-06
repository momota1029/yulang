import Yulang.RegularSchemeInference
import Yulang.RegularValueCoalescingExamples
import Yulang.TypeSimplificationExamples

/-!
Executable tour of principal regular inference and parameter simplification.

    lake env lean --trust=0 --run RunRegularInference.lean

The finite observations below check ordinary execution of constructed graphs.
The theorems in `RegularValueCoalescing` prove the model property at *all*
depths; these observations are not a depth-bounded replacement for that proof.
The input examples are nested constraint graphs, not parsed source strings.
-/

open Yulang
open NestedValueSolverExamples

private def runGraph (name : String) (graph : NestedValueSolver.Graph n Unit)
    (constraints : List (NestedValueSolver.Edge n)) (output : Fin n)
    (expectedSuccess : Bool) : IO Unit := do
  match RegularSchemeInference.infer pureRowCheck graph constraints output with
  | none =>
      if expectedSuccess then throw (IO.userError (name ++ ": inference unexpectedly failed"))
      IO.println (name ++ " => no regular model")
  | some scheme =>
      if !expectedSuccess then throw (IO.userError (name ++ ": inconsistent graph accepted"))
      let parameters : RegularValueTypes.Graph Unit Unit := fun _ => .arrow () () () ()
      let parameter : Fin n → RegularValueTypes.Layer Unit Unit :=
        fun index => if index.val % 2 == 0 then .top else .arrow () () () ()
      let instanceGraph := scheme.instantiate parameters parameter
      for depth in [1, 2, 4] do
        for edge in constraints do
          let source := RegularValueTypes.observe instanceGraph depth (.inl edge.1)
          let target := RegularValueTypes.observe instanceGraph depth (.inl edge.2)
          if !StructuralDecisions.check pureRowCheck source target then
            throw (IO.userError (name ++ ": constructed instance violates an original constraint"))
      IO.println (name ++ " => principal regular scheme; " ++ toString scheme.cache.length ++
        " saturated obligations; recursive parameter instance checked")

def main : IO Unit := do
  runGraph "identity application" identityApplication [(3, 4)] 1 true
  runGraph "self application with a cycle" selfApplication selfApplicationConstraints 3 true
  runGraph "contravariant input conflict" contravariantConflict contravariantConstraints 1 false
  runGraph "pair conflict inside an arrow" nestedPairConflict [(5, 6)] 0 false
  if TypeSimplification.simplifyAll TypeSimplificationExamples.identity !=
      TypeSimplificationExamples.identity then
    throw (IO.userError "identity lost its shared value parameter")
  IO.println "identity simplification => same parameter in input and output"
  if !(TypeSimplification.mergeCheck true 0 1 TypeSimplificationExamples.positiveCooccurrence) then
    throw (IO.userError "positive co-occurrence merge was not recognized")
  IO.println "co-occurrence => two jointly produced parameters can be shared"
  if !(TypeSimplification.sandwichCheck 0 (.base .int) TypeSimplificationExamples.primitiveSandwich) then
    throw (IO.userError "integer sandwich was not recognized")
  IO.println "sandwich => the parameter between integer bounds can be eliminated"
  if TypeSimplification.mergeCheck true 0 1 TypeSimplificationExamples.independentArrow ||
      TypeSimplification.mergeCheck false 0 1 TypeSimplificationExamples.independentArrow then
    throw (IO.userError "independent input/output parameters were incorrectly merged")
  IO.println "independent input/output parameters => unsafe merge rejected"
