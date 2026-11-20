import Yulang.GeneralDepthTwoMachine300

open Yulang
open GeneralDepthTwoMachine300 (Phase raw next remaining)
open GeneralGeneratedNestedSource299 (root)
open GeneralGeneratedNestedPredictions299 (middle terminal)

def owners (p : Phase) : List (Nat × Nat) :=
  (raw p).core.erased.current.edges.map (fun (a,b) => (a.identity,b.identity))

def main : IO Unit := do
  unless owners .source == [] &&
      owners .middle == [(root.identity,middle.identity)] &&
      owners .done == [(root.identity,middle.identity),(middle.identity,terminal.identity)] do
    throw (IO.userError "unexpected recorded raw edges")
  IO.println "PASS actual raw edge data grows [] → [outer→inner] → [outer→inner, inner→leaf]"
  unless next .source == some .middle && next .middle == some .done && (next .done).isNone do
    throw (IO.userError "incorrect phase machine")
  unless [remaining .source,remaining .middle,remaining .done] == [2,1,0] do
    throw (IO.userError "incorrect local raw rank")
  IO.println "PASS the exact fixed-source phase machine uses two installs and remaining rank [2,1,0]"
  IO.println "The separate Lean theorem covers every kernel successor of this fixed initial state."
