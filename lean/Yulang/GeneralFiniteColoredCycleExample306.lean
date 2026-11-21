import Yulang.GeneralFiniteColoredQuotient306

namespace Yulang.GeneralFiniteColoredCycleExample306
open GeneralFiniteColoredQuotient306 (fastQuotient)
open GeneralFiniteColoredRounds306 (Closed)

inductive Vertex
  | start
  | twin
  | quiet
  | done
  deriving DecidableEq, Repr

def nodes : List Vertex := [.start,.twin,.quiet,.done]

def edges : Vertex → List Vertex
  | .start => [.start,.done]
  | .twin => [.twin,.done]
  | .quiet => [.quiet]
  | .done => []

theorem closed : Closed edges nodes := by
  intro s _ t h
  cases s <;> cases t <;> revert h <;> decide

def plain := fastQuotient edges (fun _ => ()) nodes

theorem cyclic_regression :
    plain.representatives = [.twin,.quiet,.done] ∧
    plain.project .start = some .twin ∧ plain.project .quiet = some .quiet ∧
    plain.edges .twin = [.twin,.done] ∧ plain.edges .quiet = [.quiet] ∧ plain.edges .done = [] := by
  decide +kernel

def colored := fastQuotient edges (fun v => decide (v = Vertex.start)) nodes

theorem color_distinguishes :
    colored.representatives = [.start,.twin,.quiet,.done] ∧
    colored.project .start = some .start ∧ colored.project .twin = some .twin := by
  decide +kernel

end Yulang.GeneralFiniteColoredCycleExample306
