import Yulang.GeneralDeclarativeWitnessMixedReleaseMeaning356
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRecursiveMixed356
open GeneralDeclarativeWitnessMixedScope356 (Scope Ordinary)
open GeneralDeclarativeWitnessPayloadRoute356 (Route)
open GeneralDeclarativeWitnessMixedTyped356 (At atChild)
open GeneralDeclarativeWitnessSpineNode355 (Node Author Send)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWitnessTree349 (Report)

inductive Plan where
  | typed (author : Author) (children : List Plan)
  | ordinaryPayload (clause binder : Nat)

mutual
inductive Code where
  | typed (at_ : Send) (children : Codes)
  | payload (path : List Nat) (old : GeneralDeclarativeWitnessMixedForest352.Code) (report : Report)
inductive Codes where
  | nil
  | cons (first : Code) (rest : Codes)
end

mutual
inductive Tree {s : State} (e : Scope) : Node s → Type where
  | typed {p : Node s} (role : p.input.demand.role ∈ e.typedRoles) :
      Branches e p 0 p.proof.compiled.children → Tree e p
inductive Branches {s : State} (e : Scope) : (p : Node s) → Nat → List Demand → Type where
  | nil {p : Node s} : Branches e p i []
  | typed {p : Node s} {a w} (picked : At p e i d a w) :
      Tree e picked.node → Branches e p (i+1) ds → Branches e p i (d::ds)
  | payload {p : Node s} {r} (where_ : Route p i d)
    (observed : Ordinary e p.input.metadata.sourceInput s (p.origin.path ++ [i]) d r) :
      Branches e p (i+1) ds → Branches e p i (d::ds)
end

def decodeBranches {s : State} (e : Scope) (p : Node s) (i : Nat)
    (ds : List Demand) (author : List Plan) (wires : Codes) : Option (Branches e p i ds) :=
  match wires,ds,author with
  | .nil,[],[] => some .nil
  | .cons (.typed here underneath) rest,d::ds,.typed found childPlans::more => do
    let located ← atChild p e i d found here
    let below ← decodeBranches e located.node 0 located.node.proof.compiled.children childPlans underneath
    let next ← decodeBranches e p (i+1) ds more rest
    pure (.typed located (.typed located.permitted below) next)
  | .cons (.payload path w answer) rest,d::ds,.ordinaryPayload clause binder::more =>
    if path = p.origin.path ++ [i] then do
      let picked ← GeneralDeclarativeWitnessPayloadRoute356.read p i d clause binder
      let branch ← GeneralDeclarativeWitnessMixedScope356.ordinary e p.input.metadata.sourceInput s (p.origin.path ++ [i]) d w answer
      let next ← decodeBranches e p (i+1) ds more rest
      pure (.payload picked branch next)
    else none
  | _,_,_ => none
termination_by sizeOf wires

def decodeTree {s : State} (e : Scope) (p : Node s) (author : List Plan) (wire : Codes) :
    Option (Tree e p) := do
  if inScope : p.input.demand.role ∈ e.typedRoles then
    let children ← decodeBranches e p 0 p.proof.compiled.children author wire
    pure (.typed inScope children)
  else none

end Yulang.GeneralDeclarativeWitnessRecursiveMixed356
