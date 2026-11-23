import Yulang.GeneralDeclarativeWitnessPayloadRoute356
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMixedTyped356
open GeneralDeclarativeWitnessSpineNode355 (Node Author Send Permit release redirected)
open GeneralDeclarativeWitnessCovariantOrigin353 (Row)
open GeneralDeclarativeWitnessMixedScope356 (Scope)
open GeneralDeclarativeWitnessNominalSpine355 (Code Checked read)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWitnessTypedRelease354 (Key)
open GeneralDeclarativeWitnessTypedOutput354 (Write)

structure Plan where
  first : Author
  rest : List Author

structure Wire where
  here : Send
  continuation : Code

structure At {s : State} (p : Node s) (e : Scope) (idx : Nat) (d : Demand) (a : Author) (w : Send) where
  issued : Permit p a.authority a.write
  actual : p.proof.compiled.children[idx]? = some d
  permitted : d.role ∈ e.typedRoles
  path : w.path = p.origin.path ++ [idx]
  apart : issued.item.typed.row.root ∉ a.rows.map Row.root
  ordinal : w.head.center.center = a.rows.length
  readback : GeneralDeclarativeWitnessTypedRangeWriter354.Accepted
    (redirected p a d issued.item.typed.row) w.head s w.output

def At.node {s : State} {p : Node s} {e idx d a w} (b : At p e idx d a w) : Node s :=
  ⟨_,⟨w.path,a.nextVersion⟩,w.head,w.output,b.readback⟩

def atChild {s : State} (p : Node s) (e : Scope) (idx : Nat) (d : Demand)
    (a : Author) (w : Send) : Option (At p e idx d a w) := do
  let out ← release p a.authority a.write
  if actualCode : (p.proof.compiled.children[idx]?).map GeneralDeclarativeWitnessCompiler350.printDemand =
      some (GeneralDeclarativeWitnessCompiler350.printDemand d) then
    if allowed : d.role ∈ e.typedRoles then
      if path : w.path = p.origin.path ++ [idx] then
        if apart : out.item.typed.row.root ∉ a.rows.map Row.root then
          if index : w.head.center.center = a.rows.length then do
            let read ← GeneralDeclarativeWitnessTypedRangeWriter354.decode
              (redirected p a d out.item.typed.row) w.head s w.output
            have actual : p.proof.compiled.children[idx]? = some d := by
              cases noted : p.proof.compiled.children[idx]? with
              | none => simp [noted] at actualCode
              | some compiled =>
                have same := GeneralDeclarativeWitnessCompiler350.print_injective
                  (Option.some.inj (show some (GeneralDeclarativeWitnessCompiler350.printDemand compiled) =
                    some (GeneralDeclarativeWitnessCompiler350.printDemand d) from by simpa [noted] using actualCode))
                exact congrArg some same
            pure ⟨out,actual,allowed,path,apart,index,read⟩
          else none
        else none
      else none
    else none
  else none

theorem consumed_row {s : State} {p : Node s} {e idx d a w} (x : At p e idx d a w) :
    x.node.proof.compiled.readFrom.center.anchor.current = x.issued.item.typed.row := by
  have at_ := x.readback.compiled.readFrom.center.anchor.currentAt
  change (a.rows ++ [x.issued.item.typed.row])[w.head.center.center]? =
    some x.node.proof.compiled.readFrom.center.anchor.current at at_
  rw [x.ordinal,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at at_
  exact (Option.some.inj at_).symm

theorem exact_actual_center {s : State} {p : Node s} {e idx d a w} (x : At p e idx d a w) :
    x.node.proof.compiled.readFrom.arg.center = x.issued.item.demand.target := by
  have at_ := x.node.proof.compiled.readFrom.center.anchor.actualCenter
  rw [consumed_row x,GeneralDeclarativeWitnessCovariantInterval353.actual_index] at at_
  exact at_.symm

structure Typed {s : State} (p : Node s) (e : Scope) (idx : Nat) (d : Demand) (a : Plan) (w : Wire) where
  first : At p e idx d a.first w.here
  subtree : Checked first.node
  remainsTyped : ∀ n ∈ subtree.nodes, n.input.demand.role ∈ e.typedRoles

def subtree {s : State} (p : Node s) (e : Scope) (idx : Nat) (d : Demand) (a : Plan) (w : Wire) :
    Option (Typed p e idx d a w) := do
  let first ← atChild p e idx d a.first w.here
  let checked ← read first.node a.rest w.continuation
  if stays : checked.nodes.all (fun n => e.typedRoles.contains n.input.demand.role) = true then
    some ⟨first,checked,fun n h => by simpa using List.all_eq_true.mp stays n h⟩
  else none

end Yulang.GeneralDeclarativeWitnessMixedTyped356
