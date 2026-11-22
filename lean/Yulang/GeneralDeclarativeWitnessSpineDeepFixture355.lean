import Yulang.GeneralDeclarativeWitnessSpineDeepSeed355
import Yulang.GeneralDeclarativeWitnessRetainedCut355
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65000
set_option maxHeartbeats 75000000
namespace Yulang.GeneralDeclarativeWitnessSpineDeepFixture355
open GeneralDeclarativeWitnessSpineDeepSeed355 (root input second third fourth full forLayer)
open GeneralDeclarativeWitnessCovariantFixture353 (wire)
open GeneralDeclarativeWitnessTypedForestFixture354 (head)
open GeneralDeclarativeWitnessNominalSpine355 (Code)
open GeneralDeclarativeWitnessNominalSpineWhole355 (Seed run)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeHead320 (State)

def receipt : Report :=
  ⟨.selected 92 [.selected 93 [.selected 94 [.selected 95 [.selected 96 []]]]],
    .selected (.node 92 [.node 93 [.node 94 [.node 95 [.node 96 []]]]]),
    input.demand.outputs⟩

def plan : Seed := ⟨8,[second.source,third.source,fourth.source]⟩

def data : Option (State × GeneralDeclarativeWitnessTypedReemit354.Wire × Code) := do
  let (p,b,c,d,e) ← full
  let s := e.done.state
  let keep ← literalPlan p.state s
  let rb ← forLayer b s
  let rc ← forLayer c s
  let rd ← forLayer d s
  let re ← forLayer e s
  let first : GeneralDeclarativeWitnessTypedReemit354.Wire := {
    writerHead := wire
    writer := ⟨p.source.decl.id,p.children.map printDemand,p.writes.trace,keep⟩
    receiverHead := head false
    receiver := rb }
  pure (s,first,.send ⟨second.path,second.head,rc⟩
    (.send ⟨third.path,third.head,rd⟩ (.send ⟨fourth.path,fourth.head,re⟩ .leaf)))

def test (se : Seed := plan) (out : Report := receipt) (edit : Code → Code := id) : Bool :=
  (data.map (fun (s,w,c) =>
    ((GeneralDeclarativeWitnessTypedReemit354.decode root s w).map (fun a =>
      (run a se (edit c) out).isSome)).getD false)).getD false

theorem actual_five_nodes : test = true := by decide +kernel

theorem truncated_spine_not_a_leaf :
    test {plan with authors := plan.authors.take 1} receipt
      (fun c => match c with | .send x _ => .send x .leaf | _ => c) = false := by decide +kernel

theorem stale_middle_incarnation :
    test {plan with authors := [{second.source with nextVersion := 8},third.source,fourth.source]} = false := by
  decide +kernel

theorem old_publisher_cannot_replace_later_authority :
    test {plan with authors := [second.source,{third.source with authority := second.source.authority},fourth.source]} =
      false := by decide +kernel

theorem next_path_is_proven_not_printed :
    test plan receipt (fun c => match c with | .send h t => .send {h with path := [4,0]} t | _ => c) = false :=
  by decide +kernel

theorem internal_choice_cannot_disappear :
    test plan {receipt with result := .selected (.node 92 [.node 93 [.node 94 [.node 96 []]]])} = false :=
  by decide +kernel

end Yulang.GeneralDeclarativeWitnessSpineDeepFixture355
