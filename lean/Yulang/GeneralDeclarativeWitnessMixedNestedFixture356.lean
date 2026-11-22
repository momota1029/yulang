import Yulang.GeneralDeclarativeWitnessMixedNestedSeed356
import Yulang.GeneralDeclarativeWitnessRecursiveTree356
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65000
set_option maxHeartbeats 75000000
namespace Yulang.GeneralDeclarativeWitnessMixedNestedFixture356
open GeneralDeclarativeWitnessRecursiveMixed356 (Plan Codes Code Tree decodeTree)
open GeneralDeclarativeWitnessRecursiveTree356 (view dictionary)
open GeneralDeclarativeWitnessMixedNestedSeed356 (Runs OrdinaryRun root assemble scope combined bounds readsFrom)
open GeneralDeclarativeWitnessMixedReal356 (entry location typedPlan origins)
open GeneralDeclarativeWitnessMixedScope356 (Scope)
open GeneralDeclarativeWitnessTypedForestFixture354 (head)
open GeneralDeclarativeWitnessSpineNode355 (Node)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeWitnessAllocation350 (names)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan)
open GeneralDeclarativeWitnessTree349 (Report agrees)
open GeneralDeclarativeWitnessTypedJoint354 (compatible)
open GeneralDeclarativeHead320 (State)

def high : List Nat := [6,10,32,33,34,35,60,61,62,63,64,70]
def ranks : List Nat := (List.range 160).map (fun n => if n ∈ high then 2 else 0)

def authors : List Plan := [.typed typedPlan [.ordinaryPayload 82 31],.ordinaryPayload 81 32]
def report : Report :=
  ⟨.selected 92 [.selected 93 [.selected 95 []],.selected 94 []],
    .selected (.node 92 [.node 93 [.node 95 []],.node 94 []]),root.demand.outputs⟩

def ordinaryCode (x : OrdinaryRun) (path : List Nat) (id offset : Nat) (s : State) : Option Code := do
  let snapshot ← literalPlan x.result.state s
  let wire : GeneralDeclarativeWitnessTagBranch352.Wire :=
    ⟨bounds offset,readsFrom offset,bounds offset,readsFrom offset,ranks,names x.old.spans,
      ⟨x.result.kids.map printDemand,x.result.fixed,snapshot⟩⟩
  pure (.payload path (.node (.tagged wire) .nil) ⟨.selected id [],.selected (.node id []),x.argument.outputs⟩)

structure Data where
  state : State
  environment : Scope
  emitter : GeneralDeclarativeWitnessTypedPacket354.Report
  ordered : Codes

def data : Option Data := do
  let x ← assemble
  let s := combined x.atTop.result.state x.below.result.state
  let p ← literalPlan x.top.state s
  let m ← literalPlan x.middle.state s
  let o ← ordinaryCode x.atTop [4,1] 94 10 s
  let n ← ordinaryCode x.below [4,0,0] 95 18 s
  let w : GeneralDeclarativeWitnessTypedPacket354.Report :=
    ⟨93,x.middle.children.map printDemand,x.middle.output.trace,m⟩
  pure ⟨s,scope x.middle.state,⟨92,x.top.children.map printDemand,x.top.output.trace,p⟩,
    .cons (.typed ⟨[4,0],head false,w⟩ (.cons n .nil)) (.cons o .nil)⟩

def checkedRoot (p : Data) : Option (Node p.state) := do
  let r ← GeneralDeclarativeWitnessTypedRangeWriter354.decode root entry p.state p.emitter
  pure ⟨root,location,entry,p.emitter,r⟩

def test (plan : List Plan := authors) (send : Codes → Codes := id)
    (answer : Report := report) (sc : Scope → Scope := id) : Bool :=
  (data.map (fun p => ((checkedRoot p).map (fun r =>
    ((decodeTree (sc p.environment) r plan (send p.ordered)).map
      (fun tree => compatible (GeneralDeclarativeWitnessRecursiveTree356.rows tree) &&
        agrees ⟨r.input.metadata.sourceInput,p.state,r.input.demand⟩ (view tree) answer)).getD false)).getD false)).getD false

theorem actual_nested_ordinary_route : test = true := by decide +kernel

theorem actual_two_fixed_ordinary_sites :
    (assemble.map (fun x => decide (x.atTop.result.fixed = [⟨60,.variant 7 (.variable 86)⟩] ∧
      x.below.result.fixed = [⟨70,.variant 7 (.variable 126)⟩]))).getD false = true := by decide +kernel

theorem projected_grandchild_cannot_be_truncated :
    test [.typed typedPlan [],.ordinaryPayload 81 32]
      (fun w => match w with
        | .cons (.typed here _) rest => .cons (.typed here .nil) rest
        | other => other) = false := by decide +kernel

def wrongNestedPath : Codes → Codes
  | .cons (.typed here (.cons (.payload _ w r) more)) rest =>
    .cons (.typed here (.cons (.payload [4,1,0] w r) more)) rest
  | other => other

theorem ordinary_absolute_path_cannot_be_rebased :
    test authors wrongNestedPath = false := by decide +kernel

theorem wrong_mixed_return :
    test authors id {report with result := .selected (.node 92 [.node 93 [],.node 94 [.node 95 []]])} =
      false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessMixedNestedFixture356
