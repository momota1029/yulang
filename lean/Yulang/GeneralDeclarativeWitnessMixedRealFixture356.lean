import Yulang.GeneralDeclarativeWitnessMixedReal356
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 55000
set_option maxHeartbeats 68000000
namespace Yulang.GeneralDeclarativeWitnessMixedRealFixture356
open GeneralDeclarativeWitnessMixedReal356 (Before assemble problem entry location typedPlan scopeAt origins
  simpleBounds sourceReads dataInput)
open GeneralDeclarativeWitnessMixedSiblings356 (Plan BranchWire decode)
open GeneralDeclarativeWitnessMixedScope356 (Scope)
open GeneralDeclarativeWitnessSpineNode355 (Node)
open GeneralDeclarativeWitnessTypedForestFixture354 (head)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeWitnessAllocation350 (names)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeHead320 (State Equation)

def highNames : List Nat := [6,10,32,33,34,35,60,61,62,63,64]
def rank : List Nat := (List.range 100).map (fun n => if n ∈ highNames then 2 else 0)

def author : List Plan := [.typed ⟨typedPlan,[]⟩,.payload 81 32]
def report : Report :=
  ⟨.selected 92 [.selected 93 [],.selected 94 []],
    .selected (.node 92 [.node 93 [],.node 94 []]),problem.demand.outputs⟩

structure Data where
  current : State
  env : Scope
  root : GeneralDeclarativeWitnessTypedPacket354.Report
  children : List BranchWire

def data : Option Data := do
  let b ← assemble
  let current := b.final.state
  let parent ← literalPlan b.top.state current
  let child ← literalPlan b.route.state current
  let ordinary ← literalPlan b.final.state current
  let r : GeneralDeclarativeWitnessTypedPacket354.Report :=
    ⟨92,b.top.children.map printDemand,b.top.output.trace,parent⟩
  let l : GeneralDeclarativeWitnessTypedPacket354.Report :=
    ⟨93,b.route.children.map printDemand,b.route.output.trace,child⟩
  let ordinaryWire : GeneralDeclarativeWitnessTagBranch352.Wire :=
    ⟨simpleBounds,sourceReads,simpleBounds,sourceReads,rank,names b.cfg.spans,
      ⟨b.final.kids.map printDemand,b.final.fixed,ordinary⟩⟩
  let report : Report := ⟨.selected 94 [],.selected (.node 94 []),b.ordinary.outputs⟩
  pure ⟨current,scopeAt b.route.state,r,
    [.typed ⟨⟨[4,0],head false,l⟩,.leaf⟩,.payload [4,1] (.node (.tagged ordinaryWire) .nil) report]⟩

def readRoot (a : Data) : Option (Node a.current) := do
  let k ← GeneralDeclarativeWitnessTypedRangeWriter354.decode problem entry a.current a.root
  pure ⟨problem,location,entry,a.root,k⟩

def test (ps : List Plan := author) (edit : List BranchWire → List BranchWire := id)
    (tables : Scope → Scope := id) (returning : Report := report) : Bool :=
  (data.map (fun tuple =>
    ((readRoot tuple).map (fun root =>
      (decode root (tables tuple.env) ps (edit tuple.children) returning).isSome)).getD false)).getD false

theorem actual_mixed_branches : test = true := by decide +kernel

theorem actual_compiler_outputs :
    (assemble.map (fun a => decide (a.top.children.map printDemand =
      ([(3,[(32,10,33)],[]),(4,[(34,10,35)],[(0,60)])] : List GeneralDeclarativeWitnessCompiler350.DemandCode) ∧
      a.top.whereRows = [⟨60,.variable 10⟩] ∧
      a.final.fixed = [⟨60,.variant 7 (.variable 86)⟩]))).getD false = true := by decide +kernel

theorem wrong_ordinary_clausal_binder :
    test [.typed ⟨typedPlan,[]⟩,.payload 81 31] = false := by decide +kernel

theorem declared_projection_not_an_ordinal_guess :
    test [.typed ⟨typedPlan,[]⟩,.payload 80 32] = false := by decide +kernel

theorem numeric_identity_cannot_promote_ordinary :
    test author id (fun e => {e with origins := {origins with authored := []}}) = false := by decide +kernel

theorem whole_registry_is_not_ordinary :
    test author id (fun e => {e with typedRoles := [1]}) = false := by decide +kernel

theorem wrong_physical_branch_order :
    test author List.reverse = false := by decide +kernel

theorem wrong_returned_dictionary_order :
    test author id id {report with result := .selected (.node 92 [.node 94 [],.node 93 []])} =
      false := by decide +kernel

theorem missing_nominal_release :
    test [.typed ⟨{typedPlan with authority := {typedPlan.authority with released := []}},[]⟩,.payload 81 32] =
      false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessMixedRealFixture356
