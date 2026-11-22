import Yulang.GeneralDeclarativeWitnessTypedForest354
import Yulang.GeneralDeclarativeWitnessTypedFixture354
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 38000
set_option maxHeartbeats 32000000
namespace Yulang.GeneralDeclarativeWitnessTypedForestFixture354
open GeneralDeclarativeWitnessTypedFixture354 (receiver active loc)
open GeneralDeclarativeWitnessCovariantFixture353 (input parent clause0 clause1 source wire)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row)
open GeneralDeclarativeWitnessTypedOutput354 (Write)
open GeneralDeclarativeWitnessTypedPacket354 (Run run typedAt)
open GeneralDeclarativeWitnessTypedForest354 (Input Plan ChildWire WriterWire Wire decode)
open GeneralDeclarativeWitnessTypedRelease354 (Key Authority)
open GeneralDeclarativeWitnessTypedChild354 (downstream)
open GeneralDeclarativeWitnessCovariantInterval353 (read)
open GeneralDeclarativeWitnessCovariantHead352 (rawPattern)
open GeneralDeclarativeWitnessCompiler350 (execute printDemand Finished)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessTree349 (Report)

def last : Declaration := ⟨94,4,[rawPattern],[],[],[]⟩
def decl : Declaration :=
  {parent with associated := [⟨91,0,.variant 13 (.app 0 [.var 31])⟩,
    ⟨95,1,.variant 13 (.app 0 [.var 32])⟩,⟨96,2,.var 31⟩]}
def root : Demand := ⟨1,[⟨20,20,20⟩],[⟨0,5⟩,⟨1,9⟩,⟨2,6⟩]⟩
def producer : Problem :=
  let old := GeneralDeclarativeWitnessCovariantFixture353.problem
  let sourceInput : GeneralSourceMetadataBareBundle291.InputBundle := ⟨source,source,⟨0,[⟨1,1,[(0,none),(1,none),(2,none)]⟩,⟨3,1,[]⟩,⟨4,1,[]⟩]⟩,
    [decl,receiver,last]⟩
  {old with metadata := {old.metadata with sourceInput := sourceInput}, demand := root}

def leftKey : Key := ⟨active,0,0,5⟩
def rightKey : Key := ⟨active,1,1,9⟩
def auth : Authority := ⟨[active],[leftKey,rightKey]⟩
def sourceRows (second : Bool) : List Row :=
  let l := if second then 34 else 32
  [⟨30,13,0,7⟩,⟨31,13,0,8⟩,⟨l,13,0,l⟩,⟨l+1,13,0,l+1⟩]
def plan (second : Bool) : Plan :=
  ⟨1,sourceRows second,[if second then 69 else 49],fun _ => ⟨9,9,9⟩⟩
def problem : Input := ⟨producer,loc,auth,[plan false,plan true]⟩

def head (second : Bool) : GeneralDeclarativeWitnessCovariantInterval353.Wire :=
  let offset := if second then 10 else 2
  ⟨⟨0,rawPattern,0,1,4⟩,2,3,.constraint offset,.constraint (offset+3)⟩

def childRun (r : Run producer wire) (idx : Nat) (second : Bool) : Option Finished := do
  let d ← r.children[idx]?
  let typedOut ← typedAt r.writes 1
  let p := downstream (problem.atChild (plan second) idx) r.state d typedOut.1.typed.row
  let checked ← read p (head second)
  execute checked.ctx

def combined (l r : Finished) : State :=
  ⟨⟨l.state.normal.ordinary ++ r.state.normal.ordinary,[]⟩,
    l.state.equations ++ r.state.equations⟩

def report : Report := ⟨.selected 92 [.selected 93 [],.selected 94 []],
  .selected (.node 92 [.node 93 [],.node 94 []]),root.outputs⟩

def data : Option (State × Wire) := do
  let r ← run producer wire
  let l ← childRun r 0 false
  let h ← childRun r 1 true
  let current := combined l h
  let p ← literalPlan r.state current
  let left ← literalPlan l.state current
  let right ← literalPlan h.state current
  pure (current,⟨⟨wire,⟨r.source.decl.id,r.children.map printDemand,r.writes.trace,p⟩⟩,
    [⟨[4,0],head false,⟨l.kids.map printDemand,l.fixed,left⟩⟩,
     ⟨[4,1],head true,⟨h.kids.map printDemand,h.fixed,right⟩⟩],report⟩)

def test (p : Input := problem) (edit : Wire → Wire := id) : Bool :=
  (data.map (fun (s,w) => (decode p s (edit w)).isSome)).getD false

theorem actual_siblings : test = true := by decide +kernel

theorem both_typed_writes_emitted :
    (data.map (fun (_,w) => decide (w.writer.out.trace =
      [.typed ⟨5,13,0,9⟩,.typed ⟨9,13,0,9⟩,.ordinary ⟨6,.variable 9⟩]))).getD false = true := by
  decide +kernel

theorem correctly_released_equal_payload_elsewhere_is_wrong :
    test {problem with kids := [{plan false with writtenOrdinal := 0},plan true]} = false := by decide +kernel

theorem reverse_child_paths :
    test problem (fun w => {w with children := w.children.reverse}) = false := by decide +kernel

theorem missing_actual_child :
    test problem (fun w => {w with children := w.children.take 1}) = false := by decide +kernel

theorem wrong_report_order :
    test problem (fun w => {w with report := {report with result := .selected (.node 92 [.node 94 [],.node 93 []])}}) =
      false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessTypedForestFixture354
