import Yulang.GeneralDeclarativeWitnessCovariantCompiler353
import Yulang.GeneralDeclarativeWitnessOrderedFixture350

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
set_option maxRecDepth 36000
namespace Yulang.GeneralDeclarativeWitnessCovariantFixture353
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Wire Row)
open GeneralDeclarativeWitnessCovariantCompiler353 (prepare check)
open GeneralDeclarativeWitnessCovariantHead352 (rawPattern)
open GeneralDeclarativeWitnessCovariant352 (covariant)
open GeneralDeclarativeWitnessCompiler350 (Finished execute printDemand)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration Clause)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Source)
open GeneralDeclarativeWitnessAllocation350 (names)

def source : Source := ⟨.absent,[⟨0,some ⟨[.type],0⟩,.unclassified⟩]⟩
def child0 : Declaration := ⟨93,3,[.var 0],[],[],[]⟩
def child1 : Declaration := ⟨94,4,[.var 0],[],[],[]⟩
def clause0 : Clause := ⟨80,3,[.var 31],[]⟩
def clause1 : Clause := ⟨81,4,[.var 32],[]⟩
def parent : Declaration :=
  ⟨92,1,[rawPattern],[clause0,clause1],[⟨91,0,.var 31⟩,⟨95,1,.var 32⟩],[]⟩
def input : InputBundle :=
  ⟨source,source,⟨0,[⟨1,1,[(0,none),(1,none)]⟩,⟨3,1,[]⟩,⟨4,1,[]⟩]⟩,[parent,child0,child1]⟩
def rows : List Row := [⟨30,13,0,7⟩,⟨31,13,0,8⟩,⟨20,13,0,9⟩]
def payload : Equation := GeneralDeclarativeWitnessCovariantOrigin353.bill 9 7 8
def eInt : GeneralNominalCenteredHeadMatExpressions.Expr := .primitive (.scalar .int) []
def eBool : GeneralNominalCenteredHeadMatExpressions.Expr := .primitive (.scalar .bool) []
def stage : State := ⟨⟨[],[]⟩,[⟨7,eInt⟩,⟨8,eBool⟩,payload]⟩
def root : Demand := ⟨1,[⟨20,20,20⟩],[⟨0,5⟩,⟨1,6⟩]⟩
def problem : Problem :=
  ⟨⟨input,[⟨0,covariant⟩]⟩,stage,rows,root,[20,30,31],fun _ => ⟨9,9,9⟩,fun _ _ => 0⟩
def wire : Wire := ⟨0,rawPattern,0,1,2⟩

def run : Option Finished := do
  let bound ← prepare problem wire
  execute bound.ctx

def out : List Equation := [⟨5,.variable 9⟩,⟨6,.variable 9⟩]
def data : Option (State × GeneralDeclarativeWitnessCompiler350.Wire) := do
  let f ← run
  let plan ← literalPlan f.state f.state
  pure (f.state,⟨f.kids.map printDemand,f.fixed,plan⟩)

def test (p : Problem := problem) (w : Wire := wire)
    (edit : GeneralDeclarativeWitnessCompiler350.Wire → GeneralDeclarativeWitnessCompiler350.Wire := id) : Bool :=
  (data.map (fun (s,r) => (check p w s (edit r)).isSome)).getD false

theorem doubled_real_slot :
    (prepare problem wire |>.map (fun p => names p.ctx.spans)) = some [(31,9,9,9),(32,9,9,9)] := by decide +kernel

theorem actual_accept : test = true := by decide +kernel

theorem checked_fixed_writes :
    (run.map (fun f => decide (f.fixed = out))).getD false = true := by decide +kernel

theorem reordered_writes :
    test problem wire (fun r => {r with outputRows := r.outputRows.reverse}) = false := by decide +kernel

theorem reordered_children :
    test problem wire (fun r => {r with children := r.children.reverse}) = false := by decide +kernel

theorem rejects_replaced_target :
    test problem wire (fun r => {r with outputRows := [⟨5,.variable 9⟩,⟨8,.variable 9⟩]}) = false := by decide +kernel

theorem rejects_split_capture :
    test problem wire (fun r => {r with outputRows := [⟨5,.variable 7⟩,⟨6,.variable 8⟩]}) = false := by decide +kernel

theorem chosen_center_cannot_be_endpoint : test problem {wire with center := 0} = false := by decide +kernel

theorem mode_cannot_be_withheld :
    test {problem with metadata := {problem.metadata with variance := []}} = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessCovariantFixture353
