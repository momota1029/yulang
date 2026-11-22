import Yulang.GeneralDeclarativeWitnessGrandchild355
import Yulang.GeneralDeclarativeWitnessRangeReleaseFixture355
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 40000
set_option maxHeartbeats 36000000
namespace Yulang.GeneralDeclarativeWitnessGrandchildSeed355
open GeneralDeclarativeWitnessTypedRangeFixture354 (req rootDecl childDecl)
open GeneralDeclarativeWitnessTypedForestFixture354 (problem head)
open GeneralDeclarativeWitnessCovariantFixture353 (wire stage)
open GeneralDeclarativeWitnessCovariantHead352 (rawPattern)
open GeneralDeclarativeWitnessTypedPacket354 (Report Run typedAt)
open GeneralDeclarativeWitnessTypedChild354 (Input downstream)
open GeneralDeclarativeWitnessTypedRelease354 (Authority)
open GeneralDeclarativeWitnessTypedReemit354 (Wire)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row bill)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarations (Clause Declaration)

def desc : Clause := ⟨83,4,[.var 31],[]⟩
def middle : Declaration := {childDecl with requirements := [desc]}
def leaf : Declaration := ⟨94,4,[rawPattern],[],[],[]⟩

def producer (k : Nat) : Problem :=
  let old := GeneralDeclarativeWitnessTypedRangeFixture354.producer
  let original := old.metadata.sourceInput
  let new := { original with
    declarations := [rootDecl,middle,leaf]
    roles := ⟨0,[⟨1,1,[(0,none),(1,none),(2,none)]⟩,⟨3,1,[(4,none)]⟩,⟨4,1,[]⟩]⟩ }
  { old with
    metadata := {old.metadata with sourceInput := new}
    stage := {stage with equations := stage.equations.take 2 ++ [bill k 7 8]}
    rows := [⟨30,13,0,7⟩,⟨31,13,0,8⟩,⟨20,13,0,k⟩]
    demand := {old.demand with outputs := [⟨0,5⟩,⟨1,k⟩,⟨2,6⟩]} }

def authority (k : Nat) : Authority := ⟨problem.authority.active,
  [⟨GeneralDeclarativeWitnessTypedFixture354.active,0,0,5⟩,
   ⟨GeneralDeclarativeWitnessTypedFixture354.active,1,1,k⟩]⟩

def seed (k : Nat) : Input :=
  { problem.atChild (GeneralDeclarativeWitnessTypedForestFixture354.plan false) 0 with
    producer := producer k
    auth := authority k }

structure Emitted (k : Nat) where
  parent : Run (producer k) wire
  demand : GeneralDeclarativeDemand320.Demand
  row : Row
  context : Problem
  receiver : GeneralDeclarativeWitnessTypedRangeWriter354.Run context (head false)

def compilePair (k : Nat) : Option (Emitted k) := do
  let parent ← GeneralDeclarativeWitnessTypedPacket354.run (producer k) wire
  let child ← parent.children[0]?
  let row ← typedAt parent.writes 1
  let ctx := downstream (seed k) parent.state child row.1.typed.row
  let receiver ← GeneralDeclarativeWitnessTypedRangeWriter354.run ctx (head false)
  pure ⟨parent,child,row.1.typed.row,ctx,receiver⟩

def partialWire {k : Nat} (out : Emitted k) (current : State) : Option Wire := do
  let top ← literalPlan out.parent.state current
  let after ← literalPlan out.receiver.state current
  pure ⟨wire,⟨out.parent.source.decl.id,out.parent.children.map printDemand,out.parent.writes.trace,top⟩,head false,
    ⟨out.receiver.readFrom.center.decl.id,out.receiver.children.map printDemand,out.receiver.output.trace,after⟩⟩

def summarize (k : Nat) :=
  (compilePair k).map (fun result => (result.receiver.children.map printDemand,
    result.receiver.state.normal.ordinary.length,
    result.receiver.state.equations.map GeneralDeclarativeHead320.Equation.left))

end Yulang.GeneralDeclarativeWitnessGrandchildSeed355
