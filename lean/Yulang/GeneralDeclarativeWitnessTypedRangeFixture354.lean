import Yulang.GeneralDeclarativeWitnessTypedRangeWriter354
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 38000
set_option maxHeartbeats 32000000
namespace Yulang.GeneralDeclarativeWitnessTypedRangeFixture354
open GeneralDeclarativeWitnessTypedForestFixture354 (problem sourceRows head)
open GeneralDeclarativeWitnessCovariantFixture353 (wire)
open GeneralDeclarativeWitnessTypedOutput354 (Write)
open GeneralDeclarativeWitnessTypedPacket354 (typedAt Report)
open GeneralDeclarativeWitnessTypedChild354 (downstream)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem)
open GeneralDeclarativeWitnessTypedRangeWriter354 (run decode)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarations (Clause Declaration)
open GeneralSourceState (Output)

def req : Clause := ⟨80,3,[.var 31],[⟨82,4,.var 31⟩]⟩
def rootDecl : Declaration := {GeneralDeclarativeWitnessTypedForestFixture354.decl with requirements := [req]}
def childDecl : Declaration :=
  {GeneralDeclarativeWitnessTypedFixture354.receiver with associated := [⟨100,4,.variant 13 (.app 0 [.var 32])⟩]}
def producer : Problem :=
  let old := problem.producer
  let original := old.metadata.sourceInput
  let new := { original with
    declarations := [rootDecl,childDecl]
    roles := ⟨0,[⟨1,1,[(0,none),(1,none),(2,none)]⟩,⟨3,1,[(4,none)]⟩]⟩ }
  {old with metadata := {old.metadata with sourceInput := new}, targets := fun _ _ => 10}

def emitted : Option (State × Problem × Report × Report) := do
  let parent ← GeneralDeclarativeWitnessTypedPacket354.run producer wire
  let child ← parent.children[0]?
  let typed ← typedAt parent.writes 1
  let i := {problem.atChild (GeneralDeclarativeWitnessTypedForestFixture354.plan false) 0 with producer := producer}
  let actual := downstream i parent.state child typed.1.typed.row
  let r ← run actual (head false)
  let before ← literalPlan parent.state r.state
  let self ← literalPlan r.state r.state
  pure (r.state,actual,⟨92,parent.children.map printDemand,parent.writes.trace,before⟩,
    ⟨93,r.children.map printDemand,r.output.trace,self⟩)

def positive : Bool :=
  (emitted.map (fun (s,actual,_,r) => (decode actual (head false) s r).isSome)).getD false

theorem true_nonpoint_child_reemits : positive = true := by decide +kernel

theorem no_child_output_invention :
    (emitted.map (fun (_,p,parent,r) =>
      decide (printDemand p.demand = (3,[(32,9,33)],[(4,10)]) ∧
        parent.kids = [(3,[(32,9,33)],[(4,10)])] ∧
        r.trace = [.typed ⟨10,13,0,9⟩]))).getD false = true := by decide +kernel

end Yulang.GeneralDeclarativeWitnessTypedRangeFixture354
