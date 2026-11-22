import Yulang.GeneralDeclarativeWitnessRecursiveMixed356
import Yulang.GeneralDeclarativeWitnessMixedRealFixture356
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65000
set_option maxHeartbeats 72000000
namespace Yulang.GeneralDeclarativeWitnessMixedNestedSeed356
open GeneralDeclarativeWitnessMixedReal356 (problem dataInput rootDecl typedDecl ordinaryDecl ordinaryPattern entry
  location typedPlan origins tagArms fallbackOrdinary)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem)
open GeneralDeclarativeWitnessTypedRangeWriter354 (Run run)
open GeneralDeclarativeWitnessTypedPacket354 (typedAt Report)
open GeneralDeclarativeWitnessSpineNode355 (Node redirected)
open GeneralDeclarativeWitnessMixedScope356 (Scope filtered)
open GeneralDeclarativeWitnessTypedForestFixture354 (head)
open GeneralDeclarativeWitnessCompiler350 (Context Finished execute printDemand)
open GeneralDeclarativeWitnessTagElection352 (Ends reads)
open GeneralDeclarativeWitnessTagLocal351 (parse context)
open GeneralDeclarativeWitnessBound349 (Range)
open GeneralDeclarativeWitnessForest350 (Layout)
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open GeneralSourceMetadataBareBundle291 (InputBundle compile)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Clause Declaration)

def nestedReq : Clause := ⟨82,5,[.var 31],[⟨83,0,.var 31⟩]⟩
def innerTyped : Declaration := {typedDecl with requirements := [nestedReq]}
def other : Declaration := {ordinaryDecl with id := 95, role := 5}

def inputs : InputBundle := {dataInput with
  declarations := [rootDecl,innerTyped,ordinaryDecl,other]
  roles := ⟨0,[⟨1,1,[(0,none),(1,none),(2,none)]⟩,⟨3,1,[]⟩,⟨4,1,[(0,none)]⟩,⟨5,1,[(0,none)]⟩]⟩ }

def root : Problem :=
  { problem with
    metadata := {problem.metadata with sourceInput := inputs}
    targets := fun clause _ => if clause.role = 5 then 70 else 60 }

def layout (before : State) (path : List Nat) (_d : Demand) : Layout :=
  ⟨before,if path = [4,1] then [79] else [119],fallbackOrdinary,fun _ _ => 0⟩

def scope (before : State) : Scope :=
  ⟨[1,3],origins,layout before⟩

def bounds (offset : Nat) : Range := ⟨.constraint offset,.constraint (offset+3)⟩
def readsFrom (offset : Nat) : Ends := .recursive
  (.named ⟨2,.order ⟨.constraint offset,.constraint (offset+1)⟩⟩ tagArms)
  (.named ⟨2,.order ⟨.constraint (offset+2),.constraint (offset+3)⟩⟩ tagArms)

structure OrdinaryRun where
  argument : Demand
  old : Context
  result : Finished

def ordinaryRun (before : State) (path : List Nat) (decl : Declaration) (d : Demand)
    (offset : Nat) : Option OrdinaryRun := do
  let catalogue ← compile (filtered inputs [1,3])
  let live ← attach before origins
  let argument ← d.arguments[0]?
  let facts ← reads live argument 7 (bounds offset) (readsFrom offset)
  let shape ← parse (registry catalogue).constructors (interpretation catalogue.snapshot) ordinaryPattern 7
  let e := layout before path d
  let ctx := context (r := registry catalogue) d decl facts shape e.keep e.fallback e.targets
  let out ← execute ctx
  pure ⟨d,ctx,out⟩

structure Runs where
  top : Run root entry
  typed : Problem
  middle : Run typed (head false)
  atTop : OrdinaryRun
  below : OrdinaryRun

def assemble : Option Runs := do
  let top ← run root entry
  let issued ← typedAt top.output 1
  let td ← top.children[0]?
  let od ← top.children[1]?
  let typed : Problem := { root with
    rows := typedPlan.rows ++ [issued.1.typed.row]
    stage := top.state
    demand := td
    keep := typedPlan.keep
    fallback := typedPlan.fallback }
  let middle ← run typed (head false)
  let next ← middle.children[0]?
  let topBranch ← ordinaryRun middle.state [4,1] ordinaryDecl od 10
  let inner ← ordinaryRun middle.state [4,0,0] other next 18
  pure ⟨top,typed,middle,topBranch,inner⟩

def combined (l r : State) : State :=
  ⟨⟨l.normal.ordinary ++ r.normal.ordinary,l.normal.intervals ++ r.normal.intervals⟩,l.equations ++ r.equations⟩

end Yulang.GeneralDeclarativeWitnessMixedNestedSeed356
