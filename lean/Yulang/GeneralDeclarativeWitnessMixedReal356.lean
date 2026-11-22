import Yulang.GeneralDeclarativeWitnessMixedSiblings356
import Yulang.GeneralDeclarativeWitnessCovariantFixture353
import Yulang.GeneralDeclarativeWitnessTypedForestFixture354
import Yulang.GeneralDeclarativeWitnessTagCoreFixture352
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 55000
set_option maxHeartbeats 55000000
namespace Yulang.GeneralDeclarativeWitnessMixedReal356
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row bill)
open GeneralDeclarativeWitnessCovariantHead352 (rawPattern)
open GeneralDeclarativeWitnessCovariantFixture353 (wire eInt eBool clause0 clause1)
open GeneralDeclarativeWitnessTypedForestFixture354 (leftKey plan head)
open GeneralDeclarativeWitnessSpineNode355 (Node Author redirected)
open GeneralDeclarativeWitnessTypedPacket354 (typedAt Report)
open GeneralDeclarativeWitnessTypedOutput354 (Write)
open GeneralDeclarativeWitnessTypedRangeWriter354 (Run run)
open GeneralDeclarativeWitnessMixedSiblings356 (Plan BranchWire)
open GeneralDeclarativeWitnessMixedScope356 (Scope filtered)
open GeneralDeclarativeWitnessCompiler350 (Finished execute printDemand)
open GeneralDeclarativeWitnessTagSources351 (Script)
open GeneralDeclarativeWitnessTagElection352 (Ends reads)
open GeneralDeclarativeWitnessTagLocal351 (parse context)
open GeneralDeclarativeWitnessTagBranch352 (Wire)
open GeneralDeclarativeWitnessBound349 (Range)
open GeneralDeclarativeWitnessAllocation350 (names)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan)
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open GeneralDeclarativeWitnessForest350 (Layout)
open GeneralSourceMetadataBareBundle291 (InputBundle compile)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarations (Declaration Clause)

def typedDecl : Declaration := GeneralDeclarativeWitnessTypedFixture354.receiver
def ordinaryPattern : GeneralDeclarationPatterns.Pattern := .variant 7 (.var 40)
def ordinaryDecl : Declaration := ⟨94,4,[ordinaryPattern],[],[⟨99,0,ordinaryPattern⟩],[]⟩
def delayedOrdinary : Clause := {clause1 with outputs := [⟨82,0,.var 32⟩]}
def rootDecl : Declaration :=
  {GeneralDeclarativeWitnessTypedForestFixture354.decl with requirements := [clause0,delayedOrdinary]}

def source : GeneralSourceMetadataRows291.Source :=
  let p := GeneralDeclarativeWitnessCovariantFixture353.source
  {p with rows := p.rows ++ [⟨1,some ⟨[],1⟩,.primitive (.scalar .int)⟩,
    ⟨2,some ⟨[],2⟩,.primitive (.scalar .bool)⟩]}

def dataInput : InputBundle :=
  ⟨source,source,⟨0,[⟨1,1,[(0,none),(1,none),(2,none)]⟩,⟨3,1,[]⟩,⟨4,1,[(0,none)]⟩]⟩,
    [rootDecl,typedDecl,ordinaryDecl]⟩

def sourceEquations : List Equation := [⟨7,.variant 7 eInt⟩,⟨8,.variant 7 eBool⟩,bill 10 7 8]
def base : State := ⟨⟨[],[]⟩,sourceEquations⟩

def problem : Problem :=
  let old := GeneralDeclarativeWitnessCovariantFixture353.problem
  { old with
    metadata := {old.metadata with sourceInput := dataInput}
    stage := base
    rows := [⟨30,13,0,7⟩,⟨31,13,0,8⟩,⟨20,13,0,10⟩]
    demand := {old.demand with outputs := [⟨0,5⟩,⟨1,10⟩,⟨2,6⟩]}
    targets := fun _ _ => 60 }

def location : GeneralDeclarativeWitnessTypedRelease354.Location := ⟨[4],7⟩
def entry : GeneralDeclarativeWitnessCovariantInterval353.Wire := ⟨wire,2,2,.refl 10,.refl 10⟩
def written := GeneralDeclarativeWitnessTypedFixture354.active
def auth : GeneralDeclarativeWitnessTypedRelease354.Authority := ⟨[written],[leftKey,⟨written,1,1,10⟩]⟩
def typedPlan : Author := ⟨auth,1,8,(plan false).authored,[49],fun _ => ⟨10,10,10⟩⟩

def origins : Table := ⟨sourceEquations,[],[]⟩
def keepOrdinary : List Nat := [79]
def fallbackOrdinary : Nat → GeneralDeclarativeWhere319.Capture := fun _ => ⟨10,10,10⟩

def scopeAt (before : State) : Scope :=
  ⟨[1,3],origins,fun _ _ => ⟨before,keepOrdinary,fallbackOrdinary,fun _ _ => 0⟩⟩

def simpleBounds : Range := ⟨.constraint 10,.constraint 13⟩
def tagArms : Script := .join (.named ⟨0,.same⟩ .tagged) (.named ⟨1,.same⟩ .tagged)
def sourceReads : Ends := .recursive
  (.named ⟨2,.order ⟨.constraint 10,.constraint 11⟩⟩ tagArms)
  (.named ⟨2,.order ⟨.constraint 12,.constraint 13⟩⟩ tagArms)

structure Before where
  top : Run problem entry
  typed : Problem
  route : Run typed (head false)
  ordinary : Demand
  cfg : GeneralDeclarativeWitnessCompiler350.Context
  final : Finished

def assemble : Option Before := do
  let top ← run problem entry
  let fixed ← typedAt top.output 1
  let d0 ← top.children[0]?
  let d1 ← top.children[1]?
  let typed : Problem := { problem with
    rows := typedPlan.rows ++ [fixed.1.typed.row]
    stage := top.state
    demand := d0
    keep := typedPlan.keep
    fallback := typedPlan.fallback }
  let child ← run typed (head false)
  let t ← compile (filtered dataInput [1,3])
  let live ← attach child.state origins
  let arg ← d1.arguments[0]?
  let route ← reads live arg 7 simpleBounds sourceReads
  let ready ← parse (registry t).constructors (interpretation t.snapshot) ordinaryPattern 7
  let ctx := context (r := registry t) d1 ordinaryDecl route ready keepOrdinary fallbackOrdinary (fun _ _ => 0)
  let leaf ← execute ctx
  pure ⟨top,typed,child,d1,ctx,leaf⟩

end Yulang.GeneralDeclarativeWitnessMixedReal356
