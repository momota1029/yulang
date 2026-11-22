import Yulang.GeneralDeclarativeWitnessMixedRelease352
import Yulang.GeneralDeclarativeWitnessMixedControls352
import Yulang.GeneralDeclarativeWitnessWriterFixture351

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 22000000
namespace Yulang.GeneralDeclarativeWitnessMixedReleaseFixture352
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeWitnessCompiler350 (Finished execute)
open GeneralDeclarativeWitnessForest350 (ProblemTree anchor Layout Code)
open GeneralDeclarativeWitnessCatalog351 (Anchor)
open GeneralDeclarativeWitnessIdentity351 (Key Stamp)
open GeneralDeclarativeWitnessManifest349 (attach)
open GeneralDeclarativeWitnessRecordHeader350 (replay)
open GeneralDeclarativeWitnessOneRecord350 (compilerCtx)
open GeneralDeclarativeWitnessMixedFixture352 (author rootRead data levels layout)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessMixedRelease352 (Problem Wire check)
open GeneralDeclarativeWitnessOrderedFixture350 (root eqCode mkProjection literalPlan intCode)
open GeneralDeclarativeWitnessWriterFixture351 (cap pattern readCode sourceEq before manifest)
open GeneralDeclarativeEndpointCase336 (endCode)

def table := GeneralDeclarativeWitnessWriterFixture351.ctorTable
def constructors : GeneralSourceMetadataRows291.Source :=
  {table with rows := table.rows ++ [⟨74,some ⟨[],74⟩,.primitive (.scalar .bool)⟩]}
def rhs : GeneralDeclarationPatterns.Pattern := .variant 7 (.app 74 [])
def out : Equation := ⟨9,.variant 7 GeneralDeclarativeTaggedFixture340.eBool⟩
def rule : Declaration := ⟨190,19,[pattern],[],[⟨195,0,rhs⟩],[]⟩
def input : InputBundle := ⟨constructors,constructors,⟨0,[⟨19,1,[(0,none)]⟩]⟩,[rule]⟩
def producerDemand : Demand := ⟨19,[cap],[⟨0,9⟩]⟩
def stamp : Stamp := ⟨[],19,7⟩
def key : Key := ⟨[],19,7,0,9⟩
def priorAnswer : Report := ⟨.selected 190 [],.selected (.node 190 []),producerDemand.outputs⟩
def tree (current : State) : ProblemTree := ⟨input,current,manifest,fun _ _ => GeneralDeclarativeWitnessWriterFixture351.layout⟩

def compilerRun : Option Finished := do
  let base := anchor (tree before) [] producerDemand
  let words ← replay base.problem ⟨priorAnswer.outputs⟩
  let origin ← attach before manifest
  let seen ← GeneralDeclarativeWitnessProjection349.decode origin cap pattern readCode
  execute (compilerCtx (p := base) seen words rule)

def ranked : List Nat := (List.range 106).map (fun i => if i < 100 then levels[i]?.getD 0 else 0)

def producerCode (s : State) (f : Finished) : Option Code := do
  let shape ← eqCode s 10 sourceEq.right
  let first ← mkProjection s [(8,intCode)] shape 100 intCode intCode intCode
  let rest ← mkProjection s [(8,intCode)] shape 103 endCode endCode endCode
  pure (.node ⟨readCode,readCode,[(0,100,101,102),(1,103,104,105)],[first,rest],0,.same,ranked,
    ⟨[],[out],← literalPlan f.state s⟩⟩ .nil)

def projectionRows : List Equation :=
  [⟨100,intCode⟩,⟨101,intCode⟩,⟨102,intCode⟩,⟨103,endCode⟩,⟨104,endCode⟩,⟨105,endCode⟩]

def together (s : State) (f : Finished) : State :=
  ⟨⟨s.normal.ordinary ++ f.state.normal.ordinary,s.normal.intervals⟩,
    s.equations ++ f.state.equations ++ projectionRows⟩

def solution : Option (State × Wire) := do
  let (state,consumer) ← data
  let f ← compilerRun
  let current := together state f
  let producer ← producerCode current f
  pure (current,⟨producer,priorAnswer,consumer⟩)

def independentOrigin : List Equation := author.take 5

def problem (s : State) (releases : List Key) : Problem :=
  ⟨⟨tree s,producerDemand,[⟨stamp,0⟩],independentOrigin,releases⟩,
    GeneralDeclarativeWitnessMixedFixture352.input,root,layout⟩

def test (releases : List Key) (active : List Stamp := [stamp]) (tweak : Problem → Problem := id) : Bool :=
  (solution.map (fun (s,w) => check (tweak (problem s releases)) active w GeneralDeclarativeWitnessMixedFixture352.answer)).getD false

theorem real_writer_row : (compilerRun.map (fun f => decide (f.fixed = [out]))).getD false = true := by
  decide +kernel

theorem released_named_arm : test [key] = true := by decide +kernel

theorem no_authored_promotion : out ∉ independentOrigin := by decide +kernel

theorem cannot_omit_release : test [] = false := by decide +kernel

theorem version_matters : test [{key with version := 6}] = false := by decide +kernel

theorem requires_exact_write :
    test [key] [stamp] (fun p => {p with publisher := {p.publisher with required := [⟨stamp,1⟩]}}) = false := by
  decide +kernel

theorem no_competing_versions : test [key] [stamp,{stamp with version := 6}] = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessMixedReleaseFixture352
