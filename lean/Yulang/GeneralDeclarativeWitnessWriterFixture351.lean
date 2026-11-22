import Yulang.GeneralDeclarativeWitnessAuthWhole351
import Yulang.GeneralDeclarativeWitnessOrderedModel350

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeWitnessWriterFixture351
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open GeneralSourceMetadataRows291 (Source)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeWitnessForest350 (ProblemTree Layout Code anchor)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessManifest349 (Manifest attach)
open GeneralDeclarativeWitnessRecordHeader350 (replay)
open GeneralDeclarativeWitnessRecordReplay350 (Wire)
open GeneralDeclarativeWitnessOneRecord350 (compilerCtx)
open GeneralDeclarativeWitnessCompiler350 (Finished execute)
open GeneralDeclarativeWitnessIdentity351 (Stamp Key)
open GeneralDeclarativeWitnessOrderedFixture350 (eqCode mkProjection literalPlan nested intCode leafRows)
open GeneralDeclarativeEndpointCase336 (endCode)
open GeneralDeclarativeEndpointMixedTail336 (width)

def ctorTable : Source :=
  ⟨.absent,[⟨71,some ⟨[],71⟩,.primitive (.scalar .int)⟩,
    ⟨72,some ⟨[],72⟩,.primitive .exactEmpty⟩,⟨73,some ⟨[],73⟩,.primitive .emptyRecord⟩]⟩

def printed : Pattern := .record 7 (.record 9 (.app 71 []) (.app 72 [])) (.app 73 [])
def out : Equation := ⟨2,.record 7 nested width⟩

def pattern : Pattern := .record 8 (.var 0) (.var 1)
def rule : Declaration := ⟨190,19,[pattern],[],[⟨195,0,printed⟩],[]⟩
def input : InputBundle :=
  ⟨ctorTable,ctorTable,⟨0,[⟨19,1,[(0,none)]⟩]⟩,[rule]⟩

def cap : Capture := ⟨10,10,10⟩
def demand : Demand := ⟨19,[cap],[⟨0,2⟩]⟩
def sourceEq : Equation := ⟨10,.record 8 intCode endCode⟩
def before : State := ⟨⟨[],[]⟩,[sourceEq]⟩
def manifest : Manifest := ⟨[sourceEq]⟩
def layout : Layout := ⟨before,[99],fun _ => cap,fun _ _ => 0⟩

def tree (current : State) : ProblemTree := ⟨input,current,manifest,fun _ _ => layout⟩
def answer : Report := ⟨.selected 190 [],.selected (.node 190 []),demand.outputs⟩

def readCode : GeneralDeclarativeWitnessRecord349.Wire :=
  ⟨⟨.refl 10,.refl 10⟩,.inline 0 .same,.inline 0 .same⟩

def compilerRun : Option Finished := do
  let base := anchor (tree before) [] demand
  let words ← replay base.problem ⟨answer.outputs⟩
  let attached ← attach before manifest
  let seen ← GeneralDeclarativeWitnessProjection349.decode attached cap pattern readCode
  execute (compilerCtx (p := base) seen words rule)

def code (current : State) (ran : Finished) (levels : List Nat) : Option Code := do
  let shape ← eqCode current 10 sourceEq.right
  let field ← mkProjection current [(8,intCode)] shape 100 intCode intCode intCode
  let rest ← mkProjection current [(8,intCode)] shape 103 endCode endCode endCode
  let proof ← literalPlan ran.state current
  pure (.node ⟨readCode,readCode,[(0,100,101,102),(1,103,104,105)],[field,rest],0,.same,levels,
    ⟨[],[out],proof⟩⟩ .nil)

def stamp : Stamp := ⟨[],19,7⟩
def key : Key := ⟨[],19,7,0,2⟩

theorem actual_compiler_row :
    (compilerRun.map (fun ran => (decide (ran.fixed = [out]) && ran.kids.isEmpty))).getD false = true := by
  decide +kernel

end Yulang.GeneralDeclarativeWitnessWriterFixture351
