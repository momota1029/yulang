import Yulang.GeneralDeclarativeWitnessWriterFixture351

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralDeclarativeWitnessAuthFixture351
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessIdentity351 (Key)
open GeneralDeclarativeWitnessCatalog351 (WriteAnchor)
open GeneralDeclarativeWitnessAuthForest351 (Problem localProblem)
open GeneralDeclarativeWitnessAuthNode351 (compilerCtx)
open GeneralDeclarativeWitnessAuthWhole351 (Wire check)
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open GeneralDeclarativeWitnessForest350 (Layout Code Codes)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessRecordHeader350 (replay)
open GeneralDeclarativeWitnessCompiler350 (Finished execute printDemand)
open GeneralDeclarativeWitnessReleased350 (project)
open GeneralDeclarativeWitnessWriterFixture351 (out key stamp sourceEq)
open GeneralDeclarativeWitnessOrderedFixture350 (leafRows)
open GeneralDeclarativeWitnessOrderedFixture350
  (parent kid0 kid1 root q0 q1 prior treeProblem childArg nested intCode manifest literalPlan
   ranks eqCode mkProjection rootOutput center)
open GeneralDeclarativeEndpointCase336 (endCode)
open GeneralDeclarativeEndpointMixedTail336 (width)
open GeneralDeclarativeWitnessCutDecl334 (arg pat)

def swapUpper (s : State) : State :=
  {s with equations := s.equations.map (fun e => if e.left = 2 then out else e)}

def originRows : List Equation := manifest.sourceRows.filter (fun e => decide (e.left ≠ 2))
def places (path : List Nat) (d : Demand) : Layout :=
  let L := (treeProblem prior).layout path d
  {L with before := swapUpper L.before}

def state (producer : Finished) : State :=
  let s := swapUpper GeneralDeclarativeWitnessOrderedModel350.fixedState
  ⟨⟨s.normal.ordinary ++ producer.state.normal.ordinary,s.normal.intervals⟩,
    s.equations ++ [sourceEq] ++ leafRows 100⟩

def expected : Table := ⟨originRows,[(out,0)],[0]⟩

def problem (s : State) (released : List Key) : Problem :=
  ⟨⟨GeneralDeclarativeWitnessWriterFixture351.tree s,GeneralDeclarativeWitnessWriterFixture351.demand,
       [⟨stamp,0⟩],originRows,released⟩,
    GeneralDeclarativeWitnessOrderedFixture350.input,root,places⟩

def rootRead : GeneralDeclarativeWitnessRecord349.Wire :=
  ⟨⟨.interval 0,.interval 1⟩,.inline 0 .same,.inline 3 .same⟩
def childRead : GeneralDeclarativeWitnessRecord349.Wire :=
  ⟨⟨.constraint 0,.constraint 1⟩,
    .inline 1 (.order ⟨.constraint 2,.constraint 3⟩),
    .inline 2 (.order ⟨.constraint 4,.constraint 5⟩)⟩
def childPattern : GeneralDeclarationPatterns.Pattern := .record 9 (.var 0) (.var 1)

def expectedRun (p : Problem) (path : List Nat) (d : Demand)
    (decl : Declaration) (arg : GeneralDeclarativeWhere319.Capture)
    (pat : GeneralDeclarationPatterns.Pattern) (wire : GeneralDeclarativeWitnessRecord349.Wire) : Option Finished := do
  let base := localProblem p expected path d
  let tab ← replay base.problem ⟨d.outputs⟩
  let a ← attach base.before expected
  let seen ← project a arg pat wire
  execute (compilerCtx (p := base) seen tab decl)

def parentCode (s : State) (f : Finished) : Option GeneralDeclarativeWitnessRecordReplay350.Wire := do
  let shape ← eqCode s 1 center.right
  let l ← eqCode s 20 (.variable 3)
  let m ← eqCode s 21 (.variable 4)
  let upper ← eqCode s 22 (.variable 4)
  let unfoldNested ← eqCode s 4 nested
  let first : GeneralDeclarativeWitnessExactRest349.Wire :=
    ⟨[(7,.variable 4)],endCode,shape,l,m,.compose upper unfoldNested⟩
  let rest ← mkProjection s [(7,.variable 4)] shape 23 endCode endCode width
  pure ⟨rootRead,rootRead,[(0,20,21,22),(1,23,24,25)],[first,rest],0,.same,ranks,
    ⟨[printDemand q0,printDemand q1],[rootOutput],← literalPlan f.state s⟩⟩

def childCode (s : State) (f : Finished) (base : Nat) : Option GeneralDeclarativeWitnessRecordReplay350.Wire := do
  let l ← eqCode s 21 (.variable 4)
  let m ← eqCode s 4 nested
  let shape : GeneralDeclarativeWitnessEquation349.Code := .compose l m
  let field ← mkProjection s [(9,intCode)] shape base intCode intCode intCode
  let rest ← mkProjection s [(9,intCode)] shape (base+3) endCode endCode endCode
  pure ⟨childRead,childRead,[(0,base,base+1,base+2),(1,base+3,base+4,base+5)],[field,rest],
    1,.order ⟨.constraint 2,.constraint 3⟩,ranks,⟨[],[],← literalPlan f.state s⟩⟩

def setup : Option (Finished × Wire) := do
  let producer ← GeneralDeclarativeWitnessWriterFixture351.compilerRun
  let s := state producer
  let p := problem s [key]
  let producerCode ← GeneralDeclarativeWitnessWriterFixture351.code s producer ranks
  let parent ← expectedRun p [] root parent arg pat rootRead
  let left ← expectedRun p [0] q0 kid0 childArg childPattern childRead
  let right ← expectedRun p [1] q1 kid1 childArg childPattern childRead
  let outer ← parentCode s parent
  let l ← childCode s left 50
  let r ← childCode s right 80
  pure (producer,⟨producerCode,GeneralDeclarativeWitnessWriterFixture351.answer,
    .node outer (.cons (.node l .nil) (.cons (.node r .nil) .nil))⟩)

def answer := GeneralDeclarativeWitnessOrderedFixture350.answer

def test (keys : List Key) (tweak : Problem → Problem := id) (update : Wire → Wire := id) : Bool :=
  (setup.map (fun (f,w) => check (tweak (problem (state f) keys)) (update w) answer)).getD false

theorem accepted : test [key] = true := by decide +kernel

theorem wrong_version : test [{key with version := 6}] = false := by decide +kernel

theorem wrong_occurrence : test [{key with path := [0]}] = false := by decide +kernel

theorem wrong_target : test [{key with target := 3}] = false := by decide +kernel

theorem missing_release : test [] = false := by decide +kernel

theorem wrong_compiler_write :
    test [key] (fun p => {p with writer := {p.writer with required := [⟨stamp,1⟩]}}) = false := by
  decide +kernel

theorem false_writer_result :
    test [key] id (fun w => {w with priorReport := {w.priorReport with tree := .pending}}) = false := by
  decide +kernel

end Yulang.GeneralDeclarativeWitnessAuthFixture351
