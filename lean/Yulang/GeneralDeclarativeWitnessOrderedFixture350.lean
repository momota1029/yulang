import Yulang.GeneralDeclarativeWitnessRecordWhole350
import Yulang.GeneralDeclarativeWitnessRecordLeafFixture350

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeWitnessOrderedFixture350
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration Clause)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessManifest349 (Manifest attach)
open GeneralDeclarativeWitnessRecord349 (Wire)
open GeneralDeclarativeWitnessForest350 (ProblemTree Layout Code Codes anchor)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessCompiler350 (Finished printDemand execute)
open GeneralDeclarativeWitnessOneRecord350 (compilerCtx)
open GeneralDeclarativeWitnessRecordHeader350 (replay)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeWitnessRecordLeafFixture350 (source keep fallback recordWitness)
open GeneralDeclarativeWitnessCutDecl334 (arg pat)
open GeneralDeclarativeEndpointCase336 (endCode)
open GeneralDeclarativeEndpointMixedTail336 (width)

def clause0 : Clause := ⟨80,3,[.var 0],[]⟩
def clause1 : Clause := ⟨81,4,[.var 0],[]⟩
def parent : Declaration :=
  ⟨92,1,[pat],[clause0,clause1],[⟨91,0,.var 0⟩],[]⟩
def kid0 : Declaration := ⟨93,3,[.record 9 (.var 0) (.var 1)],[],[],[]⟩
def kid1 : Declaration := ⟨94,4,[.record 9 (.var 0) (.var 1)],[],[],[]⟩
def input : InputBundle := ⟨source,source,⟨0,[⟨1,1,[(0,none)]⟩,⟨3,1,[]⟩,⟨4,1,[]⟩]⟩,[parent,kid0,kid1]⟩
def root : Demand := ⟨1,[arg],[⟨0,5⟩]⟩

def nested : Expr := .record 9 (.primitive (.scalar .int) []) endCode
def rows : List Equation :=
  [⟨0,.record 7 (.variable 3) endCode⟩,⟨2,.record 7 (.variable 4) width⟩,
   ⟨3,nested⟩,⟨4,nested⟩]
def center : Equation := ⟨1,.record 7 (.variable 4) endCode⟩
def manifest : Manifest := ⟨rows⟩
def prior : State := ⟨⟨[],[(0,1),(1,2)]⟩,rows ++ [center]⟩
def rootLayout : Layout := ⟨prior,keep,fallback,fun _ _ => 0⟩
def baseTree (s : State) : ProblemTree := ⟨input,s,manifest,fun _ _ => rootLayout⟩
def projectedInput : Wire := ⟨⟨.interval 0,.interval 1⟩,.inline 0 .same,.inline 1 .same⟩

def finishedRoot : Option Finished := do
  let base := anchor (baseTree prior) [] root
  let env ← replay base.problem ⟨root.outputs⟩
  let attached ← attach prior manifest
  let read ← GeneralDeclarativeWitnessProjection349.decode attached arg pat projectedInput
  execute (compilerCtx (p := base) read env parent)


open GeneralDeclarativeWitnessBound349 (Path Shared)
open GeneralDeclarativeWitnessReceipt349 (Plan)
abbrev EqCode := GeneralDeclarativeWitnessEquation349.Code

def atomic (l h : Nat) : PresenceNormalForm.Atom Nat := .tyLe (.var l) (.var h)
def childEdges : List (Nat × Nat) := [(26,21),(21,27),(26,3),(3,26),(27,4),(4,27)]
def childBefore : State := GeneralDeclarativeCaptureClosure320.withOrdinary prior
  (childEdges.map fun (l,h) => atomic l h)

def childArg : Capture := ⟨26,21,27⟩
def q0 : Demand := ⟨3,[childArg],[]⟩
def q1 : Demand := ⟨4,[childArg],[]⟩

def branchLayout (slot : Nat) : Layout := ⟨childBefore,[slot],fallback,fun _ _ => 0⟩

def treeProblem (state : State) : ProblemTree := ⟨input,state,manifest,fun path _ =>
  match path with
  | [0] => branchLayout 49
  | [1] => branchLayout 79
  | _ => rootLayout⟩

def childRead : Wire :=
  ⟨⟨.constraint 0,.constraint 1⟩,
    .inline 2 (.order ⟨.constraint 2,.constraint 3⟩),
    .inline 3 (.order ⟨.constraint 4,.constraint 5⟩)⟩

def finishedChild (path : List Nat) (d : Demand) (decl : Declaration) : Option Finished := do
  let base := anchor (treeProblem childBefore) path d
  let env ← replay base.problem ⟨d.outputs⟩
  let attached ← attach base.before base.manifest
  let read ← GeneralDeclarativeWitnessProjection349.decode attached childArg (.record 9 (.var 0) (.var 1)) childRead
  execute (compilerCtx (p := base) read env decl)

def rootOutput : Equation := ⟨5,.variable 21⟩
def rootRows : List Equation :=
  [⟨20,.variable 3⟩,⟨21,.variable 4⟩,⟨22,.variable 4⟩,⟨23,endCode⟩,⟨24,endCode⟩,⟨25,width⟩]

def intCode : Expr := .primitive (.scalar .int) []
def leafRows (base : Nat) : List Equation :=
  [⟨base,intCode⟩,⟨base+1,intCode⟩,⟨base+2,intCode⟩,⟨base+3,endCode⟩,⟨base+4,endCode⟩,⟨base+5,endCode⟩]

def combined (parent first last : Finished) : State :=
  ⟨⟨(childEdges.map fun (l,h) => atomic l h) ++ parent.state.normal.ordinary ++
      first.state.normal.ordinary ++ last.state.normal.ordinary,[(0,1),(1,2)]⟩,
    prior.equations ++ [rootOutput] ++ rootRows ++ leafRows 50 ++ leafRows 80⟩

def data : Option (Finished × Finished × Finished) := do
  pure (← finishedRoot,← finishedChild [0] q0 kid0,← finishedChild [1] q1 kid1)

def indexEq (s : State) (e : Equation) : Option Nat := s.equations.findIdx? (fun q => decide (q = e))

def literalPlan (expect current : State) : Option Plan := do
  let entries ← expect.normal.ordinary.mapM (fun a => current.normal.ordinary.findIdx? (fun b => decide (a = b)))
  let ends ← expect.normal.intervals.mapM (fun e =>
    (current.normal.intervals.findIdx? (fun b => decide (e = b))).map Path.interval)
  let rows ← expect.equations.mapM (fun a => (indexEq current a).map GeneralDeclarativeWitnessEquation349.Code.currentRow)
  pure ⟨entries,ends,rows⟩

def eqCode (current : State) (n : Nat) (rhs : Expr) : Option EqCode :=
  (indexEq current ⟨n,rhs⟩).map GeneralDeclarativeWitnessEquation349.Code.currentRow

def mkProjection (s : State) (fields : List (Nat × Expr)) (shape : EqCode) (start : Nat)
    (lo mid hi : Expr) : Option GeneralDeclarativeWitnessExactRest349.Wire := do
  pure ⟨fields,endCode,shape,← eqCode s start lo,← eqCode s (start+1) mid,← eqCode s (start+2) hi⟩

def ranks : List Nat := (List.range 30).map fun x =>
  if x < 3 then 2 else if x ∈ [3,4,5,20,21,22,26,27] then 1 else 0

def parentCode (s : State) (p : Finished) : Option GeneralDeclarativeWitnessRecordReplay350.Wire := do
  let shape ← eqCode s 1 center.right
  let field ← mkProjection s [(7,.variable 4)] shape 20 (.variable 3) (.variable 4) (.variable 4)
  let rest ← mkProjection s [(7,.variable 4)] shape 23 endCode endCode width
  pure ⟨projectedInput,projectedInput,[(0,20,21,22),(1,23,24,25)],[field,rest],0,.same,ranks,
    ⟨[printDemand q0,printDemand q1],[rootOutput],← literalPlan p.state s⟩⟩

def childCode (s : State) (p : Finished) (base : Nat) : Option GeneralDeclarativeWitnessRecordReplay350.Wire := do
  let shape := GeneralDeclarativeWitnessEquation349.Code.compose (← eqCode s 21 (.variable 4)) (← eqCode s 4 nested)
  let field ← mkProjection s [(9,intCode)] shape base intCode intCode intCode
  let rest ← mkProjection s [(9,intCode)] shape (base+3) endCode endCode endCode
  pure ⟨childRead,childRead,[(0,base,base+1,base+2),(1,base+3,base+4,base+5)],[field,rest],
    2,.order ⟨.constraint 2,.constraint 3⟩,ranks,⟨[],[],← literalPlan p.state s⟩⟩

def problemAndCode : Option (ProblemTree × Code) := do
  let (parent,first,last) ← data
  let current := combined parent first last
  let outer ← parentCode current parent
  let l ← childCode current first 50
  let r ← childCode current last 80
  pure (treeProblem current,.node outer (.cons (.node l .nil) (.cons (.node r .nil) .nil)))

def answer : Report := ⟨.selected 92 [.selected 93 [],.selected 94 []],
  .selected (.node 92 [.node 93 [],.node 94 []]),root.outputs⟩

def test (w : Report) : Bool :=
  (problemAndCode.map (fun (p,code) => GeneralDeclarativeWitnessRecordWhole350.check p root code w)).getD false

theorem actual_children :
    (finishedRoot.map (fun f => decide (f.kids.map printDemand = [printDemand q0,printDemand q1]))).getD false = true := by
  decide +kernel

theorem accepted : test answer = true := by decide +kernel

theorem wrong_dictionary_order :
    test {answer with result := .selected (.node 92 [.node 94 [],.node 93 []])} = false := by
  decide +kernel

theorem wrong_diagnostic_order :
    test {answer with tree := .selected 92 [.selected 94 [],.selected 93 []]} = false := by
  decide +kernel

theorem extra_child_is_not_replayed :
    (problemAndCode.map (fun (p,code) => match code with
      | .node outer (.cons l (.cons r .nil)) =>
        GeneralDeclarativeWitnessRecordWhole350.check p root (.node outer (.cons l (.cons r (.cons r .nil)))) answer
      | _ => true)).getD true = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessOrderedFixture350
