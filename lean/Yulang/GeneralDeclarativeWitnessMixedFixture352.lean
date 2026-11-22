import Yulang.GeneralDeclarativeWitnessMixedWhole352
import Yulang.GeneralDeclarativeWitnessOrderedFixture350
import Yulang.GeneralDeclarativeWitnessTagFixture351

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 19000000
namespace Yulang.GeneralDeclarativeWitnessMixedFixture352
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open GeneralDeclarativeWitnessForest350 (Layout)
open GeneralDeclarativeWitnessMixedForest352 (Problem Code Codes NodeCode atNode)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessCompiler350 (Context Finished execute printDemand)
open GeneralDeclarativeWitnessTagBranch352 (Wire)
open GeneralDeclarativeWitnessTagElection352 (Ends reads)
open GeneralDeclarativeWitnessTagSources351 (Script Ref)
open GeneralDeclarativeWitnessTagLocal351 (parse context)
open GeneralDeclarativeWitnessAuthNode351 (compilerCtx)
open GeneralDeclarativeWitnessTagHeader352 (replay)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessOrderedFixture350
  (root parent q0 q1 childArg childEdges atomic rootOutput literalPlan eqCode mkProjection)
open GeneralDeclarativeWitnessRecordLeafFixture350 (source keep fallback)
open GeneralDeclarativeWitnessCutDecl334 (arg pat)
open GeneralDeclarativeEndpointCase336 (endCode rowLo)
open GeneralDeclarativeEndpointMixedTail336 (width rowHi)
open GeneralDeclarativeWitnessRecordFixture349 (center)
open GeneralDeclarativeTaggedFixture340 (eInt eBool)
open GeneralDeclarativeWitnessAllocation350 (names)

def h : GeneralDeclarationPatterns.Pattern := .variant 7 (.var 0)
def child0 : Declaration := ⟨93,3,[h],[],[],[]⟩
def child1 : Declaration := ⟨94,4,[h],[],[],[]⟩
def input : InputBundle := ⟨source,source,⟨0,[⟨1,1,[(0,none)]⟩,⟨3,1,[]⟩,⟨4,1,[]⟩]⟩,
  [parent,child0,child1]⟩

def paired : GeneralNominalCenteredHeadMatExpressions.Expr := .join (.variable 8) (.variable 9)
def author : List Equation :=
  [rowLo,rowHi,⟨3,paired⟩,⟨4,paired⟩,⟨8,.variant 7 eInt⟩,⟨9,.variant 7 eBool⟩]
def before : State := ⟨⟨[],[(0,1),(1,2)]⟩,author ++ [center]⟩
def authorView : Table := ⟨author,[],[]⟩
def childBefore : State := GeneralDeclarativeCaptureClosure320.withOrdinary before
  (childEdges.map fun (l,h) => atomic l h)

def layout (path : List Nat) (_ : Demand) : Layout :=
  let start := if path.isEmpty then before else childBefore
  let keep := if path = [0] then [49] else if path = [1] then [79] else keep
  ⟨start,keep,fallback,fun _ _ => 0⟩

def problem (s : State) : GeneralDeclarativeWitnessMixedForest352.Problem :=
  ⟨input,s,authorView,root,layout⟩

def rootRead : GeneralDeclarativeWitnessRecord349.Wire :=
  ⟨⟨.interval 0,.interval 1⟩,.inline 0 .same,.inline 1 .same⟩

def parentStage : Option Finished := do
  let base := atNode (problem before) [] root
  let words ← replay base.problem ⟨root.outputs⟩
  let a ← attach base.before authorView
  let verified ← GeneralDeclarativeWitnessReleased350.project a arg pat rootRead
  execute (compilerCtx (p := base) verified words parent)

def arms : Script := .join (.named ⟨4,.same⟩ .tagged) (.named ⟨5,.same⟩ .tagged)
def childBounds : GeneralDeclarativeWitnessBound349.Range := ⟨.constraint 0,.constraint 1⟩
def childEnds : Ends :=
  .recursive (.named ⟨2,.order ⟨.constraint 2,.constraint 3⟩⟩ arms)
    (.named ⟨3,.order ⟨.constraint 4,.constraint 5⟩⟩ arms)

def childContext (path : List Nat) (d : Demand) (impl : Declaration) : Option Context := do
  let base := atNode (problem childBefore) path d
  let words ← replay base.problem ⟨d.outputs⟩
  let a ← attach base.before authorView
  let verified ← reads a childArg 7 childBounds childEnds
  let scanned ← parse (registry words).constructors (interpretation words.snapshot) h 7
  pure (context (r := registry words) d impl verified scanned base.keep base.fallback base.targets)

def parentProjectionRows : List Equation :=
  [⟨20,.variable 3⟩,⟨21,.variable 4⟩,⟨22,.variable 4⟩,
    ⟨23,endCode⟩,⟨24,endCode⟩,⟨25,width⟩]

def combined (parent left right : Finished) : State :=
  ⟨⟨(childEdges.map fun (l,h) => atomic l h) ++ parent.state.normal.ordinary ++
      left.state.normal.ordinary ++ right.state.normal.ordinary,[(0,1),(1,2)]⟩,
    parent.state.equations ++ left.state.equations ++ right.state.equations ++ parentProjectionRows⟩

def levels : List Nat := (List.range 100).map (fun x =>
  if x < 3 then 3 else if x ∈ [3,4,5,20,21,22,26,27] then 2
  else if x ∈ [8,9] then 1 else 0)

def rootCode (f : Finished) (state : State) : Option GeneralDeclarativeWitnessRecordReplay350.Wire := do
  let shape ← eqCode state 1 center.right
  let first ← mkProjection state [(7,.variable 4)] shape 20 (.variable 3) (.variable 4) (.variable 4)
  let rest ← mkProjection state [(7,.variable 4)] shape 23 endCode endCode width
  pure ⟨rootRead,rootRead,[(0,20,21,22),(1,23,24,25)],[first,rest],0,.same,levels,
    ⟨[printDemand q0,printDemand q1],[rootOutput],← literalPlan f.state state⟩⟩

def taggedCode (ctx : Context) (f : Finished) (state : State) : Option Wire := do
  pure ⟨childBounds,childEnds,childBounds,childEnds,levels,names ctx.spans,
    ⟨[],[],← literalPlan f.state state⟩⟩

def data : Option (State × Code) := do
  let top ← parentStage
  let l ← childContext [0] q0 child0
  let r ← childContext [1] q1 child1
  let left ← execute l
  let right ← execute r
  let current := combined top left right
  let parent ← rootCode top current
  let readL ← taggedCode l left current
  let readR ← taggedCode r right current
  pure (current,.node (.record parent) (.cons (.node (.tagged readL) .nil) (.cons (.node (.tagged readR) .nil) .nil)))

def answer : Report := ⟨.selected 92 [.selected 93 [],.selected 94 []],
  .selected (.node 92 [.node 93 [],.node 94 []]),root.outputs⟩

def test (report : Report) (changed : Code → Code := id) : Bool :=
  (data.map fun (s,code) => GeneralDeclarativeWitnessMixedWhole352.check (problem s) root (changed code) report).getD false

theorem accepted : test answer = true := by decide +kernel

theorem reordered_children :
    test answer (fun
      | .node top (.cons one (.cons two .nil)) => .node top (.cons two (.cons one .nil))
      | other => other) = false := by decide +kernel

theorem proof_of_wrong_role_order :
    test {answer with result := .selected (.node 92 [.node 94 [],.node 93 []])} = false := by decide +kernel

def missingArm : Ends :=
  .recursive (.named ⟨2,.order ⟨.constraint 2,.constraint 3⟩⟩ (.named ⟨4,.same⟩ .tagged))
    (.named ⟨3,.order ⟨.constraint 4,.constraint 5⟩⟩ arms)

theorem omitted_named_arm :
    test answer (fun
      | .node top (.cons (.node (.tagged w) .nil) tail) =>
        let edited := {w with currentReads := missingArm}
        .node top (.cons (.node (.tagged edited) .nil) tail)
      | other => other) = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessMixedFixture352
