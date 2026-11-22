import Yulang.GeneralDeclarativeWitnessCovariantForest353
import Yulang.GeneralDeclarativeWitnessCovariantFixture353

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 25000000
namespace Yulang.GeneralDeclarativeWitnessCovariantNested353
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem)
open GeneralDeclarativeWitnessCovariantCompiler353 (prepare)
open GeneralDeclarativeWitnessCovariantSubtree353 (problem)
open GeneralDeclarativeWitnessCovariantForest353 (Environment Wire ChildWire decode)
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open GeneralDeclarativeWitnessForest350 (Layout)
open GeneralDeclarativeWitnessMixedForest352 (Code atNode)
open GeneralDeclarativeWitnessTagLocal351 (parse context)
open GeneralDeclarativeWitnessTagElection352 (Ends reads)
open GeneralDeclarativeWitnessTagHeader352 (replay)
open GeneralDeclarativeWitnessTagSources351 (Script)
open GeneralDeclarativeWitnessBound349 (Range)
open GeneralDeclarativeWitnessCompiler350 (Context Finished execute printDemand)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessCovariantFixture353 (eInt eBool payload root wire out)
open GeneralDeclarativeWitnessAllocation350 (names)

def pat : GeneralDeclarationPatterns.Pattern := .variant 7 (.var 0)
def node0 : Declaration := ⟨93,3,[pat],[],[],[]⟩
def node1 : Declaration := ⟨94,4,[pat],[],[],[]⟩
def ordinaryRows : List Equation := [⟨7,.variant 7 eInt⟩,⟨8,.variant 7 eBool⟩,payload]
def start : State := ⟨⟨[],[]⟩,ordinaryRows⟩

def rootProblem : Problem :=
  let old := GeneralDeclarativeWitnessCovariantFixture353.problem
  let src := old.metadata.sourceInput
  let nested := {src with declarations := [GeneralDeclarativeWitnessCovariantFixture353.parent,node0,node1]}
  let updated := {old.metadata with sourceInput := nested}
  {old with stage := start, metadata := updated}

def origin : Table := ⟨ordinaryRows,[],[]⟩
def layout (f : Finished) (path : List Nat) (_ : Demand) : Layout :=
  ⟨f.state,if path = [0] then [49] else [79],fun _ => ⟨9,9,9⟩,fun _ _ => 0⟩
def environment (top : Finished) : Environment rootProblem := ⟨origin,layout top⟩

def lower (second : Bool) : Nat := if second then 10 else 2
def span (second : Bool) : Range := ⟨.constraint (lower second + 4),.constraint (lower second + 5)⟩
def arms : Script := .join (.named ⟨0,.same⟩ .tagged) (.named ⟨1,.same⟩ .tagged)
def witnesses (second : Bool) : Ends :=
  let i := lower second
  .recursive (.named ⟨2,.order ⟨.constraint i,.constraint (i+1)⟩⟩ arms)
    (.named ⟨2,.order ⟨.constraint (i+2),.constraint (i+3)⟩⟩ arms)

def ctx (top : Finished) (idx : Nat) (d : Demand) (impl : Declaration) (second : Bool) : Option Context := do
  let pr := problem rootProblem top.state d origin (layout top)
  let current := atNode pr [idx] d
  let tab ← replay current.problem ⟨d.outputs⟩
  let attached ← attach top.state origin
  let arg ← d.arguments[0]?
  let view ← reads attached arg 7 (span second) (witnesses second)
  let parsed ← parse (registry tab).constructors (interpretation tab.snapshot) pat 7
  pure (context (r := registry tab) d impl view parsed current.keep current.fallback current.targets)

def combined (l r : Finished) : State :=
  ⟨⟨l.state.normal.ordinary ++ r.state.normal.ordinary,[]⟩,l.state.equations ++ r.state.equations⟩

def rank : List Nat := (List.range 100).map fun i =>
  if i ∈ [5,6,9,32,33,34,35] then 1 else 0

def fromBranch (s : State) (scope : Context) (f : Finished) (second : Bool) : Option Code := do
  let receipt ← literalPlan f.state s
  let written := ⟨span second,witnesses second,span second,witnesses second,rank,names scope.spans,
    ⟨[],[],receipt⟩⟩
  pure (.node (.tagged written) .nil)

def childReport (key : Nat) : Report := ⟨.selected key [],.selected (.node key []),[]⟩
def report : Report := ⟨.selected 92 [.selected 93 [],.selected 94 []],
  .selected (.node 92 [.node 93 [],.node 94 []]),root.outputs⟩

def data : Option (Finished × State × Wire) := do
  let r ← prepare rootProblem wire
  let f ← execute r.ctx
  let l ← f.kids[0]?
  let h ← f.kids[1]?
  let left ← ctx f 0 l node0 false
  let last ← ctx f 1 h node1 true
  let a ← execute left
  let b ← execute last
  let current := combined a b
  let x ← fromBranch current left a false
  let y ← fromBranch current last b true
  let proof ← literalPlan f.state current
  pure (f,current,⟨wire,⟨f.kids.map printDemand,f.fixed,proof⟩,
    [⟨x,childReport 93⟩,⟨y,childReport 94⟩]⟩)

def check (update : Wire → Wire := id) (answer : Report := report) : Bool :=
  (data.map (fun (f,s,w) => (decode rootProblem (environment f) s (update w) answer).isSome)).getD false

theorem success : check = true := by decide +kernel

theorem drops_actual_child : check (fun w => {w with children := w.children.take 1}) = false := by decide +kernel

theorem reorders_actual_children : check (fun w => {w with children := w.children.reverse}) = false := by decide +kernel

theorem result_order_is_checked :
    check id {report with result := .selected (.node 92 [.node 94 [],.node 93 []])} = false := by decide +kernel

theorem does_not_rewrite_fixed_targets :
    check id {report with outputs := [⟨0,5⟩,⟨1,9⟩]} = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessCovariantNested353
