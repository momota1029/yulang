import Yulang.GeneralDeclarativeWitnessOrderedFixture350
import Yulang.GeneralDeclarativeWitnessTies350

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
set_option maxRecDepth 29000
namespace Yulang.GeneralDeclarativeWitnessRepeatedFixture350
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessCompiler350 (Finished execute)
open GeneralDeclarativeWitnessOneRecord350 (Anchor compilerCtx)
open GeneralDeclarativeWitnessRecordHeader350 (replay)
open GeneralDeclarativeWitnessManifest349 (Manifest attach)
open GeneralDeclarativeWitnessRecord349 (Wire)
open GeneralDeclarativeWitnessForest350 (ProblemTree Layout)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeWitnessOrderedFixture350 (eqCode mkProjection literalPlan)
open GeneralDeclarativeWitnessRecordLeafFixture350 (source)
open GeneralDeclarativeWitnessCutDecl334 (arg)
open GeneralDeclarativeEndpointCase336 (endCode)
open GeneralDeclarativeEndpointMixedTail336 (width)

def pat : Pattern := .record 7 (.var 0) (.record 8 (.var 0) (.var 1))
def parent : Declaration := ⟨92,1,[pat],[],[⟨91,0,.var 0⟩],[]⟩
def input : InputBundle := ⟨source,source,⟨0,[⟨1,1,[(0,none)]⟩]⟩,[parent]⟩
def root : Demand := ⟨1,[arg],[⟨0,5⟩]⟩
def lo : Equation := ⟨0,.record 7 (.variable 3) (.record 8 (.variable 4) endCode)⟩
def hi : Equation := ⟨2,.record 7 (.variable 6) (.record 8 (.variable 7) width)⟩
def center : Equation := ⟨1,.record 7 (.variable 4) (.record 8 (.variable 4) endCode)⟩
def prior : State := ⟨⟨[],[(0,1),(1,2)]⟩,[lo,hi,center]⟩
def manifest : Manifest := ⟨[lo,hi]⟩
def problem (s : State) : ProblemTree :=
  ⟨input,s,manifest,fun _ _ => ⟨prior,[19],fun _ => arg,fun _ _ => 0⟩⟩
def anchor (s : State) : Anchor := GeneralDeclarativeWitnessForest350.anchor (problem s) [] root
def readCode : Wire := ⟨⟨.interval 0,.interval 1⟩,.inline 0 .same,.inline 1 .same⟩

def finished : Option Finished := do
  let base := anchor prior
  let env ← replay base.problem ⟨root.outputs⟩
  let a ← attach prior manifest
  let read ← GeneralDeclarativeWitnessProjection349.decode a arg pat readCode
  execute (compilerCtx (p := base) read env parent)

def fixedOut : Equation := ⟨5,.variable 21⟩
def theTie : Equation := ⟨21,.variable 24⟩
def evidenceRows : List Equation :=
  [⟨20,.variable 3⟩,⟨21,.variable 4⟩,⟨22,.variable 6⟩,
    ⟨23,.variable 4⟩,⟨24,.variable 4⟩,⟨25,.variable 7⟩,
    ⟨26,endCode⟩,⟨27,endCode⟩,⟨28,width⟩]

def fullState (run : Finished) : State :=
  GeneralDeclarativeEntailment320.appendFacts run.state evidenceRows

def levels : List Nat := [1,1,1]

def witness (run : Finished) (s : State) (ranks : List Nat) : Option GeneralDeclarativeWitnessRecordReplay350.Wire := do
  let shape ← eqCode s 1 center.right
  let fields : List (Nat × Expr) := [(7,.variable 4),(8,.variable 4)]
  let f ← mkProjection s fields shape 20 (.variable 3) (.variable 4) (.variable 6)
  let g ← mkProjection s fields shape 23 (.variable 4) (.variable 4) (.variable 7)
  let rest ← mkProjection s fields shape 26 endCode endCode width
  let receipt ← literalPlan run.state s
  pure ⟨readCode,readCode,[(0,20,21,22),(0,23,24,25),(1,26,27,28)],[f,g,rest],0,.same,ranks,
    ⟨[],[fixedOut],receipt⟩⟩

def answer : Report := ⟨.selected 92 [],.selected (.node 92 []),root.outputs⟩

def acceptedWith (extend : State → State) (make : Finished → State → Option GeneralDeclarativeWitnessRecordReplay350.Wire) :
    Bool := (do
  let compiled ← finished
  let live := extend (fullState compiled)
  let a ← make compiled live
  pure (GeneralDeclarativeWitnessRecordWhole350.check (problem live) root (.node a .nil) answer) : Option Bool).getD false

theorem compiler_tie :
    (finished.map fun ran => decide (theTie ∈ ran.state.equations)).getD false = true := by decide +kernel

theorem accepted :
    acceptedWith id (fun compiled live => witness compiled live levels) = true := by decide +kernel

theorem wrong_rank_not_positive :
    acceptedWith id (fun compiled live => witness compiled live []) = false := by decide +kernel

def unsupportedCycle : Equation := ⟨0,.record 7 (.variable 0) endCode⟩

/-- This structural cycle is *not* in the input manifest. The positive
rank checker still sees the ordinary row. Failure of this positive
certificate is not itself a rejection diagnostic. -/
theorem unbacked_cycle_not_positive :
    acceptedWith (fun s => GeneralDeclarativeEntailment320.appendFacts s [unsupportedCycle])
      (fun compiled live => witness compiled live levels) = false := by decide +kernel

def removeTie (s : State) : State :=
  {s with equations := s.equations.filter (fun q => decide (q ≠ theTie))}

def aliasInstead (code : GeneralDeclarativeWitnessReceipt349.Plan) (ran : Finished) (s : State) :
    Option GeneralDeclarativeWitnessReceipt349.Plan := do
  let a ← eqCode s 21 (.variable 4)
  let b ← eqCode s 24 (.variable 4)
  let equations ← ran.state.equations.mapM (fun e =>
    if e = theTie then some (.compose a (.reverse b)) else (eqCode s e.left e.right))
  pure {code with equations}

def buildNoLiteralTie (ran : Finished) (s : State) : Option GeneralDeclarativeWitnessRecordReplay350.Wire := do
  let witnessed ← witness ran (fullState ran) levels
  let aligned ← aliasInstead witnessed.emitted.receipt ran s
  let shape ← eqCode s 1 center.right
  let fields : List (Nat × Expr) := [(7,.variable 4),(8,.variable 4)]
  let f ← mkProjection s fields shape 20 (.variable 3) (.variable 4) (.variable 6)
  let g ← mkProjection s fields shape 23 (.variable 4) (.variable 4) (.variable 7)
  let rest ← mkProjection s fields shape 26 endCode endCode width
  pure {witnessed with projections := [f,g,rest],emitted := {witnessed.emitted with receipt := aligned}}

/-- The compiled tie is required in the same model, not necessarily as
that literal row. An independently checked ordinary derivation may
justify it; merely matching interval heads cannot. -/
theorem derived_tie_accepted :
    acceptedWith removeTie buildNoLiteralTie = true := by decide +kernel

end Yulang.GeneralDeclarativeWitnessRepeatedFixture350
