import Yulang.GeneralDeclarativeI65Comparison365
import Yulang.GeneralDeclarativeWitnessClassifyVariance357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonDeclaredNominalInspection (Registry)
open CommonRecursiveNominalIntervals (Endpoint ContextWellFormed)
open GeneralDeclarativeWitnessDeclaredState357
  (Current Views ModelsCurrent WrittenBody authoredRegistry)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeAssembly320 (Prepared Meaning)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceMetadataRows291 (interpretation)
open CommonRoleOutermostResolver (All₂)

/-- An original source observation; physical positions must be carried
by an explicit source fact, not guessed from ordinary solver aliases. -/
structure Origin where
  slot : Nat
  issuer : List Nat
  endpoint : Endpoint Nat

structure Alias where
  logical : Nat
  physical : Nat
  issuer : List Nat

structure State where
  current : Current
  modes : Registry
  origins : List Origin
  routes : List Alias

inductive OriginRoute (s : State) (read : Origin) : Nat → Prop where
  | direct : OriginRoute s read read.slot
  | authored : ⟨logical,read.slot,read.issuer⟩ ∈ s.routes → OriginRoute s read logical

structure Model where
  assignment : Assignment
  authoredValues : Views
  nativeSyntax : Nat → Option (Endpoint Nat)

def Fits (s : State) (m : Model) : Prop :=
  ModelsCurrent s.current m.assignment m.authoredValues ∧
  ∀ read ∈ s.origins, m.nativeSyntax read.slot = some read.endpoint

structure Request where
  occurrence : List Nat
  demand : Demand

def children (q : Request) (ds : List Demand) : List Request :=
  ds.zipIdx |>.map fun (child,i) => ⟨q.occurrence ++ [i],child⟩

def visible (s : State) (q : Request) : List Declaration :=
  (authoredRegistry s.current).declarations.filter fun row => row.role == q.demand.role

theorem visible_exact (s : State) (q : Request) (d : Declaration) :
    d ∈ visible s q ↔ d ∈ (authoredRegistry s.current).declarations ∧ d.role = q.demand.role := by
  simp [visible]

/-- Relate occurrence input to original syntax without an assignment.
A declared contextual comparison is separate from observing either
native endpoint, and neither uses the actual-center row as a head. -/
structure ModeWindow (s : State) (arg : Capture) (p : Pattern) where
  lower : Origin
  upper : Origin
  lo : OriginRoute s lower arg.lower
  hi : OriginRoute s upper arg.upper
  lowerAuthored : lower ∈ s.origins
  upperAuthored : upper ∈ s.origins
  name : Nat
  arguments : List Pattern
  syntaxHead : normalize p = .app name arguments
  firstArgs : List (CommonRecursiveNominalIntervals.Argument Nat)
  lastArgs : List (CommonRecursiveNominalIntervals.Argument Nat)
  firstHead : lower.endpoint = .nominal name firstArgs
  lastHead : upper.endpoint = .nominal name lastArgs
  modeRead : DeclaredComparison s.current.environment s.current.ordinary s.modes false
    lower.endpoint upper.endpoint

structure WindowMeaning {s : State} {arg : Capture} {p : Pattern}
    (w : ModeWindow s arg p) (m : Model) : Prop where
  lowerRoute : OriginRoute s w.lower arg.lower
  upperRoute : OriginRoute s w.upper arg.upper
  lower : m.nativeSyntax w.lower.slot = some w.lower.endpoint
  upper : m.nativeSyntax w.upper.slot = some w.upper.endpoint
  lowerKind : ContextWellFormed s.modes false w.lower.endpoint
  upperKind : ContextWellFormed s.modes false w.upper.endpoint
  typed : ContextDerives s.modes m.assignment false w.lower.endpoint w.upper.endpoint

theorem mode_window_sound {s : State} {arg : Capture} {p : Pattern}
    (read : ModeWindow s arg p) (m : Model) (fit : Fits s m) : WindowMeaning read m := by
  obtain ⟨a,b,typed⟩ := in_same_model read.modeRead m.assignment fit.1.1
  exact ⟨read.lo,read.hi,fit.2 _ read.lowerAuthored,fit.2 _ read.upperAuthored,a,b,typed⟩

/-- Existing exact output receipt theorem, but with the source rule,
request, captures, literal children and result rows all retained at the
same named declarative state. This is not itself election evidence. -/
structure BodyFacts (s : State) (q : Request) (row : Declaration) (kids : List Request) where
  spans : List (Nat × Capture)
  demands : List Demand
  body : WrittenBody s.current q.demand row spans demands
  order : kids = children q demands

theorem body_facts_sound {s : State} {q : Request} {row : Declaration} {kids : List Request}
    (body : BodyFacts s q row kids) (m : Model) (fit : Fits s m) :
    body.body.finished.fixed.map Equation.left = q.demand.outputs.map GeneralSourceState.Output.target ∧
    ∀ fixed ∈ body.body.finished.fixed, Holds m.assignment fixed :=
  GeneralDeclarativeWitnessDeclaredState357.output_meaning body.body m.assignment fit.1.1

theorem children_are_actual_requests {s : State} {q : Request} {row : Declaration} {kids : List Request}
    (body : BodyFacts s q row kids) (sig : row.Signature (authoredRegistry s.current).roles) :
    ∀ child ∈ body.demands, GeneralDeclarativeOutputSource323.Declared (authoredRegistry s.current) child :=
  GeneralDeclarativeWitnessDeclaredState357.body_declared body.body sig

end Yulang.GeneralDeclarativeI65
