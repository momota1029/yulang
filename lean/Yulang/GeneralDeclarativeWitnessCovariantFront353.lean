import Yulang.GeneralDeclarativeWitnessCovariantCanonical353
import Yulang.GeneralDeclarativeWitnessCovariantWrittenState353

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantFront353
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem)
open GeneralDeclarativeWitnessCovariantWrittenState353 (Line AllParsed rebuild printRow exact_list)
open GeneralDeclarativeWitnessCovariantIntervalForest353 (Wire Accepted)
open GeneralDeclarativeWitnessCovariantForest353 (Environment)
open GeneralDeclarativeWitnessForest350 (Layout)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open CommonRoleOutermostResolver (All₂)
open GeneralSourceMetadataExprDomain291 (bind_success)

theorem unchanged {p : Problem} {ls : List Line} {actual}
    (built : rebuild p ls = some actual) :
    actual.1 = {p with rows := actual.1.rows} := by
  unfold rebuild at built
  obtain ⟨r,_,eq⟩ := bind_success built
  cases Option.some.inj eq
  rfl

/-- Fixed problem data, including *written* rows and the separate
ordinary child origins. The solver wire carries none of these. -/
structure Input where
  base : Problem
  written : List Line
  origins : Table
  layout : List Nat → Demand → Layout

def Input.scope {i : Input} (p : Problem) : Environment p :=
  ⟨i.origins,i.layout⟩

structure Result (i : Input) (state : State) (w : Wire) (report : Report) where
  typed : Problem
  exactProblem : typed = {i.base with rows := typed.rows}
  fromWritten : AllParsed i.base.metadata i.written typed.rows
  receipt : Accepted typed (Input.scope (i := i) typed) state w report
  ran : GeneralDeclarativeWitnessCovariantIntervalForest353.decode typed (Input.scope (i := i) typed) state w report =
    some receipt

def decode (i : Input) (state : State) (w : Wire) (report : Report) : Option (Result i state w report) :=
  match parsed : rebuild i.base i.written with
  | none => none
  | some q =>
    match ran : GeneralDeclarativeWitnessCovariantIntervalForest353.decode q.1 (Input.scope (i := i) q.1)
        state w report with
    | none => none
    | some accepted => some ⟨q.1,unchanged parsed,q.2,accepted,ran⟩

theorem exact_author_report {i : Input} {s : State} {w : Wire} {report : Report}
    (a : Result i s w report) (m : Assignment) (fit : Models s m) :
    a.typed.rows.map printRow = i.written ∧
    report.result = .selected (.node a.receipt.root.facts.center.decl.id a.receipt.children.entries) ∧
    report.outputs = i.base.demand.outputs ∧
    All₂ (Evidence (registry a.receipt.ordinary) (interpretation a.receipt.ordinary.snapshot) m)
      a.receipt.root.compiler.compiled.kids a.receipt.children.entries ∧
    w.rootOut.outputRows.map Equation.left = i.base.demand.outputs.map GeneralSourceState.Output.target ∧
    ∀ row ∈ w.rootOut.outputRows,Holds m row := by
  have truth := GeneralDeclarativeWitnessCovariantCanonical353.all_models a.ran m fit
  have scopedDemand := congrArg Problem.demand a.exactProblem
  have inputDemand : a.typed.demand = i.base.demand := scopedDemand
  exact ⟨exact_list a.fromWritten,truth.2.2.2.1,by simpa only [inputDemand] using truth.2.2.2.2.1,
    truth.2.2.1,by simpa only [inputDemand] using truth.2.2.2.2.2.1,truth.2.2.2.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessCovariantFront353
