import Yulang.GeneralDeclarativeWitnessMixedSiblings356
import Yulang.GeneralDeclarativeWitnessSpineFront355
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMixedFront356
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row Valuation)
open GeneralDeclarativeWitnessCovariantMetadata353 (Input)
open GeneralDeclarativeWitnessCovariantWrittenState353 (Line AllParsed rebuild all printRow exact_list)
open GeneralDeclarativeWitnessSpineFront355 (Site Authors authored literal_sites)
open GeneralDeclarativeWitnessSpineNode355 (Node)
open GeneralDeclarativeWitnessMixedScope356 (Scope)
open GeneralDeclarativeWitnessMixedSiblings356 (Plan BranchWire Accepted MixedEvidence sound)
open GeneralDeclarativeWitnessTypedRelease354 (Location)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

inductive SitePlan where
  | typed (first : Site) (rest : List Site)
  | ordinaryPayload (clause binder : Nat)

inductive Plans (cat : Input) : List SitePlan → List Plan → Type where
  | nil : Plans cat [] []
  | typed (now : AllParsed cat p.rows rows) (later : Authors cat ps as) :
      Plans cat more tail →
      Plans cat (.typed p ps :: more) (.typed ⟨p.encode rows,as⟩ :: tail)
  | ordinary : Plans cat more tail →
      Plans cat (.ordinaryPayload cl b :: more) (.payload cl b :: tail)

def parse (cat : Input) : (original : List SitePlan) → Option (Σ compiled,Plans cat original compiled)
  | [] => some ⟨[],.nil⟩
  | .typed first rest :: more => do
    let ⟨rows,yes⟩ ← all cat first.rows
    let ⟨as,known⟩ ← authored cat rest
    let ⟨later,tailProof⟩ ← parse cat more
    pure ⟨.typed ⟨first.encode rows,as⟩ :: later,.typed yes known tailProof⟩
  | .ordinaryPayload clause b :: more => do
    let ⟨all,verified⟩ ← parse cat more
    pure ⟨.payload clause b :: all,.ordinary verified⟩

def suppliedRows : SitePlan → List (List Line)
  | .typed first rest => (first :: rest).map Site.rows
  | .ordinaryPayload .. => []

def preparedRows : Plan → List (List Line)
  | .typed plan => (plan.first :: plan.rest).map (fun a => a.rows.map printRow)
  | .payload .. => []

theorem exact_plan_rows {cat ss ps} (plan : Plans cat ss ps) :
    ps.map preparedRows = ss.map suppliedRows := by
  induction plan with
  | nil => rfl
  | typed now more rest ih =>
    simp only [List.map_cons,preparedRows,suppliedRows,Site.encode,exact_list now,literal_sites more,ih]
  | ordinary rest ih =>
    simp only [List.map_cons,preparedRows,suppliedRows,ih]

structure Source where
  problem : Problem
  location : Location
  rootRows : List Line
  scope : Scope
  plans : List SitePlan

structure Wire where
  root : GeneralDeclarativeWitnessCovariantInterval353.Wire
  outputs : GeneralDeclarativeWitnessTypedPacket354.Report
  children : List BranchWire
  result : Report

structure Found (source : Source) (s : State) (w : Wire) where
  root : Node s
  exactRoot : root.input = {source.problem with rows := root.input.rows}
  written : AllParsed source.problem.metadata source.rootRows root.input.rows
  position : root.origin = source.location
  plans : List Plan
  authored : Plans source.problem.metadata source.plans plans
  replay : Accepted root source.scope w.result

def read (p : Source) (s : State) (w : Wire) : Option (Found p s w) :=
  match parsed : rebuild p.problem p.rootRows with
  | none => none
  | some root => do
    let ⟨plans,authored⟩ ← parse p.problem.metadata p.plans
    let closed ← GeneralDeclarativeWitnessTypedRangeWriter354.decode root.1 w.root s w.outputs
    let witnessed : Node s := ⟨root.1,p.location,w.root,w.outputs,closed⟩
    let got ← GeneralDeclarativeWitnessMixedSiblings356.decode witnessed p.scope plans w.children w.result
    pure ⟨witnessed,GeneralDeclarativeWitnessCovariantFront353.unchanged parsed,root.2,rfl,plans,authored,got⟩

theorem exact_authors {p s w} (a : Found p s w) :
    a.root.input.rows.map printRow = p.rootRows ∧ a.plans.map preparedRows = p.plans.map suppliedRows :=
  ⟨exact_list a.written,exact_plan_rows a.authored⟩

theorem replay_in_one_model {p s w} (a : Found p s w) (m : Assignment) (fit : Models s m) :
    w.result.result = .selected (.node a.root.name a.replay.children.dictionaries) ∧
    w.result.outputs = p.problem.demand.outputs ∧
    ∃ v : Valuation,
      GeneralDeclarativeWitnessTypedEvidence355.Local m v a.root ∧
      All₂ (MixedEvidence a.root m v) a.root.proof.compiled.children a.replay.children.dictionaries := by
  have result := sound a.replay m fit
  have same := congrArg Problem.demand a.exactRoot
  have inputDemand : a.root.input.demand = p.problem.demand := same
  exact ⟨result.2.1,by simpa only [inputDemand] using result.2.2.1,result.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessMixedFront356
