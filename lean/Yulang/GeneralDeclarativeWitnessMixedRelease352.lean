import Yulang.GeneralDeclarativeWitnessMixedWhole352
import Yulang.GeneralDeclarativeWitnessCompletion351

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMixedRelease352
open GeneralDeclarativeHead320 (Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessIdentity351 (Stamp Owned table)
open GeneralDeclarativeWitnessCatalog351 (Anchor WriteAnchor Receipt proves_writes)
open GeneralDeclarativeWitnessFreshness351 (position distinctTrace single_position)
open GeneralDeclarativeWitnessForest350 (Layout Fixed)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Dictionary)

structure Problem where
  publisher : Anchor
  source : InputBundle
  root : Demand
  layout : List Nat → Demand → Layout

structure Wire where
  producer : GeneralDeclarativeWitnessForest350.Code
  priorReport : Report
  consumer : GeneralDeclarativeWitnessMixedForest352.Code

def downstream (p : Problem) (owned : List Owned) : GeneralDeclarativeWitnessMixedForest352.Problem :=
  ⟨p.source,p.publisher.roles.current,table p.publisher.authored owned p.publisher.releases,p.root,p.layout⟩

def stamps (p : Problem) (active : List Stamp) : Bool :=
  decide ((active.map position).Nodup) &&
  p.publisher.required.all (fun anchor => active.contains anchor.producer)

structure Accepted (p : Problem) (active : List Stamp) (w : Wire) (report : Report) where
  live : stamps p active = true
  prior : Receipt p.publisher w.producer w.priorReport
  consumer : GeneralDeclarativeWitnessMixedWhole352.Accepted (downstream p prior.owned) p.root report
  exactPrior : (prior.producer.diagnostic.fixed.map Fixed.path).Nodup
  exactConsumer : (consumer.diagnostic.fixed.map Fixed.path).Nodup

/-- Both checkers use the same original state. The consumer takes its
origin catalogue only from independently computed producer receipts,
never a duplicate solver-supplied table. -/
def decode (p : Problem) (active : List Stamp) (w : Wire) (report : Report) :
    Option (Accepted p active w report) := do
  if live : stamps p active = true then
    let prior ← GeneralDeclarativeWitnessCatalog351.check p.publisher w.producer w.priorReport
    let consumer ← GeneralDeclarativeWitnessMixedWhole352.decode (downstream p prior.owned) p.root w.consumer report
    if a : (prior.producer.diagnostic.fixed.map Fixed.path).Nodup then
      if b : (consumer.diagnostic.fixed.map Fixed.path).Nodup then
        pure ⟨live,prior,consumer,a,b⟩
      else none
    else none
  else none

def check (p : Problem) (active : List Stamp) (w : Wire) (report : Report) : Bool :=
  (decode p active w report).isSome

theorem checked {p : Problem} {active : List Stamp} {w : Wire} {report : Report}
    (ok : check p active w report = true) : Nonempty (Accepted p active w report) := by
  unfold check at ok
  cases found : decode p active w report with
  | none => simp [found] at ok
  | some a => exact ⟨a⟩

theorem active_place {p : Problem} {active : List Stamp} {w : Wire} {report : Report}
    (a : Accepted p active w report) {x y : WriteAnchor}
    (left : x ∈ p.publisher.required) (right : y ∈ p.publisher.required)
    (same : position x.producer = position y.producer) :
    x.producer = y.producer := by
  have ok := splitAnd a.live
  have member (loc : WriteAnchor) (seen : loc ∈ p.publisher.required) : loc.producer ∈ active :=
    (List.contains_iff_mem).mp (List.all_eq_true.mp ok.2 _ seen)
  exact single_position (of_decide_eq_true ok.1) (member x left) (member y right) same

theorem actual_writes {p : Problem} {active : List Stamp} {w : Wire} {report : Report}
    (a : Accepted p active w report) (m : Assignment) (fit : Models p.publisher.roles.current m) :
    ∀ owned ∈ a.prior.owned, ∃ loc ∈ p.publisher.required, ∃ block ∈ a.prior.producer.diagnostic.fixed,
      block.path = loc.producer.path ∧ block.demand.role = loc.producer.role ∧
      block.equations[loc.ordinal]? = some owned.equation ∧
      owned.key = ⟨loc.producer.path,loc.producer.role,loc.producer.version,loc.ordinal,owned.equation.left⟩ ∧
      GeneralDeclarativeEntailment320.Holds m owned.equation :=
  proves_writes a.prior m fit

theorem two_reports {p : Problem} {active : List Stamp} {w : Wire} {report : Report}
    (a : Accepted p active w report) (d : Dictionary) (selected : report.result = .selected d) :
    ∃ prior : Dictionary, w.priorReport.result = .selected prior ∧ report.outputs = p.root.outputs ∧
      ∀ m : Assignment, Models p.publisher.roles.current m →
        Evidence (registry a.prior.producer.global.table)
          (interpretation a.prior.producer.global.table.snapshot) m p.publisher.root prior ∧
        Evidence (registry a.consumer.global.table)
          (interpretation a.consumer.global.table.snapshot) m p.root d ∧
        ∀ f ∈ a.consumer.diagnostic.fixed, f.equations.map Equation.left =
          f.demand.outputs.map GeneralSourceState.Output.target ∧
          ∀ e ∈ f.equations, GeneralDeclarativeEntailment320.Holds m e := by
  have earlier := (GeneralDeclarativeWitnessRecordWhole350.agreed a.prior.producer).2.2.1
  obtain ⟨prior,printed⟩ := GeneralDeclarativeWitnessCompletion351.reports_complete earlier
  refine ⟨prior,printed,(GeneralDeclarativeWitnessMixedWhole352.agreed a.consumer).2.1,?_⟩
  intro m fit
  exact ⟨(GeneralDeclarativeWitnessRecordWhole350.selected a.prior.producer printed m fit).1,
    GeneralDeclarativeWitnessMixedWhole352.selected a.consumer selected m fit⟩

end Yulang.GeneralDeclarativeWitnessMixedRelease352
