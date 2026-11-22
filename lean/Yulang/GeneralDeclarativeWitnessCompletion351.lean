import Yulang.GeneralDeclarativeWitnessReleaseExact351
import Yulang.GeneralDeclarativeWitnessAuthModel351

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCompletion351
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralDeclarativeWitnessIdentity351 (Stamp Owned)
open GeneralDeclarativeWitnessAuthForest351 (Problem)
open GeneralDeclarativeWitnessAuthWhole351 (Wire Accepted)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeWitnessTree349 (Report exact_report)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify Resolves All₂ Tree Result Dictionary classification classifications
  classification_exact classifications_exact)

section
variable {s : State} {p : Supported s done}
variable {r i w sidecar}

mutual
/-- The scoped C340 positive rules cannot witness a pending producer.
Completion is proved from the independent tree, not a release bit. -/
theorem positive_tree (d : Demand) (tree : Tree)
    (hit : Resolves (GeneralDeclarativeTaggedDictionary340.Rule p sidecar r i w) d tree) :
    ∃ dictionary, classification tree = .selected dictionary := by
  cases hit with
  | pending h => cases h
  | ambiguous h => cases h
  | rejected h => cases h
  | selected h child =>
    obtain ⟨dicts,found⟩ := positive_forest _ _ child
    exact ⟨.node _ dicts, (classification_exact ..).mpr
      (.selected ((classifications_exact ..).mp found) (.selected rfl))⟩
termination_by sizeOf tree

theorem positive_forest (ds : List Demand) (trees : List Tree)
    (hit : All₂ (Resolves (GeneralDeclarativeTaggedDictionary340.Rule p sidecar r i w)) ds trees) :
    ∃ dicts : List Dictionary, classifications trees = dicts.map Result.selected := by
  cases hit with
  | nil => exact ⟨[],rfl⟩
  | cons one rest =>
    obtain ⟨head,first⟩ := positive_tree _ _ one
    obtain ⟨tail,last⟩ := positive_forest _ _ rest
    exact ⟨head::tail,by simp only [classifications,first,last,List.map_cons]⟩
termination_by sizeOf trees
end

theorem reports_complete
    (known : Classify (GeneralDeclarativeTaggedDictionary340.Rule p sidecar r i w) d outcome) :
    ∃ dictionary, outcome = .selected dictionary := by
  obtain ⟨tree,proof,agrees⟩ := known
  obtain ⟨found,printed⟩ := positive_tree _ _ proof
  exact ⟨found,((classification_exact ..).mpr agrees).symm.trans printed⟩
end

/-- Both independent accepted reports actually contain successful
dictionaries. The same fixed model validates both and all consumer
writes; no truth about an anonymous completed runtime is assumed. -/
theorem both {active : List Stamp} {p : Problem} {wire : Wire} {report : Report}
    (ok : GeneralDeclarativeWitnessFreshness351.check active p wire report = true) :
    ∃ (a : Accepted p wire report) (producer consumer : Dictionary),
      wire.priorReport.result = .selected producer ∧ report.result = .selected consumer ∧
      report.outputs = p.target.outputs ∧
      ∀ m : Assignment, Models p.current m →
        Evidence (registry a.writer.producer.global.table)
          (interpretation a.writer.producer.global.table.snapshot) m p.writer.root producer ∧
        Evidence (registry a.env.bundle) (interpretation a.env.bundle.snapshot) m p.target consumer ∧
        (∀ f ∈ a.diagnostic.fixed, f.equations.map Equation.left = f.demand.outputs.map Output.target ∧
          ∀ e ∈ f.equations, GeneralDeclarativeEntailment320.Holds m e) := by
  obtain ⟨_,a,_,_⟩ := GeneralDeclarativeWitnessFreshness351.sound ok
  have earlier := (GeneralDeclarativeWitnessRecordWhole350.agreed a.writer.producer).2.2.1
  have later := (GeneralDeclarativeWitnessAuthWhole351.exact_result a).2.2.1
  obtain ⟨producer,priorResult⟩ := reports_complete earlier
  obtain ⟨consumer,finalResult⟩ := reports_complete later
  refine ⟨a,producer,consumer,priorResult,finalResult,
    (GeneralDeclarativeWitnessAuthWhole351.exact_result a).2.1,?_⟩
  intro m fit
  exact ⟨GeneralDeclarativeWitnessAuthWhole351.producer_same_model a priorResult m fit,
    GeneralDeclarativeWitnessAuthWhole351.selected a finalResult m fit⟩

end Yulang.GeneralDeclarativeWitnessCompletion351
