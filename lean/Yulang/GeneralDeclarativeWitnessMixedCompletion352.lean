import Yulang.GeneralDeclarativeWitnessMixedRelease352

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMixedCompletion352
open GeneralDeclarativeHead320 (Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessMixedForest352 (Problem Global Rule)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open CommonRoleOutermostResolver (Classify Resolves All₂ Tree Result Dictionary classification classifications
  classification_exact classifications_exact)

section
variable {p : Problem} {g : Global p} {sidecar}

mutual
theorem selected_tree (d : Demand) (t : Tree) (hit : Resolves (Rule g sidecar) d t) :
    ∃ dictionary, classification t = .selected dictionary := by
  cases hit with
  | pending h => cases h with | record h => cases h
  | ambiguous h => cases h with | record h => cases h
  | rejected h => cases h with | record h => cases h
  | selected h child =>
    obtain ⟨dicts,found⟩ := selected_forest _ _ child
    exact ⟨.node _ dicts, (classification_exact ..).mpr
      (.selected ((classifications_exact ..).mp found) (.selected rfl))⟩
termination_by sizeOf t

theorem selected_forest (ds : List Demand) (trees : List Tree)
    (hit : All₂ (Resolves (Rule g sidecar)) ds trees) :
    ∃ dicts : List Dictionary, classifications trees = dicts.map Result.selected := by
  cases hit with
  | nil => exact ⟨[],rfl⟩
  | cons h t =>
    obtain ⟨first,f⟩ := selected_tree _ _ h
    obtain ⟨last,l⟩ := selected_forest _ _ t
    exact ⟨first::last,by simp only [classifications,f,l,List.map_cons]⟩
termination_by sizeOf trees
end

theorem no_positive_pending (known : Classify (Rule g sidecar) d printed) :
    ∃ dictionary, printed = .selected dictionary := by
  obtain ⟨tree,checked,report⟩ := known
  obtain ⟨dict,accepted⟩ := selected_tree _ _ checked
  exact ⟨dict,((classification_exact ..).mpr report).symm.trans accepted⟩
end

theorem common_model {p : GeneralDeclarativeWitnessMixedRelease352.Problem} {active}
    {w : GeneralDeclarativeWitnessMixedRelease352.Wire} {report : Report}
    (checked : GeneralDeclarativeWitnessMixedRelease352.check p active w report = true) :
    ∃ (a : GeneralDeclarativeWitnessMixedRelease352.Accepted p active w report) (producer consumer : Dictionary),
      w.priorReport.result = .selected producer ∧ report.result = .selected consumer ∧
      report.outputs = p.root.outputs ∧
      ∀ m : Assignment, Models p.publisher.roles.current m →
        Evidence (registry a.prior.producer.global.table)
          (interpretation a.prior.producer.global.table.snapshot) m p.publisher.root producer ∧
        Evidence (registry a.consumer.global.table)
          (interpretation a.consumer.global.table.snapshot) m p.root consumer ∧
        ∀ f ∈ a.consumer.diagnostic.fixed, f.equations.map Equation.left =
          f.demand.outputs.map GeneralSourceState.Output.target ∧
          ∀ e ∈ f.equations, GeneralDeclarativeEntailment320.Holds m e := by
  obtain ⟨a⟩ := GeneralDeclarativeWitnessMixedRelease352.checked checked
  obtain ⟨consumer,selected⟩ := no_positive_pending (GeneralDeclarativeWitnessMixedWhole352.agreed a.consumer).2.2.1
  obtain ⟨producer,prior,out,both⟩ := GeneralDeclarativeWitnessMixedRelease352.two_reports a consumer selected
  exact ⟨a,producer,consumer,prior,selected,out,both⟩

end Yulang.GeneralDeclarativeWitnessMixedCompletion352
