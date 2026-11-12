import Yulang.GeneralDictionaryOutputMergeSuccess

/-! The complete recursive root dictionary on the same inhabited reachable
nonempty-output merge fixture. Ordered child multiplicity is preserved: the
two distinct source occurrences have identical terminal runtime payloads.
This remains one-model source evidence, not Stable or general V5 completeness. -/
namespace Yulang.GeneralDictionaryOutputMergeRootEvidence
open GeneralDictionaryOutputMergeSuccess
open GeneralNominalExamples (context model displayRoot)
open GeneralNominalSupportSteps GeneralNominalSaturationState
open GeneralDictionaryRecursiveEvidence
open GeneralDictionaryReadback (Payload)

abbrev rootPayload : Payload := .node 1 [.node 7 [],.node 7 []]

theorem parent_instance :
    Instance registry (context true) model displayRoot 1 [child 10,child 11] := by
  have instanceRule := survivor_instance_of_branch registry registry_checked
    (context true) model displayRoot 1 children survivor declaration (by simp)
    checked rfl [(0,0)] rfl branch
  simpa only [children_exact] using instanceRule

theorem current_parent_instance :
    Instance registry current model displayRoot 1 [child 10,child 11] :=
  GeneralDictionaryOrdinaryTrace.instance_extension registry (context true) current
    final_extension model finish_model.1 displayRoot 1 [child 10,child 11] parent_instance

theorem root_evidence : Evidence registry current model displayRoot rootPayload :=
  evidence_node registry current model displayRoot 1 [child 10,child 11]
    [.node 7 [],.node 7 []] current_parent_instance
    (.cons (merged_child_evidence 10) (.cons (merged_child_evidence 11) .nil))

/-- Full root evidence, reachable state, common model and both named-output
equations coexist. No dictionary occurrence is removed because its payload
equals that of its sibling. -/
theorem reachable_full_dictionary :
    SourceFormed registry displayRoot finish ∧
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles)
      registry displayRoot finish ∧
    Models finish.current model ∧
    Evidence registry current model displayRoot rootPayload ∧
    GeneralNominalJointCandidates.Joint registry finish.current (child 10) 7 ∧
    outputTarget 10 ≠ outputTarget 11 ∧
    GeneralNominalDemandMerging.outputAtoms (site 10) (site 11) ≠ [] := by
  refine ⟨finish_sourceformed,reachable,finish_model,root_evidence,
    merged_child_joint,output_targets_distinct,?_⟩
  rw [output_atoms_exact]
  simp

end Yulang.GeneralDictionaryOutputMergeRootEvidence
