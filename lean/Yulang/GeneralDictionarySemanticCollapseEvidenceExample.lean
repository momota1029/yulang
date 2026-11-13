import Yulang.GeneralDictionarySemanticCollapseBranchExample
import Yulang.GeneralDictionaryRecursiveEvidenceFacts

/-! Model-indexed Evidence is inhabited before and after an actual improving
revision. This does not assert evidence for all models of either raw source. -/
namespace Yulang.GeneralDictionarySemanticCollapseEvidenceExample
open GeneralDictionarySemanticCollapseBranchExample
open GeneralDictionarySemanticCollapseExample (root model)
open GeneralDictionaryRecursiveEvidence
open GeneralNominalRecursiveCandidates

theorem old_instance : Instance registry context model root declaration.id [] := by
 refine ⟨declaration,by simp,checked,rfl,rfl,bounds,located,?_,?_,?_,prepared.1,old_branch⟩
 · rw [report_exact]; exact ⟨rfl,rfl,rfl⟩
 · constructor
   · intro output member; cases member
   · rw [generated_empty]
 · exact (children_empty _ _).symm

theorem current_instance : Instance registry currentContext model root declaration.id [] := by
 refine ⟨declaration,by simp,checked,rfl,rfl,bounds,current_located,?_,?_,?_,current_prepared.1,current_branch⟩
 · rw [current_report]; exact ⟨rfl,rfl,rfl⟩
 · constructor
   · intro output member; cases member
   · rw [current_generated_empty]
 · exact (children_empty _ _).symm

theorem old_evidence : Evidence registry context model root (.node declaration.id []) :=
 evidence_node registry context model root declaration.id [] [] old_instance .nil

theorem current_evidence : Evidence registry currentContext model root (.node declaration.id []) :=
 evidence_node registry currentContext model root declaration.id [] [] current_instance .nil

theorem reachable_evidence :
 GeneralNominalValueSteps.SourceFormed registry root GeneralDictionarySemanticCollapseExample.revisedTracked ∧
 GeneralNominalSaturationState.Models GeneralDictionarySemanticCollapseExample.revisedTracked.current model ∧
 Evidence registry context model root (.node declaration.id []) ∧
 Evidence registry currentContext model root (.node declaration.id []) :=
 ⟨source_formed,GeneralDictionarySemanticCollapseExample.result_models,old_evidence,current_evidence⟩

end Yulang.GeneralDictionarySemanticCollapseEvidenceExample
