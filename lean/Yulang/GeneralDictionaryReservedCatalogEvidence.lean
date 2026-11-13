import Yulang.GeneralDictionaryReservedCollectedHistory
import Yulang.GeneralDictionaryCatalogEvidence

/-! The actual refreshed reserved-output example uses the catalog reconstructed
from its reachable journal, not a supplied provenance or collection witness. -/
namespace Yulang.GeneralDictionaryReservedCatalogEvidence
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration checked interpretation)
open GeneralDictionaryReservedNominalRefresh (refreshed refreshed_reachable refreshed_inhabited)
open GeneralDictionaryReservedRefreshedEvidence (current shape metadata requests_exact)
open GeneralDictionaryReservedCollectedHistory (installed_closed installed_requests)
open GeneralDictionaryReachableRequestHistory
open GeneralDictionaryRecursiveEvidence GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

theorem catalog_exact : safeCatalog refreshed = [request] := by
  change ([packet] : List (GeneralNominalSaturationState.Packet GeneralDeclarationExamples.roles)).reverse.flatMap eligible = [request]
  simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [eligible_closed packet installed_closed]
  exact installed_requests

theorem automatic_history :
    GeneralDictionaryCollectedRequests.Collected registry root refreshed [request] := by
  have h := safe_history refreshed_reachable
  rw [catalog_exact] at h
  exact h

theorem current_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models refreshed.current assignment) :
    Instance registry current assignment root declaration.id [] := by
  have supported := GeneralDictionaryCollectedRequests.supported_subset
    (safe_history refreshed_reachable)
    (GeneralNominalMaterialization.requests current.state registry root declaration checked
      (bindings current.state (report current declaration [(shape.slot,shape.slot)])))
    (by
      rw [requests_exact,catalog_exact]
      exact fun _ member => member)
  have result := GeneralDictionaryProvenanceScalarBranch.instance_of_shape registry root root refreshed
    refreshed_reachable declaration (by simp) checked shape supported GeneralDictionaryReservedRefreshedEvidence.metadata assignment valid
  have empty := GeneralDictionaryLinearLeaf.children_empty current registry root declaration checked rfl
    (bindings current.state (report current declaration [(shape.slot,shape.slot)]))
  simpa only [empty] using result

theorem current_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models refreshed.current assignment) :
    Evidence registry current assignment root (.node declaration.id []) :=
  evidence_node registry current assignment root declaration.id [] [] (current_instance assignment valid) .nil

theorem no_initial_output_observation_needed :
    (¬ GeneralDictionaryObservedFiniteRequests.Observed state interpretation [request]) ∧
    safeCatalog refreshed = [request] ∧
    GeneralNominalSaturationState.Models refreshed.current positive ∧
    Evidence registry current positive root (.node declaration.id []) :=
  ⟨not_observed,catalog_exact,refreshed_inhabited,current_evidence positive refreshed_inhabited⟩
end Yulang.GeneralDictionaryReservedCatalogEvidence
