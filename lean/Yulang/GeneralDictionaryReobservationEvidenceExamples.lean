import Yulang.GeneralDictionaryReobservationEvidence
import Yulang.GeneralNominalReobservationBoundaryExamples

/-! The repaired, genuine descriptor-changing fork now has the exact runtime
payload in every final model, not merely an equal diagnostic tree. -/
namespace Yulang.GeneralDictionaryReobservationEvidenceExamples
open GeneralNominalRefreshFork GeneralNominalReobservationExamples
open GeneralNominalReobservationBoundaryExamples
open GeneralDeclarationExamples (roles)

theorem repaired_evidence (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models (after false) model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (after false).context model
      root (.node 90 []) := by
  apply (GeneralDictionaryReobservationEvidence.reachable_packetFree_terminal
    registry root root (after false) reachable_point rfl (Or.inl rfl)
    90 [] point_stable ?_).2 model valid
  exact (GeneralNominalFeedbackBoundary.local_correspondence roles
    (GeneralDictionaryFeedbackEvidence.evidence roles) registry (after false) root _).mp
      GeneralNominalRefreshDivergence.point_local

theorem actual_repair_with_evidence :
    GeneralNominalReobservationSteps.Step registry root (after true) (after false) ∧
    (∀ next, ¬ GeneralNominalReobservationSteps.Step registry root (after false) next) ∧
    ∀ model, GeneralNominalSaturationState.Models (after false) model →
      GeneralDictionaryRecursiveEvidence.Evidence registry (after false).context model
        root (.node 90 []) :=
  ⟨repair_step,point_halted,repaired_evidence⟩
end Yulang.GeneralDictionaryReobservationEvidenceExamples
