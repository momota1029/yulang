import Yulang.GeneralDictionaryFeedbackEvidence
import Yulang.GeneralNominalFeedbackRegressions

/-! A non-vacuous source-formed regression: the recorded parent's original
source instance survives a journal-certified refresh, while its cyclic child
is rejected. The parent instance is not a completed recursive dictionary. -/
namespace Yulang.GeneralDictionaryFeedbackEvidenceExamples

open GeneralNominalFeedbackObstruction
open GeneralNominalFeedbackRefresh (refreshed)
open GeneralNominalSaturationState GeneralDictionaryFeedbackEvidence

private theorem formed : GeneralNominalFeedbackSteps.SourceFormed registry root refreshed :=
  .update GeneralNominalFeedbackRegressions.formed GeneralNominalFeedbackRefresh.refresh_step

private theorem recorded : packet ∈ refreshed.packets := by
  simp [GeneralNominalFeedbackRefresh.refreshed,regenerate,installed,GeneralNominalFeedbackSites.install]

theorem refreshed_source_instance (m : GeneralNominalCommonBridge.Assignment)
    (valid : Models refreshed m) :
    GeneralDictionaryRecursiveEvidence.Instance registry context m root 2 [child] := by
  have source := (sourceFormed_recorded_instances registry root refreshed formed packet recorded).1 m valid
  change GeneralDictionaryRecursiveEvidence.Instance registry context m root 2 packet.children at source
  rw [children_exact] at source
  exact source

theorem refreshed_child_generated : Generated refreshed root child := by
  have source := (sourceFormed_recorded_instances registry root refreshed formed packet recorded).2 child
    (by rw [children_exact]; simp)
  exact source

/-- The evidence result is not vacuous: the refreshed journal has a model,
and the generated child is independently rejected by the actual K2 local rule. -/
theorem nonvacuous_refresh :
    Models refreshed model ∧
    GeneralDictionaryRecursiveEvidence.Instance registry context model root 2 [child] ∧
    Generated refreshed root child ∧
    GeneralNominalFeedbackK2.Local registry refreshed child .rejected := by
  have valid := (GeneralNominalFeedbackRefresh.refresh_models model).mpr installed_models
  exact ⟨valid,refreshed_source_instance model valid,refreshed_child_generated,
    GeneralNominalFeedbackRefresh.child_rejected⟩

end Yulang.GeneralDictionaryFeedbackEvidenceExamples
