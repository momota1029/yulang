import Yulang.GeneralDictionaryOrdinaryTrace
import Yulang.GeneralDictionaryCommittedEvidenceExamples
import Yulang.GeneralNominalFeedbackRegressions

/-! Nonvacuous final-context checks. The terminal associated-output journal
characterizes exactly its current-context dictionary evidence. The nonterminal
feedback installation supplies a current-context parent instance, not a complete
parent dictionary when the generated child is rejected. -/
namespace Yulang.GeneralDictionaryOrdinaryTransportExamples
open GeneralDictionaryOrdinaryTrace
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState

namespace Terminal
open GeneralDictionaryRecursiveObstruction
open GeneralDictionaryCommittedEvidenceExamples

theorem current_evidence (model : Assignment) (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.context model root (.node 40 []) :=
  evidence_extension registry context after.context (packet_extension packet) model valid.1 root _
    (installed_evidence model valid)

/-- Exact nonvacuous successor model class, with the original payload unchanged. -/
theorem current_evidence_iff (model : Assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.context model root (.node 40 []) ↔
      Models after model := by
  constructor
  · intro evidence
    have original := evidence_extension_backward registry context after.context (packet_extension packet)
      model root _ evidence
    exact (installed_models model).mpr ((evidence_iff_output model).mp original)
  · exact current_evidence model

theorem nonvacuous_current_evidence :
    Models after GeneralNominalExamples.model ∧
      GeneralDictionaryRecursiveEvidence.Evidence registry after.context GeneralNominalExamples.model
        root (.node 40 []) :=
  ⟨good_installed_model,current_evidence _ good_installed_model⟩

theorem bad_current_no_evidence :
    ¬ GeneralDictionaryRecursiveEvidence.Evidence registry after.context badModel root (.node 40 []) :=
  fun evidence => bad_not_installed_model ((current_evidence_iff badModel).mp evidence)
end Terminal

namespace Feedback
open GeneralNominalFeedbackObstruction

theorem current_parent_instance (assignment : Assignment) (valid : Models installed assignment) :
    GeneralDictionaryRecursiveEvidence.Instance registry installed.context assignment root 2 [child] := by
  have source := installed_trace_current_instance registry root initialState installed packet
    GeneralNominalFeedbackRegressions.enabled .refl assignment valid
  change GeneralDictionaryRecursiveEvidence.Instance registry installed.context assignment root 2 packet.children at source
  rw [children_exact] at source
  exact source

/-- This current-context instance has an actual model and a real installed edge. -/
theorem nonvacuous_current_parent :
    Models installed model ∧
      GeneralDictionaryRecursiveEvidence.Instance registry installed.context model root 2 [child] ∧
      Generated installed root child := by
  refine ⟨installed_models,current_parent_instance model installed_models,?_⟩
  exact GeneralNominalFeedbackSteps.installed_children initialState packet child (by rw [children_exact]; simp)
end Feedback

end Yulang.GeneralDictionaryOrdinaryTransportExamples
