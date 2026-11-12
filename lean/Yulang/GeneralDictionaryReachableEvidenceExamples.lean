import Yulang.GeneralDictionaryReachableEvidenceInitial
import Yulang.GeneralDictionaryCycleEvidenceExamples

/-! The initial feedback-stability premise is inhabited. This regression does
not prove the feedback selected classifier for the cyclic-wrapper example;
that classifier has stronger journal K2 guards than the older cycle classifier. -/
namespace Yulang.GeneralDictionaryReachableEvidenceExamples
open GeneralDictionaryCycleEvidenceExamples
open GeneralNominalRecursiveExamples (lenRegistry lenRoot)
open GeneralNominalCycleWrapper (context model)
open GeneralNominalSaturationState

theorem feedback_stable : GeneralNominalFeedbackSteps.Stable lenRegistry journal lenRoot :=
  GeneralDictionaryReachableEvidenceInitial.initial_feedback_stable lenRegistry context lenRoot stable

/-- A real model and source-backed terminal evidence coexist with initial
feedback stability; no new axiom or modeled-evidence premise is assumed. -/
theorem inhabited_stable :
    GeneralNominalFeedbackSteps.Stable lenRegistry journal lenRoot ∧
    Models journal model ∧
    GeneralDictionaryRecursiveEvidence.Evidence lenRegistry context model lenRoot (.node 30 []) :=
  ⟨feedback_stable,journal_model,evidence model journal_model⟩

end Yulang.GeneralDictionaryReachableEvidenceExamples
