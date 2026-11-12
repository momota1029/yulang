import Yulang.GeneralDictionarySourceChoiceVisibility
import Yulang.GeneralDictionaryModeledJointGap

/-! Source formation excludes the invisible stale-key obstruction of cycle 138.
These invariants are for the unchanged full feedback relation, including arbitrary
certified refreshes. They do not establish a shared model for all alias branches. -/
namespace Yulang.GeneralDictionaryReachableEvidenceProvenance

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalFeedbackSteps

/-- Cycle 138's inhabited, stable raw journal cannot arise by SourceFormed. -/
theorem modeled_raw_gap_not_sourceFormed :
    ¬ SourceFormed GeneralNominalRecursiveExamples.lenRegistry
      GeneralDictionaryModeledJointGap.root GeneralDictionaryModeledJointGap.journal := by
  intro formed
  have visible := GeneralDictionarySourceChoiceVisibility.visible _ _ _ formed
    GeneralDictionaryModeledJointGap.packet (List.mem_singleton_self _)
  have same := congrArg Declaration.id (List.mem_singleton.mp visible)
  cases same

/-- Actual provenance and a genuine journal model do not make every raw-context
model a journal model. Thus source formation alone cannot upgrade the existential
raw BranchModels witness supplied by selection. Stability is not asserted. -/
theorem formed_inhabited_context_incomplete :
    SourceFormed GeneralNominalFeedbackObstruction.registry
      GeneralNominalFeedbackObstruction.root GeneralNominalFeedbackObstruction.installed ∧
    Models GeneralNominalFeedbackObstruction.installed GeneralNominalFeedbackObstruction.model ∧
    ¬ ContextComplete GeneralNominalFeedbackObstruction.installed := by
  refine ⟨GeneralNominalFeedbackRegressions.formed,
    GeneralNominalFeedbackObstruction.installed_models,?_⟩
  intro complete
  have valid := complete GeneralNominalFeedbackObstruction.finiteModel
    GeneralNominalFeedbackObstruction.finite_private_models
  exact GeneralNominalFeedbackObstruction.finite_not_packet
    (valid.2.1 GeneralNominalFeedbackObstruction.packet (by
      simp [GeneralNominalFeedbackObstruction.installed,GeneralNominalFeedbackSites.install]))

end Yulang.GeneralDictionaryReachableEvidenceProvenance
