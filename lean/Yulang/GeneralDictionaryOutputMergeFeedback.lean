import Yulang.GeneralDictionaryOutputMergeClassification
import Yulang.GeneralDictionaryOutputMergeRawModel

/-! A journal-entailing equality can remain absent from the raw ordinary context.
The administrative feedback step keeps the complete journal model set and source
dictionary evidence. A separately constructed raw countermodel discharges
novelty; the successful classifier alone is not a saturation certificate. -/
namespace Yulang.GeneralDictionaryOutputMergeFeedback
open GeneralDictionaryOutputMergeSuccess
open GeneralNominalExamples (displayRoot)
open GeneralNominalSaturationState GeneralNominalSupportSteps
open GeneralNominalCommonBridge (Assignment)

theorem source_int (m : Assignment) (valid : Models finish.current m) :
    CommonNominalFullCarrier.Equivalent (m 1).1 (.base .int) :=
  (GeneralDictionaryOutputMergeAllModels.source_valid m valid).1.2.1 1 (.base .int) rfl

theorem journal_equal : GeneralNominalFeedbackK2.Equal finish.current (outputTarget 10) 1 := by
  intro m valid
  have output := GeneralDictionaryOutputMergeAllModels.output_scalar m valid 10 (Or.inl rfl)
  have source := source_int m valid
  exact ⟨CommonNominalFullCarrier.subtype_trans output.1 source.2,
    CommonNominalFullCarrier.subtype_trans source.1 output.2⟩

noncomputable abbrev next : GeneralNominalSupport.Tracked GeneralDeclarationExamples.roles :=
  {finish with current := GeneralNominalFeedbackSteps.equate finish.current (outputTarget 10) 1}

theorem actual_step_of_novel
    (novel : ¬ GeneralNominalFeedbackSteps.RawEqual finish.current (outputTarget 10) 1) :
    Step registry displayRoot finish next := by
  refine ⟨displayRoot,.root,.administrative displayRoot next.current (.equate displayRoot (outputTarget 10) 1 ?_ ?_ journal_equal novel)⟩
  · exact (child_linked 10 (Or.inl rfl)).2 ⟨0,outputTarget 10⟩ (List.mem_singleton_self _)
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(1 : Fin 2),rfl⟩)))

theorem next_models (m : Assignment) : Models next.current m ↔ Models finish.current m :=
  GeneralNominalFeedbackSteps.equate_models finish.current (outputTarget 10) 1 journal_equal m

theorem next_evidence (m : Assignment) (valid : Models next.current m) :
    GeneralDictionaryRecursiveEvidence.Evidence registry next.current.context m displayRoot
      GeneralDictionaryOutputMergeRootEvidence.rootPayload :=
  GeneralDictionaryOrdinaryTrace.evidence_extension registry current next.current.context
    (GeneralDictionaryOrdinaryTrace.equate_extension finish.current (outputTarget 10) 1)
    m valid.1 displayRoot GeneralDictionaryOutputMergeRootEvidence.rootPayload
    (GeneralDictionaryOutputMergeAllModels.full_dictionary m ((next_models m).mp valid))

theorem next_reachable_of_novel
    (novel : ¬ GeneralNominalFeedbackSteps.RawEqual finish.current (outputTarget 10) 1) :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles)
      registry displayRoot next := by
  obtain ⟨initial,source,path⟩ := reachable
  exact ⟨initial,source,.tail path (actual_step_of_novel novel)⟩

theorem not_stable_of_novel
    (novel : ¬ GeneralNominalFeedbackSteps.RawEqual finish.current (outputTarget 10) 1) :
    ¬ Stable registry finish displayRoot := by
  intro stable
  obtain ⟨focus,generated,action⟩ := actual_step_of_novel novel
  exact stable focus generated next action

theorem next_sourceformed_of_novel
    (novel : ¬ GeneralNominalFeedbackSteps.RawEqual finish.current (outputTarget 10) 1) :
    SourceFormed registry displayRoot next :=
  .update finish_sourceformed (actual_step_of_novel novel)

theorem next_inhabited : Models next.current GeneralNominalExamples.model :=
  (next_models _).mpr finish_model

theorem actual_step : Step registry displayRoot finish next :=
  actual_step_of_novel GeneralDictionaryOutputMergeRawModel.not_raw_equal

theorem not_stable : ¬ Stable registry finish displayRoot :=
  not_stable_of_novel GeneralDictionaryOutputMergeRawModel.not_raw_equal

theorem next_sourceformed : SourceFormed registry displayRoot next :=
  next_sourceformed_of_novel GeneralDictionaryOutputMergeRawModel.not_raw_equal

theorem next_reachable :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles)
      registry displayRoot next :=
  next_reachable_of_novel GeneralDictionaryOutputMergeRawModel.not_raw_equal

/-- Concrete separation: successful whole-root classification and source
semantics do not imply saturation. An actual equality-feedback transition is
still enabled, preserves every journal model, and preserves full Evidence. -/
theorem classified_but_not_saturated :
    B4TargetV3.Classify
      (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles).toSourceBoundary
      registry finish displayRoot (.selected GeneralDictionaryOutputMergeRootEvidence.rootPayload) ∧
    ¬ Stable registry finish displayRoot ∧
    Step registry displayRoot finish next ∧
    SourceFormed registry displayRoot next ∧
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles)
      registry displayRoot next ∧
    Models next.current GeneralNominalExamples.model ∧
    (∀ m, Models next.current m ↔ Models finish.current m) ∧
    ∀ m, Models next.current m →
      GeneralDictionaryRecursiveEvidence.Evidence registry next.current.context m displayRoot
        GeneralDictionaryOutputMergeRootEvidence.rootPayload :=
  ⟨GeneralDictionaryOutputMergeClassification.classified,not_stable,actual_step,
    next_sourceformed,next_reachable,next_inhabited,next_models,next_evidence⟩

end Yulang.GeneralDictionaryOutputMergeFeedback
