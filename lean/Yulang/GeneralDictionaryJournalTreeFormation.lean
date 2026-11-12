import Yulang.GeneralDictionaryJournalTreeExamples
/-! The positive terminal-output installation starts from genuine InitialSource
and follows the unchanged feedback source-formation relation. -/
namespace Yulang.GeneralDictionaryJournalTreeFormation
open GeneralDictionaryRecursiveObstruction
open GeneralDictionaryJournalTreeExamples
open GeneralNominalSaturationState

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root := by
  refine ⟨rfl,metadata,linked,?_,?_,rfl⟩
  · intro model valid index
    exact CommonNominalFullCarrier.subtype_refl _
  · intro source member
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h <;> simp [h]

theorem formed_before : GeneralNominalFeedbackSteps.SourceFormed registry root
    GeneralDictionaryCommittedEvidenceExamples.before := .initial context initial_source

theorem formed_after : GeneralNominalFeedbackSteps.SourceFormed registry root after :=
  .update formed_before feedback_step

/-- Genuine source reachability, inhabited successor, and exclusion of the
associated-output countermodel hold together. Stability is not asserted. -/
theorem reachable_positive :
    GeneralNominalFeedbackSteps.SourceFormed registry root after ∧
    Models after GeneralNominalExamples.model ∧ ¬ Models after badModel :=
  ⟨formed_after,good_after,bad_excluded⟩
end Yulang.GeneralDictionaryJournalTreeFormation
