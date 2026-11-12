import Yulang.GeneralDictionaryReachableBoundary
import Yulang.GeneralDictionaryReachableEvidenceProvenance

/-! A real reachable, inhabited state need not identify raw-context models
with journal models. Initial/reachability is not a magic completeness premise.
This is not a counterexample to the stable-selected V5 evidence obligation. -/
namespace Yulang.GeneralDictionaryReachableModelGap
open GeneralDictionaryReachableBoundary
open GeneralNominalFeedbackObstruction
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState

theorem reachable_inhabited_context_incomplete :
    B4TargetV5.Reachable (boundary roles) registry root installed ∧
    Models installed model ∧ ¬ ContextComplete installed := by
  obtain ⟨formed,valid,incomplete⟩ :=
    GeneralDictionaryReachableEvidenceProvenance.formed_inhabited_context_incomplete
  exact ⟨(reachable_iff_sourceFormed _ _ _).mpr formed,valid,incomplete⟩

/-- Disproves only a tempting proof shortcut, not the B4 target. -/
theorem no_reachable_context_complete :
    ¬ (∀ (state : State roles), B4TargetV5.Reachable (boundary roles) registry root state →
      (∃ model, Models state model) → ContextComplete state) := by
  intro shortcut
  exact reachable_inhabited_context_incomplete.2.2
    (shortcut installed reachable_inhabited_context_incomplete.1 ⟨model,installed_models⟩)
end Yulang.GeneralDictionaryReachableModelGap
