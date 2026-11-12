import Yulang.GeneralDictionaryOutputMergeRefreshClosure
import Yulang.GeneralDictionaryOutputMergeStabilityResidual

/-! A genuinely Stable, inhabited, reachable three-node dictionary with an
actual associated-output merge. This is one fixture, not general V5 bridges. -/
namespace Yulang.GeneralDictionaryOutputMergeStable
open GeneralDictionaryOutputMergeRefresh GeneralDictionaryOutputMergeSuccess
open GeneralDictionaryOutputMergeStabilityResidual
open GeneralNominalExamples (displayRoot model)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState

/-- The four constrained source identities are already Known; every other
identity varies between incompatible scalar models and cannot become Known
under an exact refresh. This does not assume every source is Known. -/
theorem refresh_closed : RefreshClosed := by
  intro context certificate source _ unknown
  by_cases zero : source = 0
  · subst source
    exact False.elim (unknown ⟨(0 : Fin 4),rfl,Or.inr ⟨descriptor,rfl⟩⟩)
  by_cases one : source = 1
  · subst source
    exact False.elim (unknown ⟨(1 : Fin 4),rfl,Or.inl (by decide +kernel)⟩)
  by_cases first : source = outputTarget 10
  · subst source
    exact False.elim (unknown output_known)
  by_cases last : source = outputTarget 11
  · subst source
    exact False.elim (unknown output_known11)
  exact GeneralDictionaryOutputMergeRefreshClosure.refresh_other_unknown
    context certificate source zero one first last

theorem stable : GeneralNominalSupportSteps.Stable registry refreshed displayRoot :=
  stable_of_refresh_closed refresh_closed

/-- The fixed actual endpoint is reachable, inhabited, Stable, genuinely
classified and has full recursive Evidence for EVERY journal model. -/
theorem stable_classified_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot refreshed ∧
    Models refreshed.current model ∧
    GeneralNominalSupportSteps.Stable registry refreshed displayRoot ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry refreshed displayRoot
      (.selected GeneralDictionaryOutputMergeRootEvidence.rootPayload) ∧
    ∀ m, Models refreshed.current m →
      GeneralDictionaryRecursiveEvidence.Evidence registry refreshed.current.context m displayRoot
        GeneralDictionaryOutputMergeRootEvidence.rootPayload :=
  ⟨GeneralDictionaryOutputMergeRefresh.reachable,inhabited,stable,
    GeneralDictionaryOutputMergeRefreshClassification.classified,
    GeneralDictionaryOutputMergeRefreshEvidence.full_dictionary⟩
end Yulang.GeneralDictionaryOutputMergeStable
