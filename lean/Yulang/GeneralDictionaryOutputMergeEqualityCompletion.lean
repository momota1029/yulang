import Yulang.GeneralDictionaryEqualityStepBound
import Yulang.GeneralDictionaryOutputMergeRefreshEvidence

/-! Nonvacuous reachable application of the general bounded equality subphase.
The endpoint is existential and equality-complete, not asserted Stable. -/
namespace Yulang.GeneralDictionaryOutputMergeEqualityCompletion
open GeneralNominalSaturationState GeneralDictionaryEqualityStepBound
open GeneralDictionaryOutputMergeSuccess
open GeneralDictionaryOutputMergeRefresh
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (displayRoot)

/-- One reachable nonempty-model endpoint completes all finite source
equalities, keeps every Joint observation, and retains full root Evidence
for every final model in its actual final context. -/
theorem reachable_bounded_dictionary :
    ∃ after n,
      Counted registry displayRoot n refreshed after ∧
      n ≤ (GeneralNominalState.sources refreshed.current.context.state).length ^ 2 ∧
      B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot after ∧
      Models after.current GeneralNominalExamples.model ∧
      GeneralDictionaryFiniteEqualityCompletion.EqualityComplete after.current ∧
      (∀ focus : GeneralSourceDictionaries.Occurrence roles, ∀ key,
        GeneralNominalJointCandidates.Joint registry after.current focus key ↔
        GeneralNominalJointCandidates.Joint registry refreshed.current focus key) ∧
      (∀ model, Models after.current model →
        GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model displayRoot
          GeneralDictionaryOutputMergeRootEvidence.rootPayload) := by
  obtain ⟨after,n,path,bound,cert,done⟩ := complete_sources_quadratic registry displayRoot refreshed
  have reached : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot after := by
    have steps := path.steps
    have start := GeneralDictionaryOutputMergeRefresh.reachable
    clear path bound cert done
    induction steps with
    | refl => exact start
    | tail _ step ih =>
      obtain ⟨initial,started,prior⟩ := ih
      exact ⟨initial,started,.tail prior step⟩
  refine ⟨after,n,path,bound,reached,(cert.models _).mpr inhabited,done,
    fun focus key => cert.joint registry focus key,?_⟩
  intro model valid
  have old := (cert.models model).mp valid
  exact (cert.evidence registry model old displayRoot _).mpr
    (GeneralDictionaryOutputMergeRefreshEvidence.full_dictionary model old)

end Yulang.GeneralDictionaryOutputMergeEqualityCompletion
