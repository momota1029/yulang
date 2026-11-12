import Yulang.GeneralDictionaryOutputMergeSiteClosure
import Yulang.GeneralDictionaryOutputMergeObservationClosure

/-! Exact remaining stability obligation for the reachable output-merge
example. This equivalence alone does not discharge the refresh obligation. -/
namespace Yulang.GeneralDictionaryOutputMergeStabilityResidual
open GeneralDictionaryOutputMergeRefresh GeneralDictionaryOutputMergeSuccess
open GeneralDictionaryOutputMergeSiteClosure GeneralDictionaryOutputMergeInstallClosure
open GeneralDictionaryOutputMergeObservationClosure
open GeneralNominalExamples (displayRoot)

/-- No registered unknown source can acquire Known in a certified refresh. -/
def RefreshClosed : Prop :=
  ∀ context : GeneralNominalCandidates.Context,
    GeneralNominalFeedbackSteps.Refresh refreshed.current context →
    ∀ source ∈ GeneralNominalState.sources refreshed.current.context.state,
      ¬ GeneralNominalState.Known refreshed.current.context.state source →
      ¬ GeneralNominalState.Known context.state source

theorem stable_of_refresh_closed (closed : RefreshClosed) :
    GeneralNominalSupportSteps.Stable registry refreshed displayRoot := by
  intro focus reached after action
  cases action with
  | administrative _ _ action =>
    cases action with
    | enqueue _ absent =>
      obtain ⟨site,member,same⟩ := generated_present focus reached
      exact absent site member same
    | refresh context certificate source member unknown known =>
      exact closed context certificate source member unknown known
    | equate first last _ _ equal novel =>
      exact no_fresh_equality first last equal novel
    | reobserve revision _ improved => exact no_reobservation revision improved
  | install packet _ enabled novel _ => exact novel (installs_committed packet reached enabled)
  | merge first last _ one two same novel _ => exact novel (merges_closed first last one two same)

theorem stable_iff_refresh_closed :
    GeneralNominalSupportSteps.Stable registry refreshed displayRoot ↔ RefreshClosed := by
  constructor
  · intro stable context certificate source member unknown known
    exact stable displayRoot .root _
      (.administrative displayRoot _ (.refresh displayRoot context certificate source member unknown known))
  · exact stable_of_refresh_closed
end Yulang.GeneralDictionaryOutputMergeStabilityResidual
