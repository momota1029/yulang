import Yulang.GeneralNominalMixedCompletion198
import Yulang.GeneralNominalCompletionObstruction195

/-! Adding actual journal recovery does not eliminate the existing current
materialization obstruction. This refutes completion, not semantic Evidence. -/
namespace Yulang.GeneralNominalMixedObstruction198
open GeneralNominalMixedCompletion198
open GeneralNominalCenteredHeadWFJoinSource
open GeneralNominalCenteredHeadWFJoinLocal
open GeneralNominalCenteredHeadWFJoinCounterexample
open GeneralNominalCenteredHeadWFBoundary (boundary)

theorem no_node : ¬ NodeAvailable registry start root := by
  rintro ⟨key,kids,recorded | ⟨plan,reuse,same,_,_⟩⟩
  · obtain ⟨packet,member,_,_,_⟩ := recorded
    cases member
  · exact GeneralNominalCompletionObstruction195.no_reusable plan same reuse

theorem no_selected_completion : ¬ SelectedCompletion registry start root :=
  fun complete => no_node (complete root .root 37 children selected)

theorem no_total_completion : ¬ TotalCompletion registry start root :=
  fun complete => no_node (complete root .root)

/-- Even an actual initial path and all the usual stable selected source facts
do not establish this mixed production contract. -/
theorem stable_selected_missing_completion :
    B4Target.Steps (GeneralNominalMixedJournal197.MixedStep registry root) start start ∧
    B4TargetV6.Reachable (boundary roles) registry root start ∧
    (boundary roles).Stable registry start root ∧
    GeneralNominalCenteredHeadWFBoundary.Local registry start root (.selected 37 children) ∧
    (∃ model, GeneralNominalCenteredHeadStepEffects.Models start model) ∧
    ¬ SelectedCompletion registry start root := by
  refine ⟨.refl,reachable,stable,selected,?_,no_selected_completion⟩
  obtain ⟨model,valid,_⟩ := positive_baseline
  exact ⟨model,valid⟩
end Yulang.GeneralNominalMixedObstruction198
