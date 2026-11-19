import Yulang.GeneralRebaseInstallNovelty279
import Yulang.GeneralRebaseCompiledInstall277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9600000
namespace Yulang.GeneralRebaseInstallDisplayDelta279
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseCompiledDisplay277 (compiled parent effect after children)
open GeneralRebaseInstallNovelty279 (FreshChild FullSilent LostModel)
open GeneralRebaseInstallDeltaModels279 (NoFreshRequests)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedMixedKernel234 (Step)

theorem silent : FullSilent before effect := GeneralRebaseCompiledInstall277.models

theorem no_fresh_requests : NoFreshRequests before effect := by
  intro goal output has
  have added := ((GeneralRebaseInstallRequestDelta279.fresh_exact before.core parent goal output).mp has).1
  change output ∈ GeneralNominalCenteredHeadOutputs.requests after.core goal at added
  rw [GeneralRebaseCompiledInstall277.no_new_request goal] at added
  cases added

theorem actual_child : displayChild ∈ GeneralNominalVersionedFrame231.children parent.packet :=
  children ▸ List.mem_singleton_self _

theorem fresh : FreshChild before parent := by
  exact ⟨displayChild,actual_child,fun absent => nomatch absent⟩

theorem no_lost_model : ¬ LostModel before effect :=
  (GeneralRebaseInstallNovelty279.no_loss_iff (effect := effect) (state := before) rfl).mp silent

theorem real_step : Step compiled displayRoot before after :=
  GeneralRebaseInstallNovelty279.graph_step (effect := effect) .root
    GeneralRebaseCompiledInstall277.installable fresh

theorem new_edge :
    (displayRoot,displayChild) ∈ after.core.erased.current.edges ∧
      (displayRoot,displayChild) ∉ before.core.erased.current.edges :=
  ⟨GeneralNominalVersionedInstall232.installed_child (effect := effect) actual_child,fun h => nomatch h⟩

theorem generated_before_iff (goal) : Generated before.core.erased.current displayRoot goal ↔ goal = displayRoot := by
  constructor
  · intro generated
    induction generated with
    | root => rfl
    | child _ edge => cases edge
    | alias _ _ last _ _ =>
      have old := List.mem_singleton.mp last
      exact congrArg GeneralNominalDemandMerging.Site.occurrence old
  · rintro rfl
    exact .root

theorem generates_real_child :
    Generated after.core.erased.current displayRoot displayChild ∧
      ¬ Generated before.core.erased.current displayRoot displayChild := by
  refine ⟨GeneralRebaseInstallNovelty279.graph_growth (effect := effect) .root actual_child,?_⟩
  intro old
  have same := (generated_before_iff _).mp old
  exact GeneralRebaseDisplayChildFresh276.invocation_distinct (congrArg _ same.symm)

end Yulang.GeneralRebaseInstallDisplayDelta279
