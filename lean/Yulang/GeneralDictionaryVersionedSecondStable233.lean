import Yulang.GeneralDictionaryVersionedSecondEquality233
import Yulang.GeneralDictionaryVersionedSecondRefresh233
import Yulang.GeneralDictionaryVersionedSecondStep233
import Yulang.GeneralNominalVersionedCommitted232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedSecondStable233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedSecondInstall233
open GeneralDictionaryVersionedSecondSelected233 (raw_sites centers frame)
open GeneralNominalVersionedJournal232 GeneralNominalVersionedKernel232

theorem edges_empty : installed.core.erased.current.edges = [] := by
  change ([] ++ GeneralNominalVersionedChildren232.edges GeneralDictionaryOptionalInstall229.plan) ++
    GeneralNominalVersionedChildren232.edges plan = []
  unfold GeneralNominalVersionedChildren232.edges
  rw [GeneralDictionaryVersionedInitialFrame233.children_empty,terminal]
  rfl

theorem generated_only (generated : GeneralNominalSaturationState.Generated installed.core.erased.current root focus) :
    focus = root := GeneralNominalVersionedTerminalStable233.generated_only raw_sites edges_empty generated

theorem point_closed : GeneralNominalReobservationSteps.PointClosed installed.core.erased.current.context.state :=
  GeneralDictionaryJournalRefinement228Reobserve.point_closed _ _ _

theorem frame_plan (framed : GeneralNominalVersionedEvidence231.Frame registry installed.core root key candidate) :
    candidate = GeneralNominalVersionedInstallation231.replayPlan plan :=
  GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl raw_sites centers framed frame

theorem no_install (candidate : Effect roles) (enabled : Installable registry installed candidate)
    (same : candidate.plan.packet.site.occurrence = root) : Committed installed candidate.plan := by
  have framed := candidate.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,same] at framed
  have equal := frame_plan framed
  rw [equal]
  exact GeneralNominalVersionedCommitted232.replay_committed GeneralDictionaryVersionedPointStage233.point effect

/-- Full guarded-kernel stability, not merely install-only closure. The refresh
barrier relies on the kernel's explicitly inherited source-only trusted cache. -/
theorem stable : Stable registry installed root := by
  intro focus generated next action
  have same := generated_only generated
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent => exact absent _ (raw_sites ▸ List.mem_singleton_self _) same.symm
    | refresh context certificate identity member unknown known =>
      exact GeneralDictionaryVersionedSecondRefresh233.no_refresh context certificate unknown known
    | reobserve revision certificate improved =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision point_closed revision improved
    | equate first last one two equal novel =>
      exact novel (GeneralDictionaryVersionedSecondEquality233.equality_closed first last one two equal)
  | refresh focus context certificate identity member unknown known =>
    exact GeneralDictionaryVersionedSecondRefresh233.no_refresh context certificate unknown known
  | install candidate enabled novel => exact novel (no_install candidate enabled same)
  | merge first last one two same novel =>
    rw [centers] at one two
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact novel (.refl _)

theorem halted : ∀ next, ¬ Step registry root installed next := by
  rintro next ⟨focus,generated,action⟩
  exact stable focus generated next action

theorem source_stable : (GeneralNominalVersionedSourceBoundary232.boundary roles).Stable sourceRegistry installed root := stable

end Yulang.GeneralDictionaryVersionedSecondStable233
