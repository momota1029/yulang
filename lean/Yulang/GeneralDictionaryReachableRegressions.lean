import Yulang.GeneralDictionaryReachableBoundary
import Yulang.GeneralDictionaryRefreshGap
import Yulang.GeneralDictionaryTerminalClassification

/-! Reachable-scope regression tests: reject the old raw journal but retain the
real installation + view-changing refresh positive, with an actual model. -/
namespace Yulang.GeneralDictionaryReachableRegressions
open GeneralDictionaryRecursiveObstruction
open GeneralDeclarationExamples (roles)
open GeneralDictionaryReachableBoundary
open GeneralNominalSaturationState

theorem raw_not_reachable : ¬ B4TargetV5.Reachable (boundary roles) registry root
    GeneralDictionaryJournalObstruction.journal := by
  intro reachable
  exact GeneralDictionaryRefreshGap.not_sourceFormed
    ((reachable_iff_sourceFormed _ _ _).mp reachable)

theorem start_initial : (boundary roles).Initial registry root (initial context root) :=
  ⟨context,GeneralDictionaryJournalTreeFormation.initial_source,rfl⟩

theorem positive_reachable : B4TargetV5.Reachable (boundary roles) registry root
    GeneralDictionaryTerminalRefresh.refreshed :=
  ⟨_,start_initial,GeneralDictionaryTerminalClassification.two_steps⟩

/-- No new executor is asserted. This is one real reachable, stable, selected
and inhabited snapshot, evaluated by the unchanged source Evidence relation. -/
theorem positive_classified :
    B4TargetV5.Reachable (boundary roles) registry root GeneralDictionaryTerminalRefresh.refreshed ∧
    (boundary roles).Stable registry GeneralDictionaryTerminalRefresh.refreshed root ∧
    B4TargetV3.Classify (boundary roles).toSourceBoundary registry GeneralDictionaryTerminalRefresh.refreshed root
      (.selected (.node 40 [])) ∧
    Models GeneralDictionaryTerminalRefresh.refreshed GeneralNominalExamples.model ∧
    (∀ model, Models GeneralDictionaryTerminalRefresh.refreshed model →
      (boundary roles).Evidence registry GeneralDictionaryTerminalRefresh.refreshed model root (.node 40 [])) :=
  ⟨positive_reachable,GeneralDictionaryTerminalRefresh.stable,
    GeneralDictionaryTerminalClassification.classified,GeneralDictionaryTerminalRefresh.inhabited,
    GeneralDictionaryTerminalRefresh.current_evidence⟩
end Yulang.GeneralDictionaryReachableRegressions
