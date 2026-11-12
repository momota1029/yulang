import Yulang.GeneralDictionaryRecordedRevisionTrace
import Yulang.GeneralDictionaryInspectionTransportExamples
import Yulang.GeneralNominalReobservationExamples

/-! Two distinct real update regressions: a nonempty recorded journal followed
by descriptor extension, and an actual point-descriptor replacement on the
existing empty-journal fork. These do not claim a nonempty arbitrary replacement
is report-preserving, nor construct Evidence for the rejected generated child. -/
namespace Yulang.GeneralDictionaryRecordedObservationExamples
open GeneralNominalSaturationState
open GeneralDictionaryRecordedObservationTrace

namespace Nonempty
open GeneralNominalFeedbackObstruction GeneralNominalFeedbackRefresh
open GeneralDictionaryInspectionTransportExamples

theorem recorded_reports : RecordedReports registry installed observation := by
  intro stored member
  have same : stored = packet := by
    simpa only [installed,GeneralNominalFeedbackSites.install,initialState,initial,List.mem_cons,List.not_mem_nil,or_false] using member
  subst stored
  exact parent_preserves

theorem actual_path : B4Target.Steps (Step registry root) initialState refreshed := by
  apply B4Target.Steps.tail (t := installed)
  · exact .tail .refl (.ordinary ⟨GeneralNominalFeedbackRegressions.install_step,
      GeneralDictionaryOrdinaryTrace.install_extension initialState packet rfl⟩)
  · exact .refresh installed observation recorded_reports refresh_step

theorem nonempty_current :
    refreshed.packets ≠ [] ∧ GeneralDictionaryCurrentJournal.Current registry refreshed := by
  refine ⟨?_,initial_trace_current registry root context refreshed actual_path⟩
  simp [refreshed,regenerate,installed,GeneralNominalFeedbackSites.install]

theorem modeled_current_parent : Models refreshed model ∧
    GeneralDictionaryRecursiveEvidence.Instance registry refreshed.context model root 2 [child] := by
  have valid := (refresh_models model).mpr installed_models
  have rule := nonempty_current.2 packet (by simp [refreshed,regenerate,installed,GeneralNominalFeedbackSites.install]) model valid
  refine ⟨valid,?_⟩
  simpa only [children_exact,GeneralNominalDemandMerging.pointSite] using rule
end Nonempty

namespace PointReplacement
open GeneralNominalRefreshFork GeneralNominalRefreshDivergence
open GeneralNominalReobservationExamples

theorem recorded_reports : GeneralDictionaryRecordedRevisionTrace.Reports registry (after true) revision := by
  intro packet member
  cases member

theorem actual_guarded_repair : GeneralDictionaryRecordedRevisionTrace.Step registry root (after true) (after false) :=
  .revision (after true) revision recorded_reports revision_certified repair_step

end PointReplacement
end Yulang.GeneralDictionaryRecordedObservationExamples
