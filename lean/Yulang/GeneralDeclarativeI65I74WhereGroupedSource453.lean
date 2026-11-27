import Yulang.GeneralDeclarativeI65I74WhereGroupedEntry453

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.GroupedEntry453
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open OutputPhase452
open InternalK2452
open LiteralAndInternal452
open GeneralDeclarativeCaptureClosure320 (withOrdinary)

theorem every_reported_group_has_all_its_actual_ordered_origins453 {p : FullProblem}
    (x : ScopedLiteralReport p) {r : GroupedReport} (exact : SameReport r (exactReport x))
    {g : CohortView} (present : g ∈ r.origins) :
    ∃ source : CohortOrigins, source ∈ x.internal.groups ∧
      g = source.marks.map OriginalMark.literal ∧
      source.marks = x.actual.diagnostics.atClass source.key ∧
      source.marks ≠ [] ∧ source.marks.Sublist x.actual.diagnostics.marks ∧
      ∀ m ∈ source.marks,
        (∃ w : SourcePointAt x.actual.parent m.ordinal,
          w.original.id = m.writtenId ∧ w.capture = m.actualCenter ∧ w.request = m.request) ∧
        RootCycle p.state.base m.request := by
  have included : g ∈ originGroups x := exact.2.2.mem_iff.mp present
  obtain ⟨source,selected,map⟩ := List.mem_map.mp included
  obtain ⟨only,notEmpty,order,cycle⟩ :=
    one_checked_entry_means_K2_at_every_original452 x.actual.diagnostics selected
  exact ⟨source,selected,map.symm,only,notEmpty,order,fun m site =>
    ⟨original_mark_has_exact_actual_source_site452 x.actual.diagnostics (order.subset site), cycle m site⟩⟩

theorem exact_child_cycle_is_in_report_after_actual_output_emission453 {p : FullProblem}
    (x : ScopedLiteralReport p) {r : GroupedReport} (exact : SameReport r (exactReport x))
    {m : OriginalMark} (actual : m ∈ x.actual.diagnostics.marks)
    (cy : GeneralDeclarativePriority321.RootRecurs
      (withOrdinary p.state.base.core.current.ordinary
        (emissionRows (verifiedEmissionPairs452 x.actual.diagnostics))) m.request.demand) :
    ∃ g ∈ r.origins, m.literal ∈ g := by
  obtain ⟨source,⟨group,located⟩,_⟩ :=
    (checked_batch_internal_report_is_exactly_for_its_same_phase452 x.internal m actual).mp cy
  have included : (source.marks.map OriginalMark.literal) ∈ originGroups x :=
    List.mem_map.mpr ⟨source,group,rfl⟩
  exact ⟨_,exact.2.2.mem_iff.mpr included,List.mem_map.mpr ⟨m,located,rfl⟩⟩

theorem accepted_grouped_has_original_positional_trace_and_no_writes453 {p : FullProblem}
    {r : GroupedReport} {w : ScopedLiteralInput}
    (ok : check_full453 p (.grouped r) (.grouped w) = true) :
    ∃ x : ScopedLiteralReport p, WholeRoster x ∧ SameReport r (exactReport x) ∧
      ExactReport p.old x.localK2.report ∧ x.localK2.report.writes = [] ∧
      (∀ m, FitsFull p.state m → WhereSites450.ReportEvidence p.state.base m p.root x.localK2.report) := by
  have valid := (exact_scoped_grouped_report_iff_finite_wire453 p r).mp ⟨w,ok⟩
  obtain ⟨x,guard,exact⟩ := valid
  have source := any_literal_replay_preserves_original_scoped_report_meaning452 p x
  exact ⟨x,guard,exact,source.1,rfl,source.2⟩

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.GroupedEntry453
