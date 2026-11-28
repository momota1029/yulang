import Yulang.GeneralDeclarativeI65I74FlatMeaning481

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Flat481
open RetainedFull445
open Checker408 (Result)

open MixedFixed442
open WhereAssociated432 (matches_associated_report_exact432)

theorem legacyClassifiedMonotone481 (p : FullProblem) (r : Result) {s t : LegacyScope}
    (order : s.rank ≤ t.rank) (h : legacyClassified p r s) : legacyClassified p r t := by
  cases s <;> cases t <;> simp only [LegacyScope.rank] at order <;>
    first
    | exact h
    | exact Or.inl h
    | exact Or.inl (Or.inl h)
    | exact Or.inl (Or.inl (Or.inl h))
    | omega

theorem legacyEvidenceMonotone481 (p : FullProblem) (m : I72.Model) (r : Result) {s t : LegacyScope}
    (order : s.rank ≤ t.rank) (h : legacyEvidence p m r s) : legacyEvidence p m r t := by
  cases s <;> cases t <;> simp only [LegacyScope.rank] at order <;>
    first
    | exact h
    | exact Or.inl h
    | exact Or.inl (Or.inl h)
    | exact Or.inl (Or.inl (Or.inl h))
    | omega

theorem eachLegacyLeafSound481 (p : FullProblem) (r : Result) (w : LegacyWire)
    (accepted : checkLegacy p r w = true) :
    legacyClassified p r w.scope ∧ ∀ m : I72.Model, FitsFull p.state m → legacyEvidence p m r w.scope := by
  cases w with
  | retained w => exact RetainedSplit446.check_full_sound446 p r w accepted
  | selected w =>
    simp only [checkLegacy] at accepted
    cases got : RetainedSplit446.SelectedReplay447.readLocalSource p.old w with
    | none => simp [got] at accepted
    | some source =>
      rw [got] at accepted
      obtain ⟨matched,reported⟩ := Bool.and_eq_true_iff.mp accepted
      obtain ⟨a,same⟩ := matches_selection_exact445 matched
      have report : r = a.report := by
        change r = sourceReport a.source
        rw [same]
        exact (matches_associated_report_exact432 _ _).mp reported
      refine ⟨.inr ⟨a,report⟩,fun m fit => ?_⟩
      have exactTargets := stored_selection_fixed_targets445 a.kept m fit
      exact .inr ⟨a,report,source_event_dictionary445 a.source m fit.1 exactTargets,exactTargets⟩
  | «opaque» w =>
    obtain ⟨a,report⟩ := Opaque448.accepted_opaque_has_exact_choice448 (w := w) accepted
    exact report.symm ▸ Opaque448.independent_resolved_choice_sound448 a
  | whole w =>
    obtain ⟨a,_,report⟩ := Opaque448.Whole.accepted_whole_wire_is_exact_choice448 (w := w) accepted
    obtain ⟨e,tr,writes,model⟩ := Opaque448.Roster.whole_choice_assembly448 a
    refine ⟨.inr ⟨a,report⟩,fun m fit => .inr ⟨a,report,e,?_,?_,?_,model m fit.1⟩⟩
    · exact report.symm ▸ tr
    · rw [report]
      exact .selected .nil (.selected rfl)
    · exact report.symm ▸ writes
  | listSite w =>
    obtain ⟨a,same,_⟩ := ListSites449.accepted_list_report_reads_exact_declaration449 (w := w) accepted
    exact same.symm ▸ ListSites449.independent_list_report_sound449 a
  | listFrame w =>
    obtain ⟨a,report,_⟩ := ListSites449.Frame.actual_checked_frame_reads_exact_source449 (w := w) accepted
    obtain ⟨e,tr,writes,caps,meaning⟩ := ListSites449.Frame.exact_framed_selection_assembly449 a
    refine ⟨.inr ⟨a,report⟩,fun m fit => .inr ⟨a,report,e,?_,?_,?_,caps,meaning m fit.1⟩⟩
    · exact report.symm ▸ tr
    · rw [report]
      exact .selected .nil (.selected rfl)
    · exact report.symm ▸ writes
  | guardedWhere w =>
    have raw : (WhereSites450.NoSiblingMerge.noSiblingMerge p &&
        WhereSites450.check_full450 p r (.whereRoot w)) = true := accepted
    have entry := Bool.and_eq_true_iff.mp raw
    obtain ⟨a,same,_,_⟩ := WhereSites450.only_true_original_ordered_reports_are_accepted450 entry.2
    have guarded : WhereSites450.NoSiblingMerge.GuardedOriginal p r :=
      ⟨a,same,WhereSites450.NoSiblingMerge.actual_guard_is_exact_visible_source450.mp entry.1⟩
    subst r
    obtain ⟨e,tr,summary,out⟩ := WhereSites450.independent_original_rejection_has_real_trace450 a
    exact ⟨.inr guarded,fun m fit => .inr ⟨guarded,e,tr,summary,out,
      WhereSites450.exact_where_trace_model_meaning450 tr m fit.1⟩⟩

theorem directLegacyFlatSound481 (p : FullProblem) (r : Result) (scope : LegacyScope)
    (w : LegacyWire) (accepted : check_full_flat p (.legacy scope r) (.legacy w) = true) :
    legacyClassified p r scope ∧ ∀ m : I72.Model, FitsFull p.state m → legacyEvidence p m r scope := by
  obtain ⟨fits,leaf⟩ := Bool.and_eq_true_iff.mp accepted
  have grade := of_decide_eq_true fits
  have sound := eachLegacyLeafSound481 p r w leaf
  exact ⟨legacyClassifiedMonotone481 p r grade sound.1,
    fun m fit => legacyEvidenceMonotone481 p m r grade (sound.2 m fit)⟩

/-- For all flat inputs, including introduced mismatched combinations,
the same FullProblem and every one of its old Fits are used. -/
theorem check_full_flat_sound481 (p : FullProblem) (r : FlatReport) (w : FlatWitness)
    (ok : check_full_flat p r w = true) :
    FlatClassified p r ∧ ∀ m : I72.Model, FitsFull p.state m → FlatEvidence p m r := by
  cases r <;> cases w <;> try exact (Bool.false_ne_true ok).elim
  case legacy.legacy level report data => exact directLegacyFlatSound481 p report level data ok
  case grouped.grouped report data =>
    have chosen := (WhereSites450.OriginalCohorts451.GroupedEntry453.exact_scoped_grouped_report_iff_finite_wire453 p report).mp ⟨data,ok⟩
    exact ⟨chosen,WhereSites450.OriginalCohorts451.GroupedEntry453.scoped_grouped_sound_at_every_fit453 chosen⟩
  case rawGrouped.rawGrouped report data =>
    obtain ⟨x,ne,same⟩ := (WhereSites450.OriginalCohorts451.SamePhase454.exact_same_phase_report_iff_finite_wire454 p report).mp ⟨data,ok⟩
    exact ⟨⟨x,ne,same⟩,fun m fit => ⟨x,ne,same,WhereSites450.OriginalCohorts451.SamePhase454.actual_parent_event_meaning_at_every_fit454 p x m fit⟩⟩
  case fieldRecord.fieldRecord report data =>
    have accepted : RoutedRecord455.checkField p.old report data = true := ok
    have exactOld := (RoutedRecord455.actual_routed_field_report_iff_finite_wire455 p.old report).mp ⟨data,accepted⟩
    exact ⟨exactOld,fun m fit => RoutedRecord455.routed_field_report_is_sound_in_every_same_fit455 exactOld m fit.1⟩
  case fieldMixed.fieldMixed report data =>
    have accepted : RoutedMixed456.checkField p.old report data = true := ok
    have exactOld := (RoutedMixed456.actual_routed_field_report_iff_finite_wire456 p.old report).mp ⟨data,accepted⟩
    exact ⟨exactOld,fun m fit => RoutedMixed456.routed_field_report_is_sound_in_every_same_fit456 exactOld m fit.1⟩
  case fieldNominal.fieldNominal report data =>
    have accepted : RoutedNominalMixed456.checkField p.old report data = true := ok
    have exactOld := (RoutedNominalMixed456.actual_routed_field_report_iff_finite_wire456 p.old report).mp ⟨data,accepted⟩
    exact ⟨exactOld,fun m fit => RoutedNominalMixed456.routed_field_report_is_sound_in_every_same_fit456 exactOld m fit.1⟩
  case fieldReadyRecord.fieldReadyRecord report data =>
    have accepted : RoutedReadyRecord457.checkField p.old report data = true := ok
    have exactOld := (RoutedReadyRecord457.actual_routed_field_report_iff_finite_wire457 p.old report).mp ⟨data,accepted⟩
    exact ⟨exactOld,fun m fit => RoutedReadyRecord457.routed_field_report_is_sound_in_every_same_fit457 exactOld m fit.1⟩
  case fieldReadyMixed.fieldReadyMixed report data =>
    have accepted : RoutedReadyMixed457.checkField p.old report data = true := ok
    have exactOld := (RoutedReadyMixed457.actual_routed_field_report_iff_finite_wire457 p.old report).mp ⟨data,accepted⟩
    exact ⟨exactOld,fun m fit => RoutedReadyMixed457.routed_field_report_is_sound_in_every_same_fit457 exactOld m fit.1⟩
  case fieldVariant.fieldVariant report data =>
    have accepted : RoutedInlineVariant458.checkField p.old report data = true := ok
    have exactOld := (RoutedInlineVariant458.actual_routed_field_report_iff_finite_wire458 p.old report).mp ⟨data,accepted⟩
    exact ⟨exactOld,fun m fit => RoutedInlineVariant458.routed_field_report_is_sound_in_every_same_fit458 exactOld m fit.1⟩
  case fieldStructural.fieldStructural report data =>
    have accepted : RoutedInlineStructural458.checkField p.old report data = true := (InstalledProtocolSum462.same_plain_field_bool p.old report data).trans ok
    have exactOld := (RoutedInlineStructural458.actual_routed_field_report_iff_finite_wire458 p.old report).mp ⟨data,accepted⟩
    exact ⟨exactOld,fun m fit => RoutedInlineStructural458.routed_field_report_is_sound_in_every_same_fit458 exactOld m fit.1⟩
  case fieldProjected.fieldProjected report data =>
    have accepted : ProjectedClosedEntry459.checkField p.old report data = true := (InstalledProtocolSum462.same_projected_field_bool p.old report data).trans ok
    have exactOld := (ProjectedClosedEntry459.actual_routed_field_report_iff_finite_wire459 p.old report).mp ⟨data,accepted⟩
    exact ⟨exactOld,fun m fit => ProjectedClosedEntry459.routed_field_report_is_sound_in_every_same_fit459 exactOld m fit.1⟩
  case fieldHomogeneous.fieldHomogeneous report data =>
    have accepted : HomogeneousClosedEntry459.checkField p.old report data = true := (InstalledProtocolSum462.same_homogeneous_field_bool p.old report data).trans ok
    have exactOld := (HomogeneousClosedEntry459.actual_routed_field_report_iff_finite_wire459 p.old report).mp ⟨data,accepted⟩
    exact ⟨exactOld,fun m fit => HomogeneousClosedEntry459.routed_field_report_is_sound_in_every_same_fit459 exactOld m fit.1⟩

theorem retained_sound_from_flat481 (p : FullProblem) (r : Result) (w : RetainedSplit446.Witness446)
    (ok : RetainedSplit446.check_full446 p r w = true) :
    ClassifiedAsFull p.state p.root r ∧ ∀ m : I72.Model, FitsFull p.state m → ReportEvidenceFull p.state m p.root r :=
  check_full_flat_sound481 p (.legacy .retained r) (.legacy (flattenRetained w))
    ((retained_same_Bool481 p r w).trans ok)

theorem selected_sound_from_flat481 (p : FullProblem) (r : Result) (w : RetainedSplit446.SelectedReplay447.Witness447)
    (ok : RetainedSplit446.SelectedReplay447.check_full447 p r w = true) :
    ClassifiedAsFull p.state p.root r ∧ ∀ m : I72.Model, FitsFull p.state m → ReportEvidenceFull p.state m p.root r :=
  check_full_flat_sound481 p (.legacy .selected r) (.legacy (flattenSelected w))
    ((selected_same_Bool481 p r w).trans ok)

theorem opaque_sound_from_flat481 (p : FullProblem) (r : Result) (w : Opaque448.Witness448)
    (ok : Opaque448.check_full448 p r w = true) :
    ClassifiedAsFull p.state p.root r ∧ ∀ m : I72.Model, FitsFull p.state m → ReportEvidenceFull p.state m p.root r :=
  check_full_flat_sound481 p (.legacy .opaque r) (.legacy (flattenOpaque w))
    ((opaque_same_Bool481 p r w).trans ok)

theorem whole_sound_from_flat481 (p : FullProblem) (r : Result) (w : Opaque448.Whole.Witness)
    (ok : Opaque448.Whole.check_full448 p r w = true) :
    Opaque448.Whole.ClassifiedAs448 p r ∧ ∀ m : I72.Model, FitsFull p.state m → Opaque448.Whole.ReportEvidence448 p m r :=
  check_full_flat_sound481 p (.legacy .whole r) (.legacy (flattenWhole w))
    ((whole_same_Bool481 p r w).trans ok)

theorem listSite_sound_from_flat481 (p : FullProblem) (r : Result) (w : ListSites449.Witness)
    (ok : ListSites449.check_full449 p r w = true) :
    Opaque448.Whole.ClassifiedAs448 p r ∧ ∀ m : I72.Model, FitsFull p.state m → Opaque448.Whole.ReportEvidence448 p m r :=
  check_full_flat_sound481 p (.legacy .listSite r) (.legacy (flattenListSite w))
    ((listSite_same_Bool481 p r w).trans ok)

theorem listFrame_sound_from_flat481 (p : FullProblem) (r : Result) (w : ListSites449.Frame.Witness)
    (ok : ListSites449.Frame.check_full449 p r w = true) :
    ListSites449.Frame.ClassifiedAs449 p r ∧ ∀ m : I72.Model, FitsFull p.state m → ListSites449.Frame.ReportEvidence449 p m r :=
  check_full_flat_sound481 p (.legacy .listFrame r) (.legacy (flattenListFrame w))
    ((listFrame_same_Bool481 p r w).trans ok)

theorem guardedWhere_sound_from_flat481 (p : FullProblem) (r : Result) (w : WhereSites450.Witness)
    (ok : WhereSites450.NoSiblingMerge.check_full450 p r w = true) :
    WhereSites450.NoSiblingMerge.ClassifiedAs p r ∧ ∀ m : I72.Model, FitsFull p.state m → WhereSites450.NoSiblingMerge.ReportEvidence p m r :=
  check_full_flat_sound481 p (.legacy .guardedWhere r) (.legacy (flattenGuardedWhere w))
    ((guardedWhere_same_Bool481 p r w).trans ok)

theorem grouped_sound_from_flat481 (p : FullProblem) (r : WhereSites450.OriginalCohorts451.GroupedEntry453.Report) (w : WhereSites450.OriginalCohorts451.GroupedEntry453.Witness)
    (ok : WhereSites450.OriginalCohorts451.GroupedEntry453.check_full453 p r w = true) :
    WhereSites450.OriginalCohorts451.GroupedEntry453.ClassifiedAs p r ∧ ∀ m : I72.Model, FitsFull p.state m → WhereSites450.OriginalCohorts451.GroupedEntry453.ReportEvidence p m r := by
  have exact := check_full_flat_sound481 p (flattenGroupedReport r) (flattenGroupedWire w)
    ((grouped_same_Bool481 p r w).trans ok)
  exact ⟨(grouped_classification_reflects481 p r).mp exact.1,
    fun m fit => (grouped_evidence_reflects481 p m r).mp (exact.2 m fit)⟩

theorem rawGrouped_sound_from_flat481 (p : FullProblem) (r : WhereSites450.OriginalCohorts451.SamePhase454.Report) (w : WhereSites450.OriginalCohorts451.SamePhase454.Witness)
    (ok : WhereSites450.OriginalCohorts451.SamePhase454.check_full454 p r w = true) :
    WhereSites450.OriginalCohorts451.SamePhase454.ClassifiedAs p r ∧ ∀ m : I72.Model, FitsFull p.state m → WhereSites450.OriginalCohorts451.SamePhase454.ReportEvidence p m r := by
  have exact := check_full_flat_sound481 p (flattenRawGroupedReport r) (flattenRawGroupedWire w)
    ((rawGrouped_same_Bool481 p r w).trans ok)
  exact ⟨(rawGrouped_classification_reflects481 p r).mp exact.1,
    fun m fit => (rawGrouped_evidence_reflects481 p m r).mp (exact.2 m fit)⟩

theorem fieldRecord_sound_from_flat481 (p : FullProblem) (r : RoutedRecord455.Report) (w : RoutedRecord455.Witness)
    (ok : RoutedRecord455.check_full455 p r w = true) :
    RoutedRecord455.ClassifiedAs p r ∧ ∀ m : I72.Model, FitsFull p.state m → RoutedRecord455.ReportEvidence p m r := by
  have exact := check_full_flat_sound481 p (flattenFieldRecordReport r) (flattenFieldRecordWire w)
    ((fieldRecord_same_Bool481 p r w).trans ok)
  exact ⟨(fieldRecord_classification_reflects481 p r).mp exact.1,
    fun m fit => (fieldRecord_evidence_reflects481 p m r).mp (exact.2 m fit)⟩

theorem fieldMixed_sound_from_flat481 (p : FullProblem) (r : RoutedMixed456.Report) (w : RoutedMixed456.Witness)
    (ok : RoutedMixed456.check_full456 p r w = true) :
    RoutedMixed456.ClassifiedAs p r ∧ ∀ m : I72.Model, FitsFull p.state m → RoutedMixed456.ReportEvidence p m r := by
  have exact := check_full_flat_sound481 p (flattenFieldMixedReport r) (flattenFieldMixedWire w)
    ((fieldMixed_same_Bool481 p r w).trans ok)
  exact ⟨(fieldMixed_classification_reflects481 p r).mp exact.1,
    fun m fit => (fieldMixed_evidence_reflects481 p m r).mp (exact.2 m fit)⟩

theorem fieldNominal_sound_from_flat481 (p : FullProblem) (r : RoutedNominalMixed456.Report) (w : RoutedNominalMixed456.Witness)
    (ok : RoutedNominalMixed456.check_full_nominal456 p r w = true) :
    RoutedNominalMixed456.ClassifiedAs p r ∧ ∀ m : I72.Model, FitsFull p.state m → RoutedNominalMixed456.ReportEvidence p m r := by
  have exact := check_full_flat_sound481 p (flattenFieldNominalReport r) (flattenFieldNominalWire w)
    ((fieldNominal_same_Bool481 p r w).trans ok)
  exact ⟨(fieldNominal_classification_reflects481 p r).mp exact.1,
    fun m fit => (fieldNominal_evidence_reflects481 p m r).mp (exact.2 m fit)⟩

theorem fieldReadyRecord_sound_from_flat481 (p : FullProblem) (r : RoutedReadyRecord457.Report) (w : RoutedReadyRecord457.Witness)
    (ok : RoutedReadyRecord457.check_full457 p r w = true) :
    RoutedReadyRecord457.ClassifiedAs p r ∧ ∀ m : I72.Model, FitsFull p.state m → RoutedReadyRecord457.ReportEvidence p m r := by
  have exact := check_full_flat_sound481 p (flattenFieldReadyRecordReport r) (flattenFieldReadyRecordWire w)
    ((fieldReadyRecord_same_Bool481 p r w).trans ok)
  exact ⟨(fieldReadyRecord_classification_reflects481 p r).mp exact.1,
    fun m fit => (fieldReadyRecord_evidence_reflects481 p m r).mp (exact.2 m fit)⟩

theorem fieldReadyMixed_sound_from_flat481 (p : FullProblem) (r : RoutedReadyMixed457.Report) (w : RoutedReadyMixed457.Witness)
    (ok : RoutedReadyMixed457.check_full_ready_mixed457 p r w = true) :
    RoutedReadyMixed457.ClassifiedAs p r ∧ ∀ m : I72.Model, FitsFull p.state m → RoutedReadyMixed457.ReportEvidence p m r := by
  have exact := check_full_flat_sound481 p (flattenFieldReadyMixedReport r) (flattenFieldReadyMixedWire w)
    ((fieldReadyMixed_same_Bool481 p r w).trans ok)
  exact ⟨(fieldReadyMixed_classification_reflects481 p r).mp exact.1,
    fun m fit => (fieldReadyMixed_evidence_reflects481 p m r).mp (exact.2 m fit)⟩

theorem fieldVariant_sound_from_flat481 (p : FullProblem) (r : RoutedInlineVariant458.Report) (w : RoutedInlineVariant458.Witness)
    (ok : RoutedInlineVariant458.check_full458 p r w = true) :
    RoutedInlineVariant458.ClassifiedAs p r ∧ ∀ m : I72.Model, FitsFull p.state m → RoutedInlineVariant458.ReportEvidence p m r := by
  have exact := check_full_flat_sound481 p (flattenFieldVariantReport r) (flattenFieldVariantWire w)
    ((fieldVariant_same_Bool481 p r w).trans ok)
  exact ⟨(fieldVariant_classification_reflects481 p r).mp exact.1,
    fun m fit => (fieldVariant_evidence_reflects481 p m r).mp (exact.2 m fit)⟩

theorem fieldStructural_sound_from_flat481 (p : FullProblem) (r : RoutedInlineStructural458.Report) (w : RoutedInlineStructural458.Witness)
    (ok : RoutedInlineStructural458.check_full_structural458 p r w = true) :
    RoutedInlineStructural458.ClassifiedAs p r ∧ ∀ m : I72.Model, FitsFull p.state m → RoutedInlineStructural458.ReportEvidence p m r := by
  have exact := check_full_flat_sound481 p (flattenFieldStructuralReport r) (flattenFieldStructuralWire w)
    ((fieldStructural_same_Bool481 p r w).trans ok)
  exact ⟨(fieldStructural_classification_reflects481 p r).mp exact.1,
    fun m fit => (fieldStructural_evidence_reflects481 p m r).mp (exact.2 m fit)⟩

theorem fieldProjected_sound_from_flat481 (p : FullProblem) (r : ProjectedClosedEntry459.Report) (w : ProjectedClosedEntry459.Witness)
    (ok : ProjectedClosedEntry459.check_full_projected459 p r w = true) :
    ProjectedClosedEntry459.ClassifiedAs p r ∧ ∀ m : I72.Model, FitsFull p.state m → ProjectedClosedEntry459.ReportEvidence p m r := by
  have exact := check_full_flat_sound481 p (flattenFieldProjectedReport r) (flattenFieldProjectedWire w)
    ((fieldProjected_same_Bool481 p r w).trans ok)
  exact ⟨(fieldProjected_classification_reflects481 p r).mp exact.1,
    fun m fit => (fieldProjected_evidence_reflects481 p m r).mp (exact.2 m fit)⟩

theorem fieldHomogeneous_sound_from_flat481 (p : FullProblem) (r : HomogeneousClosedEntry459.Report) (w : HomogeneousClosedEntry459.Witness)
    (ok : HomogeneousClosedEntry459.check_full_homogeneous459 p r w = true) :
    HomogeneousClosedEntry459.ClassifiedAs p r ∧ ∀ m : I72.Model, FitsFull p.state m → HomogeneousClosedEntry459.ReportEvidence p m r := by
  have exact := check_full_flat_sound481 p (flattenFieldHomogeneousReport r) (flattenFieldHomogeneousWire w)
    ((fieldHomogeneous_same_Bool481 p r w).trans ok)
  exact ⟨(fieldHomogeneous_classification_reflects481 p r).mp exact.1,
    fun m fit => (fieldHomogeneous_evidence_reflects481 p m r).mp (exact.2 m fit)⟩

end Yulang.GeneralDeclarativeI65.I72.Flat481
