import Yulang.GeneralDeclarativeI65I74FlatOuterCodec481

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Flat481
open RetainedFull445
open Checker408 (Result)

/-- Each early level keeps exactly the predicate of its own outward
statement. The old report payloads are shared; their scopes are not. -/
def legacyClassified (p : FullProblem) (r : Result) : LegacyScope → Prop
  | .retained => ClassifiedAsFull p.state p.root r
  | .selected => ClassifiedAsFull p.state p.root r
  | .opaque => ClassifiedAsFull p.state p.root r
  | .whole => Opaque448.Whole.ClassifiedAs448 p r
  | .listSite => Opaque448.Whole.ClassifiedAs448 p r
  | .listFrame => ListSites449.Frame.ClassifiedAs449 p r
  | .guardedWhere => WhereSites450.NoSiblingMerge.ClassifiedAs p r

def legacyEvidence (p : FullProblem) (m : I72.Model) (r : Result) : LegacyScope → Prop
  | .retained => ReportEvidenceFull p.state m p.root r
  | .selected => ReportEvidenceFull p.state m p.root r
  | .opaque => ReportEvidenceFull p.state m p.root r
  | .whole => Opaque448.Whole.ReportEvidence448 p m r
  | .listSite => Opaque448.Whole.ReportEvidence448 p m r
  | .listFrame => ListSites449.Frame.ReportEvidence449 p m r
  | .guardedWhere => WhereSites450.NoSiblingMerge.ReportEvidence p m r

def FlatClassified (p : FullProblem) : FlatReport → Prop
  | .legacy s r => legacyClassified p r s
  | .grouped r => WhereSites450.OriginalCohorts451.GroupedEntry453.ExactGrouped p r
  | .rawGrouped r => WhereSites450.OriginalCohorts451.SamePhase454.Exact p r
  | .fieldRecord r => RoutedRecord455.ExactField p.old r
  | .fieldMixed r => RoutedMixed456.ExactField p.old r
  | .fieldNominal r => RoutedNominalMixed456.ExactField p.old r
  | .fieldReadyRecord r => RoutedReadyRecord457.ExactField p.old r
  | .fieldReadyMixed r => RoutedReadyMixed457.ExactField p.old r
  | .fieldVariant r => RoutedInlineVariant458.ExactField p.old r
  | .fieldStructural r => RoutedInlineStructural458.ExactField p.old r
  | .fieldProjected r => ProjectedClosedEntry459.ExactField p.old r
  | .fieldHomogeneous r => HomogeneousClosedEntry459.ExactField p.old r

def FlatEvidence (p : FullProblem) (m : I72.Model) : FlatReport → Prop
  | .legacy s r => legacyEvidence p m r s
  | .grouped r => WhereSites450.OriginalCohorts451.GroupedEntry453.GroupedEvidence p m r
  | .rawGrouped r => WhereSites450.OriginalCohorts451.SamePhase454.GroupedEvidence p m r
  | .fieldRecord r => RoutedRecord455.FieldEvidence p.old m r
  | .fieldMixed r => RoutedMixed456.FieldEvidence p.old m r
  | .fieldNominal r => RoutedNominalMixed456.FieldEvidence p.old m r
  | .fieldReadyRecord r => RoutedReadyRecord457.FieldEvidence p.old m r
  | .fieldReadyMixed r => RoutedReadyMixed457.FieldEvidence p.old m r
  | .fieldVariant r => RoutedInlineVariant458.FieldEvidence p.old m r
  | .fieldStructural r => RoutedInlineStructural458.FieldEvidence p.old m r
  | .fieldProjected r => ProjectedClosedEntry459.FieldEvidence p.old m r
  | .fieldHomogeneous r => HomogeneousClosedEntry459.FieldEvidence p.old m r

theorem retained_legacy_meaning_unchanged481 (p : FullProblem) (r : Result) :
    (FlatClassified p (.legacy .retained r) ↔ ClassifiedAsFull p.state p.root r) ∧
    (∀ m : I72.Model, FlatEvidence p m (.legacy .retained r) ↔ ReportEvidenceFull p.state m p.root r) :=
  ⟨Iff.rfl,fun _ => Iff.rfl⟩

theorem selected_legacy_meaning_unchanged481 (p : FullProblem) (r : Result) :
    (FlatClassified p (.legacy .selected r) ↔ ClassifiedAsFull p.state p.root r) ∧
    (∀ m : I72.Model, FlatEvidence p m (.legacy .selected r) ↔ ReportEvidenceFull p.state m p.root r) :=
  ⟨Iff.rfl,fun _ => Iff.rfl⟩

theorem opaque_legacy_meaning_unchanged481 (p : FullProblem) (r : Result) :
    (FlatClassified p (.legacy .opaque r) ↔ ClassifiedAsFull p.state p.root r) ∧
    (∀ m : I72.Model, FlatEvidence p m (.legacy .opaque r) ↔ ReportEvidenceFull p.state m p.root r) :=
  ⟨Iff.rfl,fun _ => Iff.rfl⟩

theorem whole_legacy_meaning_unchanged481 (p : FullProblem) (r : Result) :
    (FlatClassified p (.legacy .whole r) ↔ Opaque448.Whole.ClassifiedAs448 p r) ∧
    (∀ m : I72.Model, FlatEvidence p m (.legacy .whole r) ↔ Opaque448.Whole.ReportEvidence448 p m r) :=
  ⟨Iff.rfl,fun _ => Iff.rfl⟩

theorem listSite_legacy_meaning_unchanged481 (p : FullProblem) (r : Result) :
    (FlatClassified p (.legacy .listSite r) ↔ Opaque448.Whole.ClassifiedAs448 p r) ∧
    (∀ m : I72.Model, FlatEvidence p m (.legacy .listSite r) ↔ Opaque448.Whole.ReportEvidence448 p m r) :=
  ⟨Iff.rfl,fun _ => Iff.rfl⟩

theorem listFrame_legacy_meaning_unchanged481 (p : FullProblem) (r : Result) :
    (FlatClassified p (.legacy .listFrame r) ↔ ListSites449.Frame.ClassifiedAs449 p r) ∧
    (∀ m : I72.Model, FlatEvidence p m (.legacy .listFrame r) ↔ ListSites449.Frame.ReportEvidence449 p m r) :=
  ⟨Iff.rfl,fun _ => Iff.rfl⟩

theorem guardedWhere_legacy_meaning_unchanged481 (p : FullProblem) (r : Result) :
    (FlatClassified p (.legacy .guardedWhere r) ↔ WhereSites450.NoSiblingMerge.ClassifiedAs p r) ∧
    (∀ m : I72.Model, FlatEvidence p m (.legacy .guardedWhere r) ↔ WhereSites450.NoSiblingMerge.ReportEvidence p m r) :=
  ⟨Iff.rfl,fun _ => Iff.rfl⟩

theorem grouped_classification_reflects481 (p : FullProblem) (r : WhereSites450.OriginalCohorts451.GroupedEntry453.Report) :
    FlatClassified p (flattenGroupedReport r) ↔ WhereSites450.OriginalCohorts451.GroupedEntry453.ClassifiedAs p r := by
  cases r with
  | previous old => rfl
  | grouped exactOld => rfl

theorem grouped_evidence_reflects481 (p : FullProblem) (m : I72.Model) (r : WhereSites450.OriginalCohorts451.GroupedEntry453.Report) :
    FlatEvidence p m (flattenGroupedReport r) ↔ WhereSites450.OriginalCohorts451.GroupedEntry453.ReportEvidence p m r := by
  cases r with
  | previous old => rfl
  | grouped exactOld => rfl

theorem rawGrouped_classification_reflects481 (p : FullProblem) (r : WhereSites450.OriginalCohorts451.SamePhase454.Report) :
    FlatClassified p (flattenRawGroupedReport r) ↔ WhereSites450.OriginalCohorts451.SamePhase454.ClassifiedAs p r := by
  cases r with
  | previous old => exact grouped_classification_reflects481 p old
  | rawGrouped exactOld => rfl

theorem rawGrouped_evidence_reflects481 (p : FullProblem) (m : I72.Model) (r : WhereSites450.OriginalCohorts451.SamePhase454.Report) :
    FlatEvidence p m (flattenRawGroupedReport r) ↔ WhereSites450.OriginalCohorts451.SamePhase454.ReportEvidence p m r := by
  cases r with
  | previous old => exact grouped_evidence_reflects481 p m old
  | rawGrouped exactOld => rfl

theorem fieldRecord_classification_reflects481 (p : FullProblem) (r : RoutedRecord455.Report) :
    FlatClassified p (flattenFieldRecordReport r) ↔ RoutedRecord455.ClassifiedAs p r := by
  cases r with
  | previous old => exact rawGrouped_classification_reflects481 p old
  | fieldK2 exactOld => rfl

theorem fieldRecord_evidence_reflects481 (p : FullProblem) (m : I72.Model) (r : RoutedRecord455.Report) :
    FlatEvidence p m (flattenFieldRecordReport r) ↔ RoutedRecord455.ReportEvidence p m r := by
  cases r with
  | previous old => exact rawGrouped_evidence_reflects481 p m old
  | fieldK2 exactOld => rfl

theorem fieldMixed_classification_reflects481 (p : FullProblem) (r : RoutedMixed456.Report) :
    FlatClassified p (flattenFieldMixedReport r) ↔ RoutedMixed456.ClassifiedAs p r := by
  cases r with
  | previous old => exact fieldRecord_classification_reflects481 p old
  | fieldK2 exactOld => rfl

theorem fieldMixed_evidence_reflects481 (p : FullProblem) (m : I72.Model) (r : RoutedMixed456.Report) :
    FlatEvidence p m (flattenFieldMixedReport r) ↔ RoutedMixed456.ReportEvidence p m r := by
  cases r with
  | previous old => exact fieldRecord_evidence_reflects481 p m old
  | fieldK2 exactOld => rfl

theorem fieldNominal_classification_reflects481 (p : FullProblem) (r : RoutedNominalMixed456.Report) :
    FlatClassified p (flattenFieldNominalReport r) ↔ RoutedNominalMixed456.ClassifiedAs p r := by
  cases r with
  | previous old => exact fieldMixed_classification_reflects481 p old
  | fieldK2 exactOld => rfl

theorem fieldNominal_evidence_reflects481 (p : FullProblem) (m : I72.Model) (r : RoutedNominalMixed456.Report) :
    FlatEvidence p m (flattenFieldNominalReport r) ↔ RoutedNominalMixed456.ReportEvidence p m r := by
  cases r with
  | previous old => exact fieldMixed_evidence_reflects481 p m old
  | fieldK2 exactOld => rfl

theorem fieldReadyRecord_classification_reflects481 (p : FullProblem) (r : RoutedReadyRecord457.Report) :
    FlatClassified p (flattenFieldReadyRecordReport r) ↔ RoutedReadyRecord457.ClassifiedAs p r := by
  cases r with
  | previous old => exact fieldNominal_classification_reflects481 p old
  | fieldK2 exactOld => rfl

theorem fieldReadyRecord_evidence_reflects481 (p : FullProblem) (m : I72.Model) (r : RoutedReadyRecord457.Report) :
    FlatEvidence p m (flattenFieldReadyRecordReport r) ↔ RoutedReadyRecord457.ReportEvidence p m r := by
  cases r with
  | previous old => exact fieldNominal_evidence_reflects481 p m old
  | fieldK2 exactOld => rfl

theorem fieldReadyMixed_classification_reflects481 (p : FullProblem) (r : RoutedReadyMixed457.Report) :
    FlatClassified p (flattenFieldReadyMixedReport r) ↔ RoutedReadyMixed457.ClassifiedAs p r := by
  cases r with
  | previous old => exact fieldReadyRecord_classification_reflects481 p old
  | fieldK2 exactOld => rfl

theorem fieldReadyMixed_evidence_reflects481 (p : FullProblem) (m : I72.Model) (r : RoutedReadyMixed457.Report) :
    FlatEvidence p m (flattenFieldReadyMixedReport r) ↔ RoutedReadyMixed457.ReportEvidence p m r := by
  cases r with
  | previous old => exact fieldReadyRecord_evidence_reflects481 p m old
  | fieldK2 exactOld => rfl

theorem fieldVariant_classification_reflects481 (p : FullProblem) (r : RoutedInlineVariant458.Report) :
    FlatClassified p (flattenFieldVariantReport r) ↔ RoutedInlineVariant458.ClassifiedAs p r := by
  cases r with
  | previous old => exact fieldReadyMixed_classification_reflects481 p old
  | fieldK2 exactOld => rfl

theorem fieldVariant_evidence_reflects481 (p : FullProblem) (m : I72.Model) (r : RoutedInlineVariant458.Report) :
    FlatEvidence p m (flattenFieldVariantReport r) ↔ RoutedInlineVariant458.ReportEvidence p m r := by
  cases r with
  | previous old => exact fieldReadyMixed_evidence_reflects481 p m old
  | fieldK2 exactOld => rfl

theorem fieldStructural_classification_reflects481 (p : FullProblem) (r : RoutedInlineStructural458.Report) :
    FlatClassified p (flattenFieldStructuralReport r) ↔ RoutedInlineStructural458.ClassifiedAs p r := by
  cases r with
  | previous old => exact fieldVariant_classification_reflects481 p old
  | fieldK2 exactOld => rfl

theorem fieldStructural_evidence_reflects481 (p : FullProblem) (m : I72.Model) (r : RoutedInlineStructural458.Report) :
    FlatEvidence p m (flattenFieldStructuralReport r) ↔ RoutedInlineStructural458.ReportEvidence p m r := by
  cases r with
  | previous old => exact fieldVariant_evidence_reflects481 p m old
  | fieldK2 exactOld => rfl

theorem fieldProjected_classification_reflects481 (p : FullProblem) (r : ProjectedClosedEntry459.Report) :
    FlatClassified p (flattenFieldProjectedReport r) ↔ ProjectedClosedEntry459.ClassifiedAs p r := by
  cases r with
  | previous old => exact fieldStructural_classification_reflects481 p old
  | fieldK2 exactOld => rfl

theorem fieldProjected_evidence_reflects481 (p : FullProblem) (m : I72.Model) (r : ProjectedClosedEntry459.Report) :
    FlatEvidence p m (flattenFieldProjectedReport r) ↔ ProjectedClosedEntry459.ReportEvidence p m r := by
  cases r with
  | previous old => exact fieldStructural_evidence_reflects481 p m old
  | fieldK2 exactOld => rfl

theorem fieldHomogeneous_classification_reflects481 (p : FullProblem) (r : HomogeneousClosedEntry459.Report) :
    FlatClassified p (flattenFieldHomogeneousReport r) ↔ HomogeneousClosedEntry459.ClassifiedAs p r := by
  cases r with
  | previous old => exact fieldProjected_classification_reflects481 p old
  | fieldK2 exactOld => rfl

theorem fieldHomogeneous_evidence_reflects481 (p : FullProblem) (m : I72.Model) (r : HomogeneousClosedEntry459.Report) :
    FlatEvidence p m (flattenFieldHomogeneousReport r) ↔ HomogeneousClosedEntry459.ReportEvidence p m r := by
  cases r with
  | previous old => exact fieldProjected_evidence_reflects481 p m old
  | fieldK2 exactOld => rfl

end Yulang.GeneralDeclarativeI65.I72.Flat481
