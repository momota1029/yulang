import Yulang.GeneralDeclarativeI65I74FlatLegacyCodec481

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Flat481
open RetainedFull445 (FullProblem)

def FlatReport.tier : FlatReport → Nat
  | .legacy _ _ => 0
  | .grouped _ => 1
  | .rawGrouped _ => 2
  | .fieldRecord _ => 3
  | .fieldMixed _ => 4
  | .fieldNominal _ => 5
  | .fieldReadyRecord _ => 6
  | .fieldReadyMixed _ => 7
  | .fieldVariant _ => 8
  | .fieldStructural _ => 9
  | .fieldProjected _ => 10
  | .fieldHomogeneous _ => 11

def FlatWitness.tier : FlatWitness → Nat
  | .legacy _ => 0
  | .grouped _ => 1
  | .rawGrouped _ => 2
  | .fieldRecord _ => 3
  | .fieldMixed _ => 4
  | .fieldNominal _ => 5
  | .fieldReadyRecord _ => 6
  | .fieldReadyMixed _ => 7
  | .fieldVariant _ => 8
  | .fieldStructural _ => 9
  | .fieldProjected _ => 10
  | .fieldHomogeneous _ => 11

theorem different_flat_tiers_return_false481 (p : FullProblem)
    (r : FlatReport) (w : FlatWitness) (different : r.tier ≠ w.tier) :
    check_full_flat p r w = false := by
  cases r <;> cases w <;> first | rfl | exact (different rfl).elim

private theorem below_next_tier_distinct481 {actual older : Nat} (limit : actual ≤ older) :
    actual ≠ older + 1 := by
  intro contradiction
  rw [contradiction] at limit
  exact Nat.not_succ_le_self older limit

def flattenGroupedReport : WhereSites450.OriginalCohorts451.GroupedEntry453.Report → FlatReport
  | .previous prior => .legacy .guardedWhere prior
  | .grouped report => .grouped report

def flattenGroupedWire : WhereSites450.OriginalCohorts451.GroupedEntry453.Witness → FlatWitness
  | .previous prior => .legacy (flattenGuardedWhere prior)
  | .grouped data => .grouped data

theorem grouped_report_tier481 (r : WhereSites450.OriginalCohorts451.GroupedEntry453.Report) :
    (flattenGroupedReport r).tier ≤ 1 := by
  cases r with
  | previous older => exact Nat.le_trans (Nat.le_refl 0) (by decide)
  | grouped data => exact Nat.le_refl _

theorem grouped_wire_tier481 (w : WhereSites450.OriginalCohorts451.GroupedEntry453.Witness) :
    (flattenGroupedWire w).tier ≤ 1 := by
  cases w with
  | previous older => exact Nat.le_trans (Nat.le_refl 0) (by decide)
  | grouped data => exact Nat.le_refl _

theorem grouped_same_Bool481 (p : FullProblem) (r : WhereSites450.OriginalCohorts451.GroupedEntry453.Report) (w : WhereSites450.OriginalCohorts451.GroupedEntry453.Witness) :
    check_full_flat p (flattenGroupedReport r) (flattenGroupedWire w) =
      WhereSites450.OriginalCohorts451.GroupedEntry453.check_full453 p r w := by
  cases r with
  | previous old =>
    cases w with
    | previous report => exact guardedWhere_same_Bool481 p old report
    | grouped fresh =>
      apply different_flat_tiers_return_false481
      exact below_next_tier_distinct481 (Nat.le_refl 0)
  | grouped newest =>
    cases w with
    | previous old =>
      apply different_flat_tiers_return_false481
      exact Ne.symm (below_next_tier_distinct481 (Nat.le_refl 0))
    | grouped fresh => rfl

def flattenRawGroupedReport : WhereSites450.OriginalCohorts451.SamePhase454.Report → FlatReport
  | .previous prior => flattenGroupedReport prior
  | .rawGrouped report => .rawGrouped report

def flattenRawGroupedWire : WhereSites450.OriginalCohorts451.SamePhase454.Witness → FlatWitness
  | .previous prior => flattenGroupedWire prior
  | .rawGrouped data => .rawGrouped data

theorem rawGrouped_report_tier481 (r : WhereSites450.OriginalCohorts451.SamePhase454.Report) :
    (flattenRawGroupedReport r).tier ≤ 2 := by
  cases r with
  | previous older => exact Nat.le_trans (grouped_report_tier481 older) (by decide)
  | rawGrouped data => exact Nat.le_refl _

theorem rawGrouped_wire_tier481 (w : WhereSites450.OriginalCohorts451.SamePhase454.Witness) :
    (flattenRawGroupedWire w).tier ≤ 2 := by
  cases w with
  | previous older => exact Nat.le_trans (grouped_wire_tier481 older) (by decide)
  | rawGrouped data => exact Nat.le_refl _

theorem rawGrouped_same_Bool481 (p : FullProblem) (r : WhereSites450.OriginalCohorts451.SamePhase454.Report) (w : WhereSites450.OriginalCohorts451.SamePhase454.Witness) :
    check_full_flat p (flattenRawGroupedReport r) (flattenRawGroupedWire w) =
      WhereSites450.OriginalCohorts451.SamePhase454.check_full454 p r w := by
  cases r with
  | previous old =>
    cases w with
    | previous report => exact grouped_same_Bool481 p old report
    | rawGrouped fresh =>
      apply different_flat_tiers_return_false481
      exact below_next_tier_distinct481 (grouped_report_tier481 old)
  | rawGrouped newest =>
    cases w with
    | previous old =>
      apply different_flat_tiers_return_false481
      exact Ne.symm (below_next_tier_distinct481 (grouped_wire_tier481 old))
    | rawGrouped fresh => rfl

def flattenFieldRecordReport : RoutedRecord455.Report → FlatReport
  | .previous prior => flattenRawGroupedReport prior
  | .fieldK2 report => .fieldRecord report

def flattenFieldRecordWire : RoutedRecord455.Witness → FlatWitness
  | .previous prior => flattenRawGroupedWire prior
  | .fieldK2 data => .fieldRecord data

theorem fieldRecord_report_tier481 (r : RoutedRecord455.Report) :
    (flattenFieldRecordReport r).tier ≤ 3 := by
  cases r with
  | previous older => exact Nat.le_trans (rawGrouped_report_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldRecord_wire_tier481 (w : RoutedRecord455.Witness) :
    (flattenFieldRecordWire w).tier ≤ 3 := by
  cases w with
  | previous older => exact Nat.le_trans (rawGrouped_wire_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldRecord_same_Bool481 (p : FullProblem) (r : RoutedRecord455.Report) (w : RoutedRecord455.Witness) :
    check_full_flat p (flattenFieldRecordReport r) (flattenFieldRecordWire w) =
      RoutedRecord455.check_full455 p r w := by
  cases r with
  | previous old =>
    cases w with
    | previous report => exact rawGrouped_same_Bool481 p old report
    | fieldK2 fresh =>
      apply different_flat_tiers_return_false481
      exact below_next_tier_distinct481 (rawGrouped_report_tier481 old)
  | fieldK2 newest =>
    cases w with
    | previous old =>
      apply different_flat_tiers_return_false481
      exact Ne.symm (below_next_tier_distinct481 (rawGrouped_wire_tier481 old))
    | fieldK2 fresh => rfl

def flattenFieldMixedReport : RoutedMixed456.Report → FlatReport
  | .previous prior => flattenFieldRecordReport prior
  | .fieldK2 report => .fieldMixed report

def flattenFieldMixedWire : RoutedMixed456.Witness → FlatWitness
  | .previous prior => flattenFieldRecordWire prior
  | .fieldK2 data => .fieldMixed data

theorem fieldMixed_report_tier481 (r : RoutedMixed456.Report) :
    (flattenFieldMixedReport r).tier ≤ 4 := by
  cases r with
  | previous older => exact Nat.le_trans (fieldRecord_report_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldMixed_wire_tier481 (w : RoutedMixed456.Witness) :
    (flattenFieldMixedWire w).tier ≤ 4 := by
  cases w with
  | previous older => exact Nat.le_trans (fieldRecord_wire_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldMixed_same_Bool481 (p : FullProblem) (r : RoutedMixed456.Report) (w : RoutedMixed456.Witness) :
    check_full_flat p (flattenFieldMixedReport r) (flattenFieldMixedWire w) =
      RoutedMixed456.check_full456 p r w := by
  cases r with
  | previous old =>
    cases w with
    | previous report => exact fieldRecord_same_Bool481 p old report
    | fieldK2 fresh =>
      apply different_flat_tiers_return_false481
      exact below_next_tier_distinct481 (fieldRecord_report_tier481 old)
  | fieldK2 newest =>
    cases w with
    | previous old =>
      apply different_flat_tiers_return_false481
      exact Ne.symm (below_next_tier_distinct481 (fieldRecord_wire_tier481 old))
    | fieldK2 fresh => rfl

def flattenFieldNominalReport : RoutedNominalMixed456.Report → FlatReport
  | .previous prior => flattenFieldMixedReport prior
  | .fieldK2 report => .fieldNominal report

def flattenFieldNominalWire : RoutedNominalMixed456.Witness → FlatWitness
  | .previous prior => flattenFieldMixedWire prior
  | .fieldK2 data => .fieldNominal data

theorem fieldNominal_report_tier481 (r : RoutedNominalMixed456.Report) :
    (flattenFieldNominalReport r).tier ≤ 5 := by
  cases r with
  | previous older => exact Nat.le_trans (fieldMixed_report_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldNominal_wire_tier481 (w : RoutedNominalMixed456.Witness) :
    (flattenFieldNominalWire w).tier ≤ 5 := by
  cases w with
  | previous older => exact Nat.le_trans (fieldMixed_wire_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldNominal_same_Bool481 (p : FullProblem) (r : RoutedNominalMixed456.Report) (w : RoutedNominalMixed456.Witness) :
    check_full_flat p (flattenFieldNominalReport r) (flattenFieldNominalWire w) =
      RoutedNominalMixed456.check_full_nominal456 p r w := by
  cases r with
  | previous old =>
    cases w with
    | previous report => exact fieldMixed_same_Bool481 p old report
    | fieldK2 fresh =>
      apply different_flat_tiers_return_false481
      exact below_next_tier_distinct481 (fieldMixed_report_tier481 old)
  | fieldK2 newest =>
    cases w with
    | previous old =>
      apply different_flat_tiers_return_false481
      exact Ne.symm (below_next_tier_distinct481 (fieldMixed_wire_tier481 old))
    | fieldK2 fresh => rfl

def flattenFieldReadyRecordReport : RoutedReadyRecord457.Report → FlatReport
  | .previous prior => flattenFieldNominalReport prior
  | .fieldK2 report => .fieldReadyRecord report

def flattenFieldReadyRecordWire : RoutedReadyRecord457.Witness → FlatWitness
  | .previous prior => flattenFieldNominalWire prior
  | .fieldK2 data => .fieldReadyRecord data

theorem fieldReadyRecord_report_tier481 (r : RoutedReadyRecord457.Report) :
    (flattenFieldReadyRecordReport r).tier ≤ 6 := by
  cases r with
  | previous older => exact Nat.le_trans (fieldNominal_report_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldReadyRecord_wire_tier481 (w : RoutedReadyRecord457.Witness) :
    (flattenFieldReadyRecordWire w).tier ≤ 6 := by
  cases w with
  | previous older => exact Nat.le_trans (fieldNominal_wire_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldReadyRecord_same_Bool481 (p : FullProblem) (r : RoutedReadyRecord457.Report) (w : RoutedReadyRecord457.Witness) :
    check_full_flat p (flattenFieldReadyRecordReport r) (flattenFieldReadyRecordWire w) =
      RoutedReadyRecord457.check_full457 p r w := by
  cases r with
  | previous old =>
    cases w with
    | previous report => exact fieldNominal_same_Bool481 p old report
    | fieldK2 fresh =>
      apply different_flat_tiers_return_false481
      exact below_next_tier_distinct481 (fieldNominal_report_tier481 old)
  | fieldK2 newest =>
    cases w with
    | previous old =>
      apply different_flat_tiers_return_false481
      exact Ne.symm (below_next_tier_distinct481 (fieldNominal_wire_tier481 old))
    | fieldK2 fresh => rfl

def flattenFieldReadyMixedReport : RoutedReadyMixed457.Report → FlatReport
  | .previous prior => flattenFieldReadyRecordReport prior
  | .fieldK2 report => .fieldReadyMixed report

def flattenFieldReadyMixedWire : RoutedReadyMixed457.Witness → FlatWitness
  | .previous prior => flattenFieldReadyRecordWire prior
  | .fieldK2 data => .fieldReadyMixed data

theorem fieldReadyMixed_report_tier481 (r : RoutedReadyMixed457.Report) :
    (flattenFieldReadyMixedReport r).tier ≤ 7 := by
  cases r with
  | previous older => exact Nat.le_trans (fieldReadyRecord_report_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldReadyMixed_wire_tier481 (w : RoutedReadyMixed457.Witness) :
    (flattenFieldReadyMixedWire w).tier ≤ 7 := by
  cases w with
  | previous older => exact Nat.le_trans (fieldReadyRecord_wire_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldReadyMixed_same_Bool481 (p : FullProblem) (r : RoutedReadyMixed457.Report) (w : RoutedReadyMixed457.Witness) :
    check_full_flat p (flattenFieldReadyMixedReport r) (flattenFieldReadyMixedWire w) =
      RoutedReadyMixed457.check_full_ready_mixed457 p r w := by
  cases r with
  | previous old =>
    cases w with
    | previous report => exact fieldReadyRecord_same_Bool481 p old report
    | fieldK2 fresh =>
      apply different_flat_tiers_return_false481
      exact below_next_tier_distinct481 (fieldReadyRecord_report_tier481 old)
  | fieldK2 newest =>
    cases w with
    | previous old =>
      apply different_flat_tiers_return_false481
      exact Ne.symm (below_next_tier_distinct481 (fieldReadyRecord_wire_tier481 old))
    | fieldK2 fresh => rfl

def flattenFieldVariantReport : RoutedInlineVariant458.Report → FlatReport
  | .previous prior => flattenFieldReadyMixedReport prior
  | .fieldK2 report => .fieldVariant report

def flattenFieldVariantWire : RoutedInlineVariant458.Witness → FlatWitness
  | .previous prior => flattenFieldReadyMixedWire prior
  | .fieldK2 data => .fieldVariant data

theorem fieldVariant_report_tier481 (r : RoutedInlineVariant458.Report) :
    (flattenFieldVariantReport r).tier ≤ 8 := by
  cases r with
  | previous older => exact Nat.le_trans (fieldReadyMixed_report_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldVariant_wire_tier481 (w : RoutedInlineVariant458.Witness) :
    (flattenFieldVariantWire w).tier ≤ 8 := by
  cases w with
  | previous older => exact Nat.le_trans (fieldReadyMixed_wire_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldVariant_same_Bool481 (p : FullProblem) (r : RoutedInlineVariant458.Report) (w : RoutedInlineVariant458.Witness) :
    check_full_flat p (flattenFieldVariantReport r) (flattenFieldVariantWire w) =
      RoutedInlineVariant458.check_full458 p r w := by
  cases r with
  | previous old =>
    cases w with
    | previous report => exact fieldReadyMixed_same_Bool481 p old report
    | fieldK2 fresh =>
      apply different_flat_tiers_return_false481
      exact below_next_tier_distinct481 (fieldReadyMixed_report_tier481 old)
  | fieldK2 newest =>
    cases w with
    | previous old =>
      apply different_flat_tiers_return_false481
      exact Ne.symm (below_next_tier_distinct481 (fieldReadyMixed_wire_tier481 old))
    | fieldK2 fresh => rfl

def flattenFieldStructuralReport : RoutedInlineStructural458.Report → FlatReport
  | .previous prior => flattenFieldVariantReport prior
  | .fieldK2 report => .fieldStructural report

def flattenFieldStructuralWire : RoutedInlineStructural458.Witness → FlatWitness
  | .previous prior => flattenFieldVariantWire prior
  | .fieldK2 data => .fieldStructural data

theorem fieldStructural_report_tier481 (r : RoutedInlineStructural458.Report) :
    (flattenFieldStructuralReport r).tier ≤ 9 := by
  cases r with
  | previous older => exact Nat.le_trans (fieldVariant_report_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldStructural_wire_tier481 (w : RoutedInlineStructural458.Witness) :
    (flattenFieldStructuralWire w).tier ≤ 9 := by
  cases w with
  | previous older => exact Nat.le_trans (fieldVariant_wire_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldStructural_same_Bool481 (p : FullProblem) (r : RoutedInlineStructural458.Report) (w : RoutedInlineStructural458.Witness) :
    check_full_flat p (flattenFieldStructuralReport r) (flattenFieldStructuralWire w) =
      RoutedInlineStructural458.check_full_structural458 p r w := by
  cases r with
  | previous old =>
    cases w with
    | previous report => exact fieldVariant_same_Bool481 p old report
    | fieldK2 fresh =>
      apply different_flat_tiers_return_false481
      exact below_next_tier_distinct481 (fieldVariant_report_tier481 old)
  | fieldK2 newest =>
    cases w with
    | previous old =>
      apply different_flat_tiers_return_false481
      exact Ne.symm (below_next_tier_distinct481 (fieldVariant_wire_tier481 old))
    | fieldK2 fresh => exact (InstalledProtocolSum462.same_plain_field_bool p.old newest fresh).symm

def flattenFieldProjectedReport : ProjectedClosedEntry459.Report → FlatReport
  | .previous prior => flattenFieldStructuralReport prior
  | .fieldK2 report => .fieldProjected report

def flattenFieldProjectedWire : ProjectedClosedEntry459.Witness → FlatWitness
  | .previous prior => flattenFieldStructuralWire prior
  | .fieldK2 data => .fieldProjected data

theorem fieldProjected_report_tier481 (r : ProjectedClosedEntry459.Report) :
    (flattenFieldProjectedReport r).tier ≤ 10 := by
  cases r with
  | previous older => exact Nat.le_trans (fieldStructural_report_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldProjected_wire_tier481 (w : ProjectedClosedEntry459.Witness) :
    (flattenFieldProjectedWire w).tier ≤ 10 := by
  cases w with
  | previous older => exact Nat.le_trans (fieldStructural_wire_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldProjected_same_Bool481 (p : FullProblem) (r : ProjectedClosedEntry459.Report) (w : ProjectedClosedEntry459.Witness) :
    check_full_flat p (flattenFieldProjectedReport r) (flattenFieldProjectedWire w) =
      ProjectedClosedEntry459.check_full_projected459 p r w := by
  cases r with
  | previous old =>
    cases w with
    | previous report => exact fieldStructural_same_Bool481 p old report
    | fieldK2 fresh =>
      apply different_flat_tiers_return_false481
      exact below_next_tier_distinct481 (fieldStructural_report_tier481 old)
  | fieldK2 newest =>
    cases w with
    | previous old =>
      apply different_flat_tiers_return_false481
      exact Ne.symm (below_next_tier_distinct481 (fieldStructural_wire_tier481 old))
    | fieldK2 fresh => exact (InstalledProtocolSum462.same_projected_field_bool p.old newest fresh).symm

def flattenFieldHomogeneousReport : HomogeneousClosedEntry459.Report → FlatReport
  | .previous prior => flattenFieldProjectedReport prior
  | .fieldK2 report => .fieldHomogeneous report

def flattenFieldHomogeneousWire : HomogeneousClosedEntry459.Witness → FlatWitness
  | .previous prior => flattenFieldProjectedWire prior
  | .fieldK2 data => .fieldHomogeneous data

theorem fieldHomogeneous_report_tier481 (r : HomogeneousClosedEntry459.Report) :
    (flattenFieldHomogeneousReport r).tier ≤ 11 := by
  cases r with
  | previous older => exact Nat.le_trans (fieldProjected_report_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldHomogeneous_wire_tier481 (w : HomogeneousClosedEntry459.Witness) :
    (flattenFieldHomogeneousWire w).tier ≤ 11 := by
  cases w with
  | previous older => exact Nat.le_trans (fieldProjected_wire_tier481 older) (by decide)
  | fieldK2 data => exact Nat.le_refl _

theorem fieldHomogeneous_same_Bool481 (p : FullProblem) (r : HomogeneousClosedEntry459.Report) (w : HomogeneousClosedEntry459.Witness) :
    check_full_flat p (flattenFieldHomogeneousReport r) (flattenFieldHomogeneousWire w) =
      HomogeneousClosedEntry459.check_full_homogeneous459 p r w := by
  cases r with
  | previous old =>
    cases w with
    | previous report => exact fieldProjected_same_Bool481 p old report
    | fieldK2 fresh =>
      apply different_flat_tiers_return_false481
      exact below_next_tier_distinct481 (fieldProjected_report_tier481 old)
  | fieldK2 newest =>
    cases w with
    | previous old =>
      apply different_flat_tiers_return_false481
      exact Ne.symm (below_next_tier_distinct481 (fieldProjected_wire_tier481 old))
    | fieldK2 fresh => exact (InstalledProtocolSum462.same_homogeneous_field_bool p.old newest fresh).symm

end Yulang.GeneralDeclarativeI65.I72.Flat481
