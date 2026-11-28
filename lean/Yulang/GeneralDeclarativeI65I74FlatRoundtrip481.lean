import Yulang.GeneralDeclarativeI65I74FlatSound481

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Flat481
open Checker408 (Result)

def unflattenLegacyReport (scope : LegacyScope) : FlatReport → Option Result
  | .legacy found r => if found = scope then some r else none
  | _ => none

theorem legacy_report_roundtrip481 (s : LegacyScope) (r : Result) :
    unflattenLegacyReport s (.legacy s r) = some r := by
  simp [unflattenLegacyReport]

private theorem next_tag_is_not_a_previous_tier481 {a b : Nat} (none : a ≤ b) :
    a ≠ b + 1 := by
  intro same
  rw [same] at none
  exact Nat.not_succ_le_self b none

def unflattenRetained (data : LegacyWire) : Option RetainedSplit446.Witness446 :=
  match data with
  | .retained w => some w
  | _ => none

theorem retained_wire_roundtrip481 (w : RetainedSplit446.Witness446) :
    unflattenRetained (flattenRetained w) = some w := by
  rfl

def unflattenSelected (data : LegacyWire) : Option RetainedSplit446.SelectedReplay447.Witness447 :=
  if data.scope.rank = 1 then
    match data with
    | .selected w => some (.localSplitOutput w)
    | _ => none
  else (unflattenRetained data).map .previous

theorem selected_wire_roundtrip481 (w : RetainedSplit446.SelectedReplay447.Witness447) :
    unflattenSelected (flattenSelected w) = some w := by
  cases w with
  | previous old =>
    simp only [flattenSelected]
    have distinct : (flattenRetained old).scope.rank ≠ 1 :=
      next_tag_is_not_a_previous_tier481 (retained_scope481 old)
    change (if (flattenRetained old).scope.rank = 1 then _ else _) = _
    rw [ite_eq_right distinct,retained_wire_roundtrip481 old]
    rfl
  | localSplitOutput data => rfl

def unflattenOpaque (data : LegacyWire) : Option Opaque448.Witness448 :=
  if data.scope.rank = 2 then
    match data with
    | .opaque w => some (.opaqueName w)
    | _ => none
  else (unflattenSelected data).map .previous

theorem opaque_wire_roundtrip481 (w : Opaque448.Witness448) :
    unflattenOpaque (flattenOpaque w) = some w := by
  cases w with
  | previous old =>
    simp only [flattenOpaque]
    have distinct : (flattenSelected old).scope.rank ≠ 2 :=
      next_tag_is_not_a_previous_tier481 (selected_scope481 old)
    change (if (flattenSelected old).scope.rank = 2 then _ else _) = _
    rw [ite_eq_right distinct,selected_wire_roundtrip481 old]
    rfl
  | opaqueName data => rfl

def unflattenWhole (data : LegacyWire) : Option Opaque448.Whole.Witness :=
  if data.scope.rank = 3 then
    match data with
    | .whole w => some (.wholeBare w)
    | _ => none
  else (unflattenOpaque data).map .previous

theorem whole_wire_roundtrip481 (w : Opaque448.Whole.Witness) :
    unflattenWhole (flattenWhole w) = some w := by
  cases w with
  | previous old =>
    simp only [flattenWhole]
    have distinct : (flattenOpaque old).scope.rank ≠ 3 :=
      next_tag_is_not_a_previous_tier481 (opaque_scope481 old)
    change (if (flattenOpaque old).scope.rank = 3 then _ else _) = _
    rw [ite_eq_right distinct,opaque_wire_roundtrip481 old]
    rfl
  | wholeBare data => rfl

def unflattenListSite (data : LegacyWire) : Option ListSites449.Witness :=
  if data.scope.rank = 4 then
    match data with
    | .listSite w => some (.inspectedList w)
    | _ => none
  else (unflattenWhole data).map .previous

theorem listSite_wire_roundtrip481 (w : ListSites449.Witness) :
    unflattenListSite (flattenListSite w) = some w := by
  cases w with
  | previous old =>
    simp only [flattenListSite]
    have distinct : (flattenWhole old).scope.rank ≠ 4 :=
      next_tag_is_not_a_previous_tier481 (whole_scope481 old)
    change (if (flattenWhole old).scope.rank = 4 then _ else _) = _
    rw [ite_eq_right distinct,whole_wire_roundtrip481 old]
    rfl
  | inspectedList data => rfl

def unflattenListFrame (data : LegacyWire) : Option ListSites449.Frame.Witness :=
  if data.scope.rank = 5 then
    match data with
    | .listFrame w => some (.inspectedFrame w)
    | _ => none
  else (unflattenListSite data).map .previous

theorem listFrame_wire_roundtrip481 (w : ListSites449.Frame.Witness) :
    unflattenListFrame (flattenListFrame w) = some w := by
  cases w with
  | previous old =>
    simp only [flattenListFrame]
    have distinct : (flattenListSite old).scope.rank ≠ 5 :=
      next_tag_is_not_a_previous_tier481 (listSite_scope481 old)
    change (if (flattenListSite old).scope.rank = 5 then _ else _) = _
    rw [ite_eq_right distinct,listSite_wire_roundtrip481 old]
    rfl
  | inspectedFrame data => rfl

def unflattenGuardedWhere (data : LegacyWire) : Option WhereSites450.Witness :=
  if data.scope.rank = 6 then
    match data with
    | .guardedWhere w => some (.whereRoot w)
    | _ => none
  else (unflattenListFrame data).map .previous

theorem guardedWhere_wire_roundtrip481 (w : WhereSites450.Witness) :
    unflattenGuardedWhere (flattenGuardedWhere w) = some w := by
  cases w with
  | previous old =>
    simp only [flattenGuardedWhere]
    have distinct : (flattenListFrame old).scope.rank ≠ 6 :=
      next_tag_is_not_a_previous_tier481 (listFrame_scope481 old)
    change (if (flattenListFrame old).scope.rank = 6 then _ else _) = _
    rw [ite_eq_right distinct,listFrame_wire_roundtrip481 old]
    rfl
  | whereRoot data => rfl

def unflattenLegacyGuardedWhere : FlatWitness → Option WhereSites450.Witness
  | .legacy w => unflattenGuardedWhere w
  | _ => none

theorem guardedWhere_flat_wire_roundtrip481 (old : WhereSites450.Witness) :
    unflattenLegacyGuardedWhere (.legacy (flattenGuardedWhere old)) = some old :=
  guardedWhere_wire_roundtrip481 old

def unflattenGroupedReport (r : FlatReport) : Option WhereSites450.OriginalCohorts451.GroupedEntry453.Report :=
  if r.tier = 1 then
    match r with
    | .grouped own => some (.grouped own)
    | _ => none
  else (unflattenLegacyReport .guardedWhere r).map .previous

theorem grouped_report_roundtrip481 (old : WhereSites450.OriginalCohorts451.GroupedEntry453.Report) :
    unflattenGroupedReport (flattenGroupedReport old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenGroupedReport]
    have distinct : (.legacy .guardedWhere old : FlatReport).tier ≠ 1 :=
      next_tag_is_not_a_previous_tier481 (Nat.le_refl 0)
    have round : unflattenLegacyReport .guardedWhere (.legacy .guardedWhere old) = some old := legacy_report_roundtrip481 .guardedWhere old
    change (if (.legacy .guardedWhere old : FlatReport).tier = 1 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | grouped data => rfl

def unflattenGroupedWire (r : FlatWitness) : Option WhereSites450.OriginalCohorts451.GroupedEntry453.Witness :=
  if r.tier = 1 then
    match r with
    | .grouped own => some (.grouped own)
    | _ => none
  else (unflattenLegacyGuardedWhere r).map .previous

theorem grouped_wire_roundtrip481 (old : WhereSites450.OriginalCohorts451.GroupedEntry453.Witness) :
    unflattenGroupedWire (flattenGroupedWire old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenGroupedWire]
    have distinct : (.legacy (flattenGuardedWhere old) : FlatWitness).tier ≠ 1 :=
      next_tag_is_not_a_previous_tier481 (Nat.le_refl 0)
    have round : unflattenLegacyGuardedWhere (.legacy (flattenGuardedWhere old)) = some old := guardedWhere_flat_wire_roundtrip481 old
    change (if (.legacy (flattenGuardedWhere old) : FlatWitness).tier = 1 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | grouped data => rfl

def unflattenRawGroupedReport (r : FlatReport) : Option WhereSites450.OriginalCohorts451.SamePhase454.Report :=
  if r.tier = 2 then
    match r with
    | .rawGrouped own => some (.rawGrouped own)
    | _ => none
  else (unflattenGroupedReport r).map .previous

theorem rawGrouped_report_roundtrip481 (old : WhereSites450.OriginalCohorts451.SamePhase454.Report) :
    unflattenRawGroupedReport (flattenRawGroupedReport old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenRawGroupedReport]
    have distinct : (flattenGroupedReport old : FlatReport).tier ≠ 2 :=
      next_tag_is_not_a_previous_tier481 (grouped_report_tier481 old)
    have round : unflattenGroupedReport (flattenGroupedReport old) = some old := grouped_report_roundtrip481 old
    change (if (flattenGroupedReport old : FlatReport).tier = 2 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | rawGrouped data => rfl

def unflattenRawGroupedWire (r : FlatWitness) : Option WhereSites450.OriginalCohorts451.SamePhase454.Witness :=
  if r.tier = 2 then
    match r with
    | .rawGrouped own => some (.rawGrouped own)
    | _ => none
  else (unflattenGroupedWire r).map .previous

theorem rawGrouped_wire_roundtrip481 (old : WhereSites450.OriginalCohorts451.SamePhase454.Witness) :
    unflattenRawGroupedWire (flattenRawGroupedWire old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenRawGroupedWire]
    have distinct : (flattenGroupedWire old : FlatWitness).tier ≠ 2 :=
      next_tag_is_not_a_previous_tier481 (grouped_wire_tier481 old)
    have round : unflattenGroupedWire (flattenGroupedWire old) = some old := grouped_wire_roundtrip481 old
    change (if (flattenGroupedWire old : FlatWitness).tier = 2 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | rawGrouped data => rfl

def unflattenFieldRecordReport (r : FlatReport) : Option RoutedRecord455.Report :=
  if r.tier = 3 then
    match r with
    | .fieldRecord own => some (.fieldK2 own)
    | _ => none
  else (unflattenRawGroupedReport r).map .previous

theorem fieldRecord_report_roundtrip481 (old : RoutedRecord455.Report) :
    unflattenFieldRecordReport (flattenFieldRecordReport old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldRecordReport]
    have distinct : (flattenRawGroupedReport old : FlatReport).tier ≠ 3 :=
      next_tag_is_not_a_previous_tier481 (rawGrouped_report_tier481 old)
    have round : unflattenRawGroupedReport (flattenRawGroupedReport old) = some old := rawGrouped_report_roundtrip481 old
    change (if (flattenRawGroupedReport old : FlatReport).tier = 3 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldRecordWire (r : FlatWitness) : Option RoutedRecord455.Witness :=
  if r.tier = 3 then
    match r with
    | .fieldRecord own => some (.fieldK2 own)
    | _ => none
  else (unflattenRawGroupedWire r).map .previous

theorem fieldRecord_wire_roundtrip481 (old : RoutedRecord455.Witness) :
    unflattenFieldRecordWire (flattenFieldRecordWire old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldRecordWire]
    have distinct : (flattenRawGroupedWire old : FlatWitness).tier ≠ 3 :=
      next_tag_is_not_a_previous_tier481 (rawGrouped_wire_tier481 old)
    have round : unflattenRawGroupedWire (flattenRawGroupedWire old) = some old := rawGrouped_wire_roundtrip481 old
    change (if (flattenRawGroupedWire old : FlatWitness).tier = 3 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldMixedReport (r : FlatReport) : Option RoutedMixed456.Report :=
  if r.tier = 4 then
    match r with
    | .fieldMixed own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldRecordReport r).map .previous

theorem fieldMixed_report_roundtrip481 (old : RoutedMixed456.Report) :
    unflattenFieldMixedReport (flattenFieldMixedReport old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldMixedReport]
    have distinct : (flattenFieldRecordReport old : FlatReport).tier ≠ 4 :=
      next_tag_is_not_a_previous_tier481 (fieldRecord_report_tier481 old)
    have round : unflattenFieldRecordReport (flattenFieldRecordReport old) = some old := fieldRecord_report_roundtrip481 old
    change (if (flattenFieldRecordReport old : FlatReport).tier = 4 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldMixedWire (r : FlatWitness) : Option RoutedMixed456.Witness :=
  if r.tier = 4 then
    match r with
    | .fieldMixed own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldRecordWire r).map .previous

theorem fieldMixed_wire_roundtrip481 (old : RoutedMixed456.Witness) :
    unflattenFieldMixedWire (flattenFieldMixedWire old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldMixedWire]
    have distinct : (flattenFieldRecordWire old : FlatWitness).tier ≠ 4 :=
      next_tag_is_not_a_previous_tier481 (fieldRecord_wire_tier481 old)
    have round : unflattenFieldRecordWire (flattenFieldRecordWire old) = some old := fieldRecord_wire_roundtrip481 old
    change (if (flattenFieldRecordWire old : FlatWitness).tier = 4 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldNominalReport (r : FlatReport) : Option RoutedNominalMixed456.Report :=
  if r.tier = 5 then
    match r with
    | .fieldNominal own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldMixedReport r).map .previous

theorem fieldNominal_report_roundtrip481 (old : RoutedNominalMixed456.Report) :
    unflattenFieldNominalReport (flattenFieldNominalReport old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldNominalReport]
    have distinct : (flattenFieldMixedReport old : FlatReport).tier ≠ 5 :=
      next_tag_is_not_a_previous_tier481 (fieldMixed_report_tier481 old)
    have round : unflattenFieldMixedReport (flattenFieldMixedReport old) = some old := fieldMixed_report_roundtrip481 old
    change (if (flattenFieldMixedReport old : FlatReport).tier = 5 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldNominalWire (r : FlatWitness) : Option RoutedNominalMixed456.Witness :=
  if r.tier = 5 then
    match r with
    | .fieldNominal own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldMixedWire r).map .previous

theorem fieldNominal_wire_roundtrip481 (old : RoutedNominalMixed456.Witness) :
    unflattenFieldNominalWire (flattenFieldNominalWire old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldNominalWire]
    have distinct : (flattenFieldMixedWire old : FlatWitness).tier ≠ 5 :=
      next_tag_is_not_a_previous_tier481 (fieldMixed_wire_tier481 old)
    have round : unflattenFieldMixedWire (flattenFieldMixedWire old) = some old := fieldMixed_wire_roundtrip481 old
    change (if (flattenFieldMixedWire old : FlatWitness).tier = 5 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldReadyRecordReport (r : FlatReport) : Option RoutedReadyRecord457.Report :=
  if r.tier = 6 then
    match r with
    | .fieldReadyRecord own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldNominalReport r).map .previous

theorem fieldReadyRecord_report_roundtrip481 (old : RoutedReadyRecord457.Report) :
    unflattenFieldReadyRecordReport (flattenFieldReadyRecordReport old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldReadyRecordReport]
    have distinct : (flattenFieldNominalReport old : FlatReport).tier ≠ 6 :=
      next_tag_is_not_a_previous_tier481 (fieldNominal_report_tier481 old)
    have round : unflattenFieldNominalReport (flattenFieldNominalReport old) = some old := fieldNominal_report_roundtrip481 old
    change (if (flattenFieldNominalReport old : FlatReport).tier = 6 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldReadyRecordWire (r : FlatWitness) : Option RoutedReadyRecord457.Witness :=
  if r.tier = 6 then
    match r with
    | .fieldReadyRecord own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldNominalWire r).map .previous

theorem fieldReadyRecord_wire_roundtrip481 (old : RoutedReadyRecord457.Witness) :
    unflattenFieldReadyRecordWire (flattenFieldReadyRecordWire old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldReadyRecordWire]
    have distinct : (flattenFieldNominalWire old : FlatWitness).tier ≠ 6 :=
      next_tag_is_not_a_previous_tier481 (fieldNominal_wire_tier481 old)
    have round : unflattenFieldNominalWire (flattenFieldNominalWire old) = some old := fieldNominal_wire_roundtrip481 old
    change (if (flattenFieldNominalWire old : FlatWitness).tier = 6 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldReadyMixedReport (r : FlatReport) : Option RoutedReadyMixed457.Report :=
  if r.tier = 7 then
    match r with
    | .fieldReadyMixed own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldReadyRecordReport r).map .previous

theorem fieldReadyMixed_report_roundtrip481 (old : RoutedReadyMixed457.Report) :
    unflattenFieldReadyMixedReport (flattenFieldReadyMixedReport old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldReadyMixedReport]
    have distinct : (flattenFieldReadyRecordReport old : FlatReport).tier ≠ 7 :=
      next_tag_is_not_a_previous_tier481 (fieldReadyRecord_report_tier481 old)
    have round : unflattenFieldReadyRecordReport (flattenFieldReadyRecordReport old) = some old := fieldReadyRecord_report_roundtrip481 old
    change (if (flattenFieldReadyRecordReport old : FlatReport).tier = 7 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldReadyMixedWire (r : FlatWitness) : Option RoutedReadyMixed457.Witness :=
  if r.tier = 7 then
    match r with
    | .fieldReadyMixed own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldReadyRecordWire r).map .previous

theorem fieldReadyMixed_wire_roundtrip481 (old : RoutedReadyMixed457.Witness) :
    unflattenFieldReadyMixedWire (flattenFieldReadyMixedWire old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldReadyMixedWire]
    have distinct : (flattenFieldReadyRecordWire old : FlatWitness).tier ≠ 7 :=
      next_tag_is_not_a_previous_tier481 (fieldReadyRecord_wire_tier481 old)
    have round : unflattenFieldReadyRecordWire (flattenFieldReadyRecordWire old) = some old := fieldReadyRecord_wire_roundtrip481 old
    change (if (flattenFieldReadyRecordWire old : FlatWitness).tier = 7 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldVariantReport (r : FlatReport) : Option RoutedInlineVariant458.Report :=
  if r.tier = 8 then
    match r with
    | .fieldVariant own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldReadyMixedReport r).map .previous

theorem fieldVariant_report_roundtrip481 (old : RoutedInlineVariant458.Report) :
    unflattenFieldVariantReport (flattenFieldVariantReport old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldVariantReport]
    have distinct : (flattenFieldReadyMixedReport old : FlatReport).tier ≠ 8 :=
      next_tag_is_not_a_previous_tier481 (fieldReadyMixed_report_tier481 old)
    have round : unflattenFieldReadyMixedReport (flattenFieldReadyMixedReport old) = some old := fieldReadyMixed_report_roundtrip481 old
    change (if (flattenFieldReadyMixedReport old : FlatReport).tier = 8 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldVariantWire (r : FlatWitness) : Option RoutedInlineVariant458.Witness :=
  if r.tier = 8 then
    match r with
    | .fieldVariant own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldReadyMixedWire r).map .previous

theorem fieldVariant_wire_roundtrip481 (old : RoutedInlineVariant458.Witness) :
    unflattenFieldVariantWire (flattenFieldVariantWire old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldVariantWire]
    have distinct : (flattenFieldReadyMixedWire old : FlatWitness).tier ≠ 8 :=
      next_tag_is_not_a_previous_tier481 (fieldReadyMixed_wire_tier481 old)
    have round : unflattenFieldReadyMixedWire (flattenFieldReadyMixedWire old) = some old := fieldReadyMixed_wire_roundtrip481 old
    change (if (flattenFieldReadyMixedWire old : FlatWitness).tier = 8 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldStructuralReport (r : FlatReport) : Option RoutedInlineStructural458.Report :=
  if r.tier = 9 then
    match r with
    | .fieldStructural own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldVariantReport r).map .previous

theorem fieldStructural_report_roundtrip481 (old : RoutedInlineStructural458.Report) :
    unflattenFieldStructuralReport (flattenFieldStructuralReport old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldStructuralReport]
    have distinct : (flattenFieldVariantReport old : FlatReport).tier ≠ 9 :=
      next_tag_is_not_a_previous_tier481 (fieldVariant_report_tier481 old)
    have round : unflattenFieldVariantReport (flattenFieldVariantReport old) = some old := fieldVariant_report_roundtrip481 old
    change (if (flattenFieldVariantReport old : FlatReport).tier = 9 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldStructuralWire (r : FlatWitness) : Option RoutedInlineStructural458.Witness :=
  if r.tier = 9 then
    match r with
    | .fieldStructural own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldVariantWire r).map .previous

theorem fieldStructural_wire_roundtrip481 (old : RoutedInlineStructural458.Witness) :
    unflattenFieldStructuralWire (flattenFieldStructuralWire old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldStructuralWire]
    have distinct : (flattenFieldVariantWire old : FlatWitness).tier ≠ 9 :=
      next_tag_is_not_a_previous_tier481 (fieldVariant_wire_tier481 old)
    have round : unflattenFieldVariantWire (flattenFieldVariantWire old) = some old := fieldVariant_wire_roundtrip481 old
    change (if (flattenFieldVariantWire old : FlatWitness).tier = 9 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldProjectedReport (r : FlatReport) : Option ProjectedClosedEntry459.Report :=
  if r.tier = 10 then
    match r with
    | .fieldProjected own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldStructuralReport r).map .previous

theorem fieldProjected_report_roundtrip481 (old : ProjectedClosedEntry459.Report) :
    unflattenFieldProjectedReport (flattenFieldProjectedReport old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldProjectedReport]
    have distinct : (flattenFieldStructuralReport old : FlatReport).tier ≠ 10 :=
      next_tag_is_not_a_previous_tier481 (fieldStructural_report_tier481 old)
    have round : unflattenFieldStructuralReport (flattenFieldStructuralReport old) = some old := fieldStructural_report_roundtrip481 old
    change (if (flattenFieldStructuralReport old : FlatReport).tier = 10 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldProjectedWire (r : FlatWitness) : Option ProjectedClosedEntry459.Witness :=
  if r.tier = 10 then
    match r with
    | .fieldProjected own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldStructuralWire r).map .previous

theorem fieldProjected_wire_roundtrip481 (old : ProjectedClosedEntry459.Witness) :
    unflattenFieldProjectedWire (flattenFieldProjectedWire old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldProjectedWire]
    have distinct : (flattenFieldStructuralWire old : FlatWitness).tier ≠ 10 :=
      next_tag_is_not_a_previous_tier481 (fieldStructural_wire_tier481 old)
    have round : unflattenFieldStructuralWire (flattenFieldStructuralWire old) = some old := fieldStructural_wire_roundtrip481 old
    change (if (flattenFieldStructuralWire old : FlatWitness).tier = 10 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldHomogeneousReport (r : FlatReport) : Option HomogeneousClosedEntry459.Report :=
  if r.tier = 11 then
    match r with
    | .fieldHomogeneous own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldProjectedReport r).map .previous

theorem fieldHomogeneous_report_roundtrip481 (old : HomogeneousClosedEntry459.Report) :
    unflattenFieldHomogeneousReport (flattenFieldHomogeneousReport old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldHomogeneousReport]
    have distinct : (flattenFieldProjectedReport old : FlatReport).tier ≠ 11 :=
      next_tag_is_not_a_previous_tier481 (fieldProjected_report_tier481 old)
    have round : unflattenFieldProjectedReport (flattenFieldProjectedReport old) = some old := fieldProjected_report_roundtrip481 old
    change (if (flattenFieldProjectedReport old : FlatReport).tier = 11 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

def unflattenFieldHomogeneousWire (r : FlatWitness) : Option HomogeneousClosedEntry459.Witness :=
  if r.tier = 11 then
    match r with
    | .fieldHomogeneous own => some (.fieldK2 own)
    | _ => none
  else (unflattenFieldProjectedWire r).map .previous

theorem fieldHomogeneous_wire_roundtrip481 (old : HomogeneousClosedEntry459.Witness) :
    unflattenFieldHomogeneousWire (flattenFieldHomogeneousWire old) = some old := by
  cases old with
  | previous old =>
    simp only [flattenFieldHomogeneousWire]
    have distinct : (flattenFieldProjectedWire old : FlatWitness).tier ≠ 11 :=
      next_tag_is_not_a_previous_tier481 (fieldProjected_wire_tier481 old)
    have round : unflattenFieldProjectedWire (flattenFieldProjectedWire old) = some old := fieldProjected_wire_roundtrip481 old
    change (if (flattenFieldProjectedWire old : FlatWitness).tier = 11 then _ else _) = _
    rw [ite_eq_right distinct]
    rw [round]
    rfl
  | fieldK2 data => rfl

end Yulang.GeneralDeclarativeI65.I72.Flat481
