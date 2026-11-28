import Yulang.GeneralDeclarativeI65I74InstalledSameBoolean462

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Flat481
open RetainedFull445
open Checker408 (Result)
open SplitEscape446
open MixedFixed442

/-- Former untagged Result envelopes are kept explicit: their
declarative domains are not all the same. -/
inductive LegacyScope where
  | retained
  | selected
  | opaque
  | whole
  | listSite
  | listFrame
  | guardedWhere
  deriving DecidableEq

def LegacyScope.rank : LegacyScope → Nat
  | .retained => 0
  | .selected => 1
  | .opaque => 2
  | .whole => 3
  | .listSite => 4
  | .listFrame => 5
  | .guardedWhere => 6

inductive LegacyWire where
  | retained (w : RetainedSplit446.Witness446)
  | selected (w : RefPositions441.Wire)
  | opaque (w : Opaque448.NamedWire)
  | whole (w : Opaque448.NamedWire)
  | listSite (w : ListSites449.Wire)
  | listFrame (w : ListSites449.Frame.FrameWire)
  | guardedWhere (w : WhereSites450.WhereWire)

def LegacyWire.scope : LegacyWire → LegacyScope
  | .retained _ => .retained
  | .selected _ => .selected
  | .opaque _ => .opaque
  | .whole _ => .whole
  | .listSite _ => .listSite
  | .listFrame _ => .listFrame
  | .guardedWhere _ => .guardedWhere

inductive FlatReport where
  | legacy (scope : LegacyScope) (report : Result)
  | grouped (r : WhereSites450.OriginalCohorts451.GroupedEntry453.GroupedReport)
  | rawGrouped (r : WhereSites450.OriginalCohorts451.GroupedEntry453.GroupedReport)
  | fieldRecord (r : RecordTrail455.FieldReport)
  | fieldMixed (r : RoutedMixed456.MixedReport)
  | fieldNominal (r : RoutedMixed456.MixedReport)
  | fieldReadyRecord (r : RoutedReadyRecord457.FieldReport)
  | fieldReadyMixed (r : RoutedReadyMixed457.ReportAtField)
  | fieldVariant (r : RoutedReadyMixed457.ReportAtField)
  | fieldStructural (r : RoutedReadyMixed457.ReportAtField)
  | fieldProjected (r : RoutedReadyMixed457.ReportAtField)
  | fieldHomogeneous (r : RoutedReadyMixed457.ReportAtField)

inductive FlatWitness where
  | legacy (w : LegacyWire)
  | grouped (w : WhereSites450.OriginalCohorts451.LiteralAndInternal452.ScopedLiteralInput)
  | rawGrouped (w : WhereSites450.OriginalCohorts451.SourceDiagnosticWire)
  | fieldRecord (w : RoutedRecord455.FieldWire)
  | fieldMixed (w : RoutedMixed456.FieldWire)
  | fieldNominal (w : RoutedMixed456.FieldWire)
  | fieldReadyRecord (w : RoutedRecord455.FieldWire)
  | fieldReadyMixed (w : RoutedMixed456.FieldWire)
  | fieldVariant (w : RoutedInlineVariant458.FieldWire)
  | fieldStructural (w : RoutedInlineStructural458.FieldWire)
  | fieldProjected (w : ProjectedClosedEntry459.FieldWire)
  | fieldHomogeneous (w : HomogeneousClosedEntry459.FieldWire)

/-- The previous entry chain is absent here except for the expressly
retained C446 base. The old guarded leaf conditions are unchanged. -/
def checkLegacy (p : FullProblem) (r : Result) : LegacyWire → Bool
  | .retained w => RetainedSplit446.check_full446 p r w
  | .selected w => match RetainedSplit446.SelectedReplay447.readLocalSource p.old w with
    | none => false
    | some source => matchesSelection p source && WhereAssociated432.matchesAssociatedReport432 r (sourceReport source)
  | .opaque w => match scope : visible p.state.base.core p.root with
    | [d] => (Opaque448.readOpaque p.old d scope w).isSome &&
      Check408.matchesNoWrites r (.selected d.id []) (.selected (.node d.id []))
    | _ => false
  | .whole w => match Opaque448.Roster.readWholeChoice p.old w with
    | none => false
    | some derived =>
      Check408.matchesNoWrites r (.selected derived.picked.id []) (.selected (.node derived.picked.id []))
  | .listSite w => match scope : visible p.state.base.core p.root with
    | [d] => (ListSites449.readListSites p.old d scope w).isSome &&
      Check408.matchesNoWrites r (.selected d.id []) (.selected (.node d.id []))
    | _ => false
  | .listFrame w => match scope : visible p.state.base.core p.root with
    | [d] => (ListSites449.Frame.readListFrameChoice p.old d scope w).isSome &&
      Check408.matchesNoWrites r (.selected d.id []) (.selected (.node d.id []))
    | _ => false
  | .guardedWhere w => WhereSites450.NoSiblingMerge.noSiblingMerge p &&
    (match whole : visible p.state.base.core p.root with
    | [d] =>
      match WhereSites450.readParentChoice p.old d whole w.parent with
      | none => false
      | some read =>
        let parent : WhereSites450.ParentSelection p.old := ⟨d,read⟩
        match WhereSites450.readOrdered p.state.base parent.children w.children with
        | none => false
        | some ⟨trees,_⟩ => WhereSites450.hasRawRejection trees &&
            Check408.matchesNoWrites r (.selected d.id trees) .rejected
    | _ => false)

def check_full_flat (p : FullProblem) : FlatReport → FlatWitness → Bool
  | .legacy scope r, .legacy w => decide (w.scope.rank ≤ scope.rank) && checkLegacy p r w
  | .grouped r, .grouped w => WhereSites450.OriginalCohorts451.GroupedEntry453.checkGrouped453 p r w
  | .rawGrouped r, .rawGrouped w => WhereSites450.OriginalCohorts451.SamePhase454.check p r w
  | .fieldRecord r, .fieldRecord w => RoutedRecord455.checkField p.old r w
  | .fieldMixed r, .fieldMixed w => RoutedMixed456.checkField p.old r w
  | .fieldNominal r, .fieldNominal w => RoutedNominalMixed456.checkField p.old r w
  | .fieldReadyRecord r, .fieldReadyRecord w => RoutedReadyRecord457.checkField p.old r w
  | .fieldReadyMixed r, .fieldReadyMixed w => RoutedReadyMixed457.checkField p.old r w
  | .fieldVariant r, .fieldVariant w => RoutedInlineVariant458.checkField p.old r w
  | .fieldStructural r, .fieldStructural w => InstalledProtocolSum462.checkSameField p.old .plain w.emptyKey w.cursor r
  | .fieldProjected r, .fieldProjected w => InstalledProtocolSum462.checkSameField p.old .projected w.emptyKey w.cursor r
  | .fieldHomogeneous r, .fieldHomogeneous w => InstalledProtocolSum462.checkSameField p.old .homogeneous w.emptyKey w.cursor r
  | _,_ => false

end Yulang.GeneralDeclarativeI65.I72.Flat481
