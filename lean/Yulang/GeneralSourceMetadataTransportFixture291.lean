import Yulang.GeneralSourceMetadataContextTransfer291

/-! The parent report is unchanged under an unused key edit, but an
observed classifier change can alter it even with same table, Models
and old global Metadata. The view is not an alternate executed journal. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
namespace Yulang.GeneralSourceMetadataTransportFixture291
open GeneralRebaseRowChildSource287 (raw ctx registry interp parentDecl)
open GeneralSourceMetadataRows291 (Source constructors constructorRows interpretation)
open GeneralSourceMetadataSnapshot291 (context check check_exact)
open GeneralSourceMetadataFixture291 (source source_constructors)
open GeneralSourceMetadataSnapshotFixture291 (outside outside_fits)
open GeneralSourceMetadataContextTransfer291 (checked_report_transport)
open GeneralSourceMetadataReport291 (lower)
open GeneralNominalRecursiveCandidates (report)
open GeneralNominalInspection (Bounds)
open GeneralObservedMetadataOverlay290 (overlay)
open GeneralObservedMetadataKeys290 (headKeys)
open GeneralObservedMetadataEntry290 (agree)
open GeneralNominalCandidates (Metadata)

abbrev bounds : List (Bounds raw) := [(1,1)]
abbrev outsideFit := (check_exact raw outside).mp outside_fits

theorem outside_is_local_match :
    agree (headKeys parentDecl) raw.constructors interp (constructors outside) (interpretation outside) =
      true := by decide +kernel

theorem outside_report_unchanged :
    lower raw outside outsideFit (report (context raw outside outsideFit) parentDecl bounds) =
      report ctx parentDecl bounds :=
  checked_report_transport ctx outside outsideFit parentDecl bounds outside_is_local_match

abbrev turnOff : Source :=
  { source with rows := ⟨0,some ⟨[.type],0⟩,.unclassified⟩ ::
      source.rows.filter (fun r => r.key != 0) }

theorem owned_layout_still_valid : check raw turnOff = true := by decide +kernel
abbrev turnFit := (check_exact raw turnOff).mp owned_layout_still_valid

theorem same_constructor_table : constructors turnOff = constructors source := by
  funext key
  simp [constructors,constructorRows,overlay]

theorem old_metadata_unchanged : Metadata (registry true) (context raw turnOff turnFit) := by
  refine ⟨source_constructors.symm.trans same_constructor_table.symm,?_⟩
  change GeneralCandidateInspection.PrimitivesCompatible
    GeneralRebaseRowChildSource287.constructors (interpretation turnOff).primitives
  rw [← source_constructors,← same_constructor_table]
  exact GeneralSourceMetadataValidation291.checked_primitive turnOff (by decide +kernel)

theorem changed_classifier_changes_report :
    (report ctx parentDecl bounds).blocked = [] ∧
    (report (context raw turnOff turnFit) parentDecl bounds).blocked = bounds := by
  decide +kernel

theorem view_has_different_report :
    lower raw turnOff turnFit (report (context raw turnOff turnFit) parentDecl bounds) ≠ report ctx parentDecl bounds := by
  intro conflated
  have blocked := congrArg GeneralNominalRecursiveInspection.Report.blocked conflated
  change (report (context raw turnOff turnFit) parentDecl bounds).blocked =
    (report ctx parentDecl bounds).blocked at blocked
  rw [changed_classifier_changes_report.1,changed_classifier_changes_report.2] at blocked
  cases blocked

end Yulang.GeneralSourceMetadataTransportFixture291
