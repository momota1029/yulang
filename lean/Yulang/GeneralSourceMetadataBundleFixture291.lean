import Yulang.GeneralSourceMetadataBundle291

/-! A closed export and attachment to both existing fixture worlds.
Unsupported source materialization does not bar every old raw transition. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralSourceMetadataBundleFixture291
open GeneralSourceMetadataBundle291 (SourceBundle Certificate Attached inspect ready_exact)
open GeneralSourceMetadataFixture291 (source source_interpretation source_constructors)
open GeneralSourceMetadataRoleFixture291 (fixture actual_role_table)
open GeneralSourceMetadataComparison291 (compare)
open GeneralSourceMetadataValidation291 (check)
open GeneralRebaseRowChildSource287 (registry ctx interp before root roles)
open GeneralRebaseRowParentFrame287 (after)
open GeneralNominalCenteredHeadWFSource (Coverage)

abbrev actual (choice : Bool) : SourceBundle :=
  ⟨source,source,fixture,(registry choice).declarations⟩

theorem attached_actual (choice : Bool) : Attached (actual choice) (registry choice) ctx :=
  ⟨⟨source_constructors.symm,source_constructors.symm,source_interpretation.symm⟩,actual_role_table,rfl⟩

theorem executable_both (choice : Bool) : (inspect (actual choice)).ready = choice := by
  cases choice <;> decide +kernel

theorem executable_false_only_unsupported :
    let cert := inspect (actual false)
    cert.declarationsValid = true ∧ cert.snapshotValid = true ∧ cert.roleKeysValid = true ∧
    cert.tables = .compared .good ∧
    cert.unsupported = [⟨⟨.head 1,(6,1)⟩,.unsupportedNominalLayout⟩] := by decide +kernel

theorem original_declared_valid_both (choice : Bool) : GeneralDeclarations.Checked (registry choice) :=
  GeneralRebaseRowChildSource287.checked choice

theorem outside_coverage_still_installs :
    (inspect (actual false)).ready = false ∧ ¬ Coverage (registry false) interp ∧
      GeneralNominalVersionedMixedKernel234.Step (registry false) root before (after false) :=
  ⟨executable_both false,GeneralSourceMetadataCoverageFixture291.same_metadata_different_coverage.2.2.2,
    GeneralRebaseRowParentStep287.actual_step false⟩

abbrev noFallback : GeneralSourceMetadataRows291.Source := { source with fallback := .absent }

theorem different_defaults_control :
    compare source noFallback [6,0] = .fallbackMismatch 7 ∧
    GeneralSourceMetadataRows291.constructors source 7 = some ⟨[],7⟩ ∧
    GeneralSourceMetadataRows291.constructors noFallback 7 = none := by
  constructor
  · decide +kernel
  · exact ⟨rfl,rfl⟩

abbrev reordered : GeneralSourceMetadataRows291.Source := { source with rows := source.rows.reverse }

theorem source_order_control :
    check reordered = true ∧ compare source reordered [6,0] = .compared .good := by decide +kernel

end Yulang.GeneralSourceMetadataBundleFixture291
