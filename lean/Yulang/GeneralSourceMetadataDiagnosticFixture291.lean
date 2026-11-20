import Yulang.GeneralSourceMetadataDiagnostics291

/-! A candidate row layout can be known and valid metadata but fail only
for an actual attempt to materialize it, including in an unused default. -/
namespace Yulang.GeneralSourceMetadataDiagnosticFixture291
open GeneralRebaseRowChildSource287 (registry interp constructors)
open GeneralSourceMetadataDiagnostics291 (Failure diagnostics)
open GeneralSourceMetadataRoleFixture291 (registryWithDefault withDefault)
open GeneralSourceMetadataRoleManifest291 (manifestRows)
open GeneralSourceMetadataProblem291 (Problem problem)
open GeneralSourceMetadataValidation291 (check)
open GeneralSourceMetadataFixture291 (incompatible)
open GeneralSourceMetadataRows291 (interpretation)

theorem actual_source_failure :
    diagnostics (registry true) interp [] = [] ∧
    diagnostics (registry false) interp [] = [⟨⟨.head 1,(6,1)⟩,.unsupportedNominalLayout⟩] := by
  decide +kernel

theorem actual_default_failure :
    diagnostics (registryWithDefault 0) interp (manifestRows (withDefault 0)) = [] ∧
    diagnostics (registryWithDefault 6) interp (manifestRows (withDefault 6)) =
      [⟨⟨.roleDefault 17 0,(6,1)⟩,.unsupportedNominalLayout⟩] := by
  decide +kernel

theorem diagnostic_kinds :
    problem (fun _ => none) interp (7,0) = some .unknownConstructor ∧
    problem constructors interp (0,0) = some (.wrongArity 1) ∧
    problem constructors interp (1,1) = some .missingClassification ∧
    problem (GeneralSourceMetadataRows291.constructors incompatible) (interpretation incompatible) (9,1) =
      some .primitiveLayout := by
  decide +kernel

end Yulang.GeneralSourceMetadataDiagnosticFixture291
