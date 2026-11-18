import Yulang.GeneralNominalStableCapture250
import Yulang.GeneralNominalInstallCoverage250
import Yulang.GeneralNominalSchemaCongruence238
/-! The computed snapshot update itself supplies all aggregate equations.
Consequently its compiled bounds describe exactly the old occurrence intervals,
not just values in a separately assumed fresh model. -/
namespace Yulang.GeneralNominalStableCaptureStep250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterializedOwnerFrame249 (Frame)
open GeneralNominalOwnerOpening250 (Handle)
open GeneralNominalAllocation (Bindings occurrences)
open GeneralNominalRebaseDefinitions241 (entries)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedDependence247
open GeneralNominalStableCapture250 (bounds)
open CommonNominalFullCarrier GeneralPresenceCommonLaws245

def next (frame : Frame) (handle : Handle) (bindings : Bindings) (assignment : Assignment) : Assignment :=
 solve model (GeneralNominalPersistentOwner250.update frame
   (entries handle.seed handle.root handle.declaration bindings handle.names)).definitions assignment

theorem generated_equations (frame : Frame) (safe : SafeOrder frame.definitions) (handle : Handle) (bindings : Bindings)
 (within : TargetsWithin (entries handle.seed handle.root handle.declaration bindings handle.names) frame.definitions)
 (assignment : Assignment) :
 All model (next frame handle bindings assignment) (block (transform
   (GeneralPresenceOrderedSubstitution247.mapping frame.definitions)
   (entries handle.seed handle.root handle.declaration bindings handle.names))) :=
 GeneralPresencePersistentSnapshot250.raw_equations _ _ within
   (GeneralNominalRebaseDefinitions241.coherent handle.seed handle.root handle.declaration bindings handle.names) model _
   (block_satisfied model subtype_refl _ (GeneralNominalPersistentOwner250.safe_update frame safe _) assignment)

theorem snapshot_bounds_exact (frame : Frame) (safe : SafeOrder frame.definitions) (handle : Handle) (bindings : Bindings)
 (within : TargetsWithin (entries handle.seed handle.root handle.declaration bindings handle.names) frame.definitions)
 (assignment : Assignment) (name : Nat) (named : name ∈ handle.names)
 (nonempty : occurrences bindings name ≠ []) (actual : Ty) :
 (bounds frame handle bindings name).Fits (next frame handle bindings assignment) actual ↔
 ∀ original ∈ occurrences bindings name, GeneralNominalCaptureMerges.Fits (solve model frame.definitions assignment) original actual := by
 have exactBounds := GeneralNominalStableCapture250.bounds_exact frame handle bindings _
   (generated_equations frame safe handle bindings within assignment) name named nonempty actual
 have absorbs := solve_absorbs model frame.definitions
   (GeneralNominalPersistentOwner250.update frame (entries handle.seed handle.root handle.declaration bindings handle.names)).definitions
   safe (GeneralPresencePersistentSnapshot250.refresh_within _ _) assignment
 change solve model frame.definitions (next frame handle bindings assignment) = _ at absorbs
 rw [absorbs] at exactBounds
 exact exactBounds

theorem actual_bounds_exact (frame : Frame) (safe : SafeOrder frame.definitions) (handle : Handle) (bindings : Bindings)
 (within : TargetsWithin (entries handle.seed handle.root handle.declaration bindings handle.names) frame.definitions)
 (assignment : Assignment) (oldValid : All model assignment (block frame.definitions))
 (name : Nat) (named : name ∈ handle.names) (nonempty : occurrences bindings name ≠ []) (actual : Ty) :
 (bounds frame handle bindings name).Fits (next frame handle bindings assignment) actual ↔
 ∀ original ∈ occurrences bindings name, GeneralNominalCaptureMerges.Fits assignment original actual := by
 apply (snapshot_bounds_exact frame safe handle bindings within assignment name named nonempty actual).trans
 apply forall_congr'; intro original
 apply forall_congr'; intro member
 exact GeneralNominalSchemaCongruence238.fits_iff
   (GeneralPresenceOrderedRecovery247.solve_compatible model common_laws frame.definitions assignment oldValid)
   ⟨subtype_refl actual,subtype_refl actual⟩ original
end Yulang.GeneralNominalStableCaptureStep250
