import Yulang.GeneralNominalSourceAggregate256
import Yulang.GeneralNominalHistoricalAggregate256
namespace Yulang.GeneralNominalFrameAggregate256
open Core.PresenceGeneration GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalAllocation GeneralNominalRecursiveInspection
open GeneralNominalHistoricalAggregate256
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

abbrev pairs (plan : GeneralNominalCenters.Plan roles) (name : Nat) :=
 occurrences plan.packet.bindings name

theorem nonempty (frame : GeneralNominalVersionedEvidence231.Frame registry state root key plan)
 (name : Nat) (named : name ∈ plan.packet.declaration.inputNames) : pairs plan name ≠ [] :=
 GeneralNominalInputOccurrences256.frame_nonempty frame name named

/-- No empty-aggregate exception can block a declared input of a real frame. -/
theorem prepare_iff (frame : GeneralNominalVersionedEvidence231.Frame registry state root key plan)
 (name : Nat) (named : name ∈ plan.packet.declaration.inputNames)
 (pool : List (TyTerm Nat)) (old : List (Entry Nat))
 (result : GeneralNominalRebaseProjectionView243.Bounds) :
 prepare pool old (pairs plan name) = some result ↔
 EndpointSupported pool old (pairs plan name) ∧ result = rewrite pool old (pairs plan name) := by
 rw [prepare_exact]
 exact and_iff_right (nonempty frame name named)

/-- This discharges support from initial source endpoint membership; no
hypothesis that the desired aggregate lies in the basis is added. -/
theorem identity_supported (frame : GeneralNominalVersionedEvidence231.Frame registry state root key plan)
 (keys : List (Nat × Nat)) (name : Nat) (named : name ∈ plan.packet.declaration.inputNames) :
 EndpointSupported (GeneralNominalCanonicalBasis255.basis registry plan.packet.context keys) [] (pairs plan name) := by
 apply (supported_iff _ [] (pairs plan name) (nonempty frame name named)).mpr
 exact ⟨GeneralNominalSourceAggregate256.report_lower registry plan.packet.context keys
   plan.packet.declaration plan.packet.bounds (GeneralNominalInputOccurrences256.frame_finished frame) name named,
   GeneralNominalSourceAggregate256.report_upper registry plan.packet.context keys
   plan.packet.declaration plan.packet.bounds (GeneralNominalInputOccurrences256.frame_finished frame) name named⟩

theorem identity_prepared (frame : GeneralNominalVersionedEvidence231.Frame registry state root key plan)
 (keys : List (Nat × Nat)) (name : Nat) (named : name ∈ plan.packet.declaration.inputNames) :
 prepare (GeneralNominalCanonicalBasis255.basis registry plan.packet.context keys) [] (pairs plan name) =
 some (rewrite (GeneralNominalCanonicalBasis255.basis registry plan.packet.context keys) [] (pairs plan name)) :=
 (prepare_iff frame name named _ [] _).mpr ⟨identity_supported frame keys name named,rfl⟩

theorem identity_fits (frame : GeneralNominalVersionedEvidence231.Frame registry state root key plan)
 (keys : List (Nat × Nat)) (name : Nat) (named : name ∈ plan.packet.declaration.inputNames)
 (assignment : Assignment) (actual : Ty) :
 (rewrite (GeneralNominalCanonicalBasis255.basis registry plan.packet.context keys) [] (pairs plan name)).Fits assignment actual ↔
 ∀ pair ∈ pairs plan name, GeneralNominalCaptureMerges.Fits assignment pair actual :=
 fits_exact _ [] _ _ (identity_prepared frame keys name named) assignment actual
end Yulang.GeneralNominalFrameAggregate256
