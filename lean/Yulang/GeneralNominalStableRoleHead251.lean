import Yulang.GeneralNominalStableRoleEnvironment251
namespace Yulang.GeneralNominalStableRoleHead251
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRoleEnvironment251
open GeneralNominalMaterializedOwnerFrame249 (Frame)
open GeneralNominalOwnerOpening250 (Handle)
open GeneralNominalAllocation (Bindings occurrences lower upper)
open GeneralNominalRebaseProjectionView243 (Bounds)
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDependence247
open CommonNominalFullCarrier

noncomputable def reference (handle : Handle) (bindings : Bindings) (fallback : Nat → Bounds)
 (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) (old current : Assignment) : Values :=
 ⟨old,
 fun name => if name ∈ handle.names then (lower (occurrences bindings name)).eval model old else (fallback name).lower.eval model current,
 fun name => if name ∈ handle.names then (upper (occurrences bindings name)).eval model old else (fallback name).upper.eval model current,
 fun name => (binders name).eval model current,GeneralNominalRebaseRawView243.read targets current⟩

theorem generated_related (frame : Frame) (safe : SafeOrder frame.definitions) (handle : Handle) (bindings : Bindings)
 (within : TargetsWithin (GeneralNominalRebaseDefinitions241.entries handle.seed handle.root handle.declaration bindings handle.names) frame.definitions)
 (fallback : Nat → Bounds) (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) (assignment : Assignment) :
 Related (read (GeneralNominalStableRoleEnvironment251.compile frame handle bindings fallback binders targets)
   (GeneralNominalStableCaptureStep250.next frame handle bindings assignment))
 (reference handle bindings fallback binders targets (solve model frame.definitions assignment)
   (GeneralNominalStableCaptureStep250.next frame handle bindings assignment)) := by
 have related := GeneralNominalStableRoleEnvironment251.generated_related frame safe handle bindings within fallback binders targets assignment
 have absorbs := GeneralPresenceOrderedDependence247.solve_absorbs model frame.definitions
   (GeneralNominalPersistentOwner250.update frame (GeneralNominalRebaseDefinitions241.entries handle.seed handle.root handle.declaration bindings handle.names)).definitions
   safe (GeneralPresencePersistentSnapshot250.refresh_within _ _) assignment
 change solve model frame.definitions (GeneralNominalStableCaptureStep250.next frame handle bindings assignment) = _ at absorbs
 unfold GeneralNominalStableRoleEnvironment251.values at related
 rw [absorbs] at related
 exact related

theorem head_exact (frame : Frame) (safe : SafeOrder frame.definitions) (handle : Handle) (bindings : Bindings)
 (within : TargetsWithin (GeneralNominalRebaseDefinitions241.entries handle.seed handle.root handle.declaration bindings handle.names) frame.definitions)
 (fallback : Nat → Bounds) (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) (assignment : Assignment)
 (outputs : List Nat) (schema : GeneralNominalMaterialization.Schema) :
 (GeneralNominalRoleSchema251.compile outputs
   (GeneralNominalStableRoleEnvironment251.compile frame handle bindings fallback binders targets) schema).Holds
   (GeneralNominalStableCaptureStep250.next frame handle bindings assignment) ↔
 GeneralNominalRoleSchema251.Holds outputs schema
   (reference handle bindings fallback binders targets (solve model frame.definitions assignment)
     (GeneralNominalStableCaptureStep250.next frame handle bindings assignment)) :=
 (GeneralNominalRoleSchema251.compile_exact ..).trans
   (GeneralNominalRoleSchema251.holds_related (generated_related frame safe handle bindings within fallback binders targets assignment) outputs schema)

theorem equations_exact (frame : Frame) (safe : SafeOrder frame.definitions) (handle : Handle) (bindings : Bindings)
 (within : TargetsWithin (GeneralNominalRebaseDefinitions241.entries handle.seed handle.root handle.declaration bindings handle.names) frame.definitions)
 (fallback : Nat → Bounds) (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) (assignment : Assignment)
 (outputs : List Nat) (schema : GeneralNominalCenteredHeadMatSchemas.Schema) :
 GeneralNominalRebasePacketView243.AllEquations
   (GeneralNominalRoleEquations251.compile outputs
     (GeneralNominalStableRoleEnvironment251.compile frame handle bindings fallback binders targets) schema)
   (GeneralNominalStableCaptureStep250.next frame handle bindings assignment) ↔
 schema.Holds ((reference handle bindings fallback binders targets (solve model frame.definitions assignment)
   (GeneralNominalStableCaptureStep250.next frame handle bindings assignment)).variables outputs)
   (GeneralNominalRebaseRawView243.read targets (GeneralNominalStableCaptureStep250.next frame handle bindings assignment)) := by
 exact (GeneralNominalRoleEquations251.compile_exact ..).trans
   (GeneralNominalRoleEquations251.schema_related (generated_related frame safe handle bindings within fallback binders targets assignment) outputs schema)
end Yulang.GeneralNominalStableRoleHead251
