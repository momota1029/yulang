import Yulang.GeneralNominalRolePacketCongruence251
import Yulang.GeneralNominalStableRoleHead251
namespace Yulang.GeneralNominalStableRolePacket251
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralNominalOwnerOpening250 (Handle)
open GeneralNominalAllocation (Bindings)
open GeneralNominalRebaseProjectionView243 (Bounds)
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDependence247
open CommonNominalFullCarrier

def compile (plan : GeneralNominalCenters.Plan roles) (frame : Frame) (handle : Handle)
 (fallback : Nat → Bounds) (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) : GeneralNominalRebasePacketView243.Packet :=
 GeneralNominalRolePacket251.compile plan
   (GeneralNominalStableRoleEnvironment251.compile frame handle plan.packet.bindings fallback binders targets)

theorem generated_exact (plan : GeneralNominalCenters.Plan roles) (frame : Frame) (safe : SafeOrder frame.definitions)
 (handle : Handle)
 (within : TargetsWithin (GeneralNominalRebaseDefinitions241.entries handle.seed handle.root handle.declaration plan.packet.bindings handle.names) frame.definitions)
 (fallback : Nat → Bounds) (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) (assignment : Assignment) :
 (compile plan frame handle fallback binders targets).Holds
   (GeneralNominalStableCaptureStep250.next frame handle plan.packet.bindings assignment) ↔
 GeneralNominalRolePacket251.Holds plan
   (GeneralNominalStableRoleEnvironment251.compile frame handle plan.packet.bindings fallback binders targets)
   (GeneralNominalStableRoleHead251.reference handle plan.packet.bindings fallback binders targets
     (solve model frame.definitions assignment) (GeneralNominalStableCaptureStep250.next frame handle plan.packet.bindings assignment))
   (GeneralNominalStableCaptureStep250.next frame handle plan.packet.bindings assignment) :=
 (GeneralNominalRolePacket251.compile_exact ..).trans
   (GeneralNominalRolePacketCongruence251.packet_related
     (GeneralNominalStableRoleHead251.generated_related frame safe handle plan.packet.bindings within fallback binders targets assignment) plan _ _)

def delta (plan : GeneralNominalCenters.Plan roles) (frame : Frame) (handle : Handle)
 (fallback : Nat → Bounds) (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) : GeneralNominalJournalAppend250.Delta :=
 ⟨[],[],[compile plan frame handle fallback binders targets],[],[]⟩

theorem delta_exact (plan : GeneralNominalCenters.Plan roles) (frame : Frame) (handle : Handle)
 (fallback : Nat → Bounds) (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) (assignment : Assignment) :
 (delta plan frame handle fallback binders targets).Holds assignment ↔
 (compile plan frame handle fallback binders targets).Holds assignment := by
 simp [delta,GeneralNominalJournalAppend250.Delta.Holds,PresenceNormalForm.All]

def command (plan : GeneralNominalCenters.Plan roles) (frame : Frame) (handle : Handle)
 (fallback : Nat → Bounds) (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) : GeneralNominalFiniteInstallTrace250.Command :=
 ⟨GeneralNominalRebaseDefinitions241.entries handle.seed handle.root handle.declaration plan.packet.bindings handle.names,
 delta plan frame handle fallback binders targets⟩

theorem install_exact (plan : GeneralNominalCenters.Plan roles) (frame : Frame) (safe : SafeOrder frame.definitions)
 (handle : Handle)
 (within : TargetsWithin (GeneralNominalRebaseDefinitions241.entries handle.seed handle.root handle.declaration plan.packet.bindings handle.names) frame.definitions)
 (fallback : Nat → Bounds) (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) (assignment : Assignment)
 (oldValid : Models frame assignment) :
 Models (GeneralNominalFiniteInstallTrace250.advance frame (command plan frame handle fallback binders targets))
   (GeneralNominalStableCaptureStep250.next frame handle plan.packet.bindings assignment) ↔
 GeneralNominalRolePacket251.Holds plan
   (GeneralNominalStableRoleEnvironment251.compile frame handle plan.packet.bindings fallback binders targets)
   (GeneralNominalStableRoleHead251.reference handle plan.packet.bindings fallback binders targets
     (solve model frame.definitions assignment) (GeneralNominalStableCaptureStep250.next frame handle plan.packet.bindings assignment))
   (GeneralNominalStableCaptureStep250.next frame handle plan.packet.bindings assignment) := by
 have preserved := GeneralNominalArbitraryOwnerFrame250.models_forward frame _
   (GeneralNominalPersistentOwner250.safe_update frame safe
     (GeneralNominalRebaseDefinitions241.entries handle.seed handle.root handle.declaration plan.packet.bindings handle.names))
   (GeneralNominalMaterializedSequenceModels249.same_domain_protected frame _ safe (GeneralPresencePersistentSnapshot250.refresh_within _ _)) assignment oldValid
 change Models (GeneralNominalJournalAppend250.attach _ (delta plan frame handle fallback binders targets)) _ ↔ _
 rw [GeneralNominalJournalAppend250.attach_models,delta_exact]
 exact (and_iff_right preserved).trans (generated_exact plan frame safe handle within fallback binders targets assignment)
end Yulang.GeneralNominalStableRolePacket251
