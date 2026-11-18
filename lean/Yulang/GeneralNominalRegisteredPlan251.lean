import Yulang.GeneralNominalPlanProducer251
import Yulang.GeneralNominalRegistryInvariant250
namespace Yulang.GeneralNominalRegisteredPlan251
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCenters (Plan)
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralNominalOwnerOpening250 (Handle)
open GeneralNominalOwnerRegistry250 (Registered lookup)
open GeneralNominalFiniteInstallTrace250 (Command advance)
open GeneralPresenceOrderedDependence247 (TargetsWithin)
open GeneralPresenceOwnerRewrite244 (Coherent)
open GeneralPresenceOrderedBlock247

def Matches (plan : Plan roles) (handle : Handle) : Prop :=
 handle.root = plan.packet.site.occurrence.identity ∧ handle.declaration = plan.packet.declaration.id ∧
 handle.names = plan.packet.declaration.inputNames

def build (plan : Plan roles) (frame : Frame) (handle : Handle) : Command :=
 GeneralNominalStableRolePacket251.command plan frame handle (GeneralNominalPlanProducer251.fallback plan frame)
   (GeneralNominalRoleBinder251.compile plan frame CompTerm.var) CompTerm.var

def compile (plan : Plan roles) (frame : Frame) (handles : List Handle) : Option (Handle × Command) :=
 (lookup handles plan.packet.site.occurrence.identity plan.packet.declaration.id).bind fun handle =>
 if handle.names = plan.packet.declaration.inputNames then some (handle,build plan frame handle) else none

theorem compile_exact (plan : Plan roles) (frame : Frame) (handles : List Handle) (handle : Handle) (command : Command)
 (success : compile plan frame handles = some (handle,command)) :
 handle ∈ handles ∧ Matches plan handle ∧ command = build plan frame handle := by
 unfold compile at success
 cases found : lookup handles plan.packet.site.occurrence.identity plan.packet.declaration.id with
 | none => simp [found] at success
 | some chosen =>
   simp only [found,Option.bind_some] at success
   split at success
   · rename_i names
     have equal := Option.some.inj success
     have pair := Prod.mk.inj equal
     obtain ⟨rfl,rfl⟩ := pair
     have fields := GeneralNominalRegistryInvariant250.lookup_fields handles _ _ chosen found
     exact ⟨fields.2.2,⟨fields.1,fields.2.1,names⟩,rfl⟩
   · simp at success

theorem compile_success (plan : Plan roles) (frame : Frame) (handles : List Handle) (handle : Handle)
 (found : lookup handles plan.packet.site.occurrence.identity plan.packet.declaration.id = some handle)
 (names : handle.names = plan.packet.declaration.inputNames) :
 compile plan frame handles = some (handle,build plan frame handle) := by simp [compile,found,names]

theorem covered (plan : Plan roles) (frame : Frame) (handles : List Handle) (registered : Registered frame handles)
 (handle : Handle) (command : Command) (success : compile plan frame handles = some (handle,command)) :
 TargetsWithin command.raw frame.definitions ∧ Coherent command.raw := by
 obtain ⟨member,_,rfl⟩ := compile_exact plan frame handles handle command success
 exact ⟨GeneralNominalOwnerRegistry250.handle_coverage frame handles registered handle member plan.packet.bindings,
   GeneralNominalRebaseDefinitions241.coherent _ _ _ _ _⟩

theorem checked_success (plan : Plan roles) (frame : Frame) (safe : SafeOrder frame.definitions) (handles : List Handle)
 (registered : Registered frame handles) (handle : Handle) (command : Command)
 (success : compile plan frame handles = some (handle,command)) :
 GeneralNominalCheckedInstall250.step frame command = some (advance frame command) :=
 GeneralNominalCheckedInstall250.step_success frame command safe (covered plan frame handles registered handle command success).1
   (covered plan frame handles registered handle command success).2

theorem retains_registry (frame : Frame) (handles : List Handle) (registered : Registered frame handles) (command : Command) :
 Registered (advance frame command) handles :=
 GeneralNominalOwnerRegistry250.equal_targets_registered frame _ handles
   (GeneralNominalFiniteInstallTrace250.targets_advance frame command) registered

theorem needed_covered (plan : Plan roles) (frame : Frame) (handles : List Handle) (handle : Handle) (command : Command)
 (success : compile plan frame handles = some (handle,command)) (name : Nat)
 (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) : name ∈ handle.names :=
 GeneralNominalStableRoleEnvironment251.needed_covered plan handle (compile_exact plan frame handles handle command success).2.1.2.2 name needed
end Yulang.GeneralNominalRegisteredPlan251
