import Yulang.GeneralNominalRoleBinder251
import Yulang.GeneralNominalOwnerExecution250
namespace Yulang.GeneralNominalPlanProducer251
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralNominalOwnerOpening250 (Handle choose openFrame)
open GeneralNominalRebaseProjectionView243 (Bounds)
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDependence247
open GeneralNominalRoleEnvironment251 (Syntax)
open CommonNominalFullCarrier

def handle (plan : Plan roles) (frame : Frame) (protectedNames : List Nat) : Handle :=
 choose frame plan.packet.site.occurrence.identity plan.packet.declaration.id plan.packet.declaration.inputNames protectedNames

def opened (plan : Plan roles) (frame : Frame) (protectedNames : List Nat) : Frame :=
 openFrame frame (handle plan frame protectedNames)

def fallback (plan : Plan roles) (frame : Frame) (name : Nat) : Bounds :=
 ⟨(mapping frame.definitions ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name).1).ty,
   (mapping frame.definitions ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name).2).ty⟩

def env (plan : Plan roles) (frame : Frame) (protectedNames : List Nat) : Syntax :=
 let initial := opened plan frame protectedNames
 GeneralNominalStableRoleEnvironment251.compile initial (handle plan frame protectedNames) plan.packet.bindings
   (fallback plan initial) (GeneralNominalRoleBinder251.compile plan initial CompTerm.var) CompTerm.var

def command (plan : Plan roles) (frame : Frame) (protectedNames : List Nat) : GeneralNominalFiniteInstallTrace250.Command :=
 let initial := opened plan frame protectedNames
 GeneralNominalStableRolePacket251.command plan initial (handle plan frame protectedNames)
   (fallback plan initial) (GeneralNominalRoleBinder251.compile plan initial CompTerm.var) CompTerm.var

def result (plan : Plan roles) (frame : Frame) (protectedNames : List Nat) : Frame :=
 GeneralNominalFiniteInstallTrace250.advance (opened plan frame protectedNames) (command plan frame protectedNames)

theorem aligned (plan : Plan roles) (frame : Frame) (protectedNames : List Nat) :
 (handle plan frame protectedNames).root = plan.packet.site.occurrence.identity ∧
 (handle plan frame protectedNames).declaration = plan.packet.declaration.id ∧
 (handle plan frame protectedNames).names = plan.packet.declaration.inputNames := ⟨rfl,rfl,rfl⟩

theorem coverage (plan : Plan roles) (frame : Frame) (protectedNames : List Nat) :
 TargetsWithin (command plan frame protectedNames).raw (opened plan frame protectedNames).definitions :=
 GeneralNominalStableSlots250.entries_covered frame _ _ _ _ _

theorem safe (plan : Plan roles) (frame : Frame) (oldSafe : SafeOrder frame.definitions) (protectedNames : List Nat) :
 SafeOrder (opened plan frame protectedNames).definitions :=
 GeneralNominalOwnerOpening250.open_safe frame oldSafe _ _ _ _

theorem needed_covered (plan : Plan roles) (frame : Frame) (protectedNames : List Nat) (name : Nat)
 (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
 name ∈ (handle plan frame protectedNames).names :=
 GeneralNominalStableRoleEnvironment251.needed_covered plan _ rfl name needed

theorem checked_success (plan : Plan roles) (frame : Frame) (oldSafe : SafeOrder frame.definitions) (protectedNames : List Nat) :
 GeneralNominalCheckedInstall250.step (opened plan frame protectedNames) (command plan frame protectedNames) =
 some (result plan frame protectedNames) :=
 GeneralNominalCheckedInstall250.step_success _ _ (safe plan frame oldSafe protectedNames) (coverage plan frame protectedNames)
   (GeneralNominalRebaseDefinitions241.coherent _ _ _ _ _)

noncomputable def seedAssignment (plan : Plan roles) (frame : Frame) (protectedNames : List Nat) (assignment : Assignment) : Assignment :=
 GeneralNominalOwnerExecution250.seedAssignment (handle plan frame protectedNames) assignment

noncomputable def finalAssignment (plan : Plan roles) (frame : Frame) (protectedNames : List Nat) (assignment : Assignment) : Assignment :=
 GeneralNominalStableCaptureStep250.next (opened plan frame protectedNames) (handle plan frame protectedNames) plan.packet.bindings
   (seedAssignment plan frame protectedNames assignment)

noncomputable def reference (plan : Plan roles) (frame : Frame) (protectedNames : List Nat) (assignment : Assignment) : GeneralNominalRoleEnvironment251.Values :=
 let initial := opened plan frame protectedNames
 GeneralNominalStableRoleHead251.reference (handle plan frame protectedNames) plan.packet.bindings
   (fallback plan initial) (GeneralNominalRoleBinder251.compile plan initial CompTerm.var) CompTerm.var
   (solve model initial.definitions (seedAssignment plan frame protectedNames assignment))
   (finalAssignment plan frame protectedNames assignment)

theorem install_exact (plan : Plan roles) (frame : Frame) (oldSafe : SafeOrder frame.definitions) (protectedNames : List Nat)
 (assignment : Assignment) (valid : Models frame assignment) :
 Models (result plan frame protectedNames) (finalAssignment plan frame protectedNames assignment) ↔
 GeneralNominalRolePacket251.Holds plan (env plan frame protectedNames) (reference plan frame protectedNames assignment)
   (finalAssignment plan frame protectedNames assignment) := by
 have reserved : Models (opened plan frame protectedNames) (seedAssignment plan frame protectedNames assignment) :=
   GeneralNominalFrameReservation250.models_forward frame _ (GeneralNominalOwnerOpening250.fresh frame _ _ _ _) assignment valid
 exact GeneralNominalStableRolePacket251.install_exact plan _ (safe plan frame oldSafe protectedNames)
   _ (coverage plan frame protectedNames) _ _ _ _ reserved
end Yulang.GeneralNominalPlanProducer251
