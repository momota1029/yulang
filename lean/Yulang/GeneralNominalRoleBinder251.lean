import Yulang.GeneralNominalStableRolePacket251
namespace Yulang.GeneralNominalRoleBinder251
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCenters (Plan)
open GeneralNominalMaterializedOwnerFrame249 (Frame)
open GeneralNominalAllocation (occurrences)
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedBlock247

/-- A point singleton keeps its historical endpoint; allocated outputs and
nonpoint centers use the explicitly supplied target interpretation. -/
def compile (plan : Plan roles) (frame : Frame) (targets : Nat → CompTerm Nat) (name : Nat) : TyTerm Nat :=
 if name ∈ plan.packet.declaration.outputNames then
   (targets ((GeneralNominalVersionedFrame231.capture plan.packet).outputs name)).ty
 else match occurrences plan.packet.bindings name with
 | [pair] => if pair.1 = pair.2 then (mapping frame.definitions pair.1).ty
   else (targets (GeneralNominalVersionedFrame231.binder plan name)).ty
 | _ => (targets (GeneralNominalVersionedFrame231.binder plan name)).ty

theorem output (plan : Plan roles) (frame : Frame) (targets : Nat → CompTerm Nat) (name : Nat)
 (declared : name ∈ plan.packet.declaration.outputNames) :
 compile plan frame targets name = (targets ((GeneralNominalVersionedFrame231.capture plan.packet).outputs name)).ty := by
 simp [compile,declared]

theorem singleton_point (plan : Plan roles) (frame : Frame) (targets : Nat → CompTerm Nat) (name endpoint : Nat)
 (input : name ∉ plan.packet.declaration.outputNames)
 (one : occurrences plan.packet.bindings name = [(endpoint,endpoint)]) :
 compile plan frame targets name = (mapping frame.definitions endpoint).ty := by
 simp [compile,input,one]

theorem point_value (plan : Plan roles) (frame : Frame) (targets : Nat → CompTerm Nat) (name endpoint : Nat)
 (input : name ∉ plan.packet.declaration.outputNames)
 (one : occurrences plan.packet.bindings name = [(endpoint,endpoint)])
 (assignment : GeneralNominalCommonBridge.Assignment) :
 (compile plan frame targets name).eval CommonNominalFullCarrier.model assignment =
 (solve CommonNominalFullCarrier.model frame.definitions assignment endpoint).1 := by
 rw [singleton_point plan frame targets name endpoint input one]
 exact congrArg Prod.fst (mapping_eval frame.definitions CommonNominalFullCarrier.model assignment endpoint)

theorem nonpoint_singleton (plan : Plan roles) (frame : Frame) (targets : Nat → CompTerm Nat) (name : Nat)
 (input : name ∉ plan.packet.declaration.outputNames)
 (one : occurrences plan.packet.bindings name = [pair]) (different : pair.1 ≠ pair.2) :
 compile plan frame targets name = (targets (GeneralNominalVersionedFrame231.binder plan name)).ty := by
 simp [compile,input,one,different]

theorem nonsingleton (plan : Plan roles) (frame : Frame) (targets : Nat → CompTerm Nat) (name : Nat)
 (input : name ∉ plan.packet.declaration.outputNames)
 (many : (occurrences plan.packet.bindings name).length ≠ 1) :
 compile plan frame targets name = (targets (GeneralNominalVersionedFrame231.binder plan name)).ty := by
 unfold compile
 rw [ite_eq_right input]
 cases found : occurrences plan.packet.bindings name with
 | nil => rfl
 | cons pair rest =>
   cases rest with
   | nil => exact False.elim (many (by simp [found]))
   | cons => rfl
end Yulang.GeneralNominalRoleBinder251
