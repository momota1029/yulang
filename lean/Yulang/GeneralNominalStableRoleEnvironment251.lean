import Yulang.GeneralNominalRoleEquations251
namespace Yulang.GeneralNominalStableRoleEnvironment251
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRoleEnvironment251
open GeneralNominalMaterializedOwnerFrame249 (Frame)
open GeneralNominalOwnerOpening250 (Handle)
open GeneralNominalAllocation (Bindings occurrences lower upper)
open GeneralNominalRebaseProjectionView243 (Bounds)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedSubstitution247
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDependence247
open CommonNominalFullCarrier

def compile (frame : Frame) (handle : Handle) (bindings : Bindings)
 (fallback : Nat → Bounds) (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) : Syntax :=
 ⟨mapping frame.definitions,
 fun name => if name ∈ handle.names then GeneralNominalStableCapture250.bounds frame handle bindings name else fallback name,
 binders,targets⟩

noncomputable def values (frame : Frame) (handle : Handle) (bindings : Bindings)
 (fallback : Nat → Bounds) (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) (assignment : Assignment) : Values :=
 ⟨solve model frame.definitions assignment,
 fun name => if name ∈ handle.names then (lower (occurrences bindings name)).eval model (solve model frame.definitions assignment)
   else (fallback name).lower.eval model assignment,
 fun name => if name ∈ handle.names then (upper (occurrences bindings name)).eval model (solve model frame.definitions assignment)
   else (fallback name).upper.eval model assignment,
 fun name => (binders name).eval model assignment,GeneralNominalRebaseRawView243.read targets assignment⟩

theorem related (frame : Frame) (handle : Handle) (bindings : Bindings)
 (fallback : Nat → Bounds) (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) (assignment : Assignment)
 (valid : PresenceNormalForm.All model assignment (block (transform (mapping frame.definitions)
   (GeneralNominalRebaseDefinitions241.entries handle.seed handle.root handle.declaration bindings handle.names)))) :
 Related (read (compile frame handle bindings fallback binders targets) assignment)
   (values frame handle bindings fallback binders targets assignment) := by
 constructor
 · exact GeneralNominalOrderedRaw248.read_mapping _ _
 · intro name
   by_cases named : name ∈ handle.names
   · simpa [GeneralNominalRoleEnvironment251.read,compile,values,named] using
       (GeneralNominalStableCapture250.bound_values frame handle bindings assignment valid name named).1
   · simp only [GeneralNominalRoleEnvironment251.read,compile,values,named,ite_false]
     exact ⟨subtype_refl _,subtype_refl _⟩
 · intro name
   by_cases named : name ∈ handle.names
   · simpa [GeneralNominalRoleEnvironment251.read,compile,values,named] using
       (GeneralNominalStableCapture250.bound_values frame handle bindings assignment valid name named).2
   · simp only [GeneralNominalRoleEnvironment251.read,compile,values,named,ite_false]
     exact ⟨subtype_refl _,subtype_refl _⟩
 · intro name; exact ⟨subtype_refl _,subtype_refl _⟩
 · intro name; exact ⟨⟨subtype_refl _,subtype_refl _⟩,rfl⟩

theorem generated_related (frame : Frame) (safe : SafeOrder frame.definitions) (handle : Handle) (bindings : Bindings)
 (within : TargetsWithin (GeneralNominalRebaseDefinitions241.entries handle.seed handle.root handle.declaration bindings handle.names) frame.definitions)
 (fallback : Nat → Bounds) (binders : Nat → TyTerm Nat) (targets : Nat → CompTerm Nat) (assignment : Assignment) :
 Related (read (compile frame handle bindings fallback binders targets)
   (GeneralNominalStableCaptureStep250.next frame handle bindings assignment))
 (values frame handle bindings fallback binders targets (GeneralNominalStableCaptureStep250.next frame handle bindings assignment)) :=
 related frame handle bindings fallback binders targets _
   (GeneralNominalStableCaptureStep250.generated_equations frame safe handle bindings within assignment)

theorem needed_covered (plan : GeneralNominalCenters.Plan roles) (handle : Handle)
 (names : handle.names = plan.packet.declaration.inputNames) (name : Nat)
 (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
 name ∈ handle.names := by
 rw [names]
 rcases needed with input | ⟨clause,present,used⟩
 · exact input
 · exact plan.packet.checked.scope.1 clause present name used
end Yulang.GeneralNominalStableRoleEnvironment251
