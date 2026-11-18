import Yulang.GeneralNominalOwnerOpening250
import Yulang.GeneralNominalPersistentOwner250
import Yulang.GeneralNominalCaptureMerges
/-! Actual occurrence folds feed stable expression bounds. Singleton endpoints
are read through the old snapshot; many/empty cases use reserved lo/hi cells.
This is a component of a new packet compiler, not a full source transition. -/
namespace Yulang.GeneralNominalStableCapture250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralNominalOwnerOpening250 (Handle)
open GeneralNominalAllocation (Bindings occurrences lower upper)
open GeneralNominalRebaseDefinitions241 (entries slot)
open GeneralNominalRebaseProjectionView243 (Bounds)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedSubstitution247
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDependence247
open CommonNominalFullCarrier

def bounds (frame : Frame) (handle : Handle) (bindings : Bindings) (name : Nat) : Bounds :=
 match occurrences bindings name with
 | [pair] => ⟨(mapping frame.definitions pair.1).ty,(mapping frame.definitions pair.2).ty⟩
 | _ => ⟨.var (slot handle.seed handle.root handle.declaration 0 name bindings),
          .var (slot handle.seed handle.root handle.declaration 1 name bindings)⟩

theorem equation_value (old : List (Entry Nat)) (raw : List (Entry Nat))
 (valid : All model assignment (block (transform (mapping old) raw)))
 (entry : Entry Nat) (member : entry ∈ raw) :
 Equivalent (assignment entry.1).1 (entry.2.eval model (solve model old assignment)) := by
 have equationsValid : All model assignment (equations entry.1 (entry.2.subst (mapping old))) := by
   intro atom present
   exact valid atom (List.mem_flatMap.mpr ⟨_,List.mem_map.mpr ⟨entry,member,rfl⟩,present⟩)
 have equivalent := (GeneralNominalCaptureMerges.equations_exact assignment entry.1 (entry.2.subst (mapping old))).mp equationsValid
 rw [GeneralPresenceSnapshotBlock250.rhs_snapshot] at equivalent
 exact equivalent

theorem bound_values (frame : Frame) (handle : Handle) (bindings : Bindings)
 (assignment : Assignment)
 (valid : All model assignment (block (transform (mapping frame.definitions)
   (entries handle.seed handle.root handle.declaration bindings handle.names))))
 (name : Nat) (named : name ∈ handle.names) :
 Equivalent ((bounds frame handle bindings name).lower.eval model assignment)
   ((lower (occurrences bindings name)).eval model (solve model frame.definitions assignment)) ∧
 Equivalent ((bounds frame handle bindings name).upper.eval model assignment)
   ((upper (occurrences bindings name)).eval model (solve model frame.definitions assignment)) := by
 have many (different : (occurrences bindings name).length ≠ 1) :
   Equivalent (assignment (slot handle.seed handle.root handle.declaration 0 name bindings)).1
     ((lower (occurrences bindings name)).eval model (solve model frame.definitions assignment)) ∧
   Equivalent (assignment (slot handle.seed handle.root handle.declaration 1 name bindings)).1
     ((upper (occurrences bindings name)).eval model (solve model frame.definitions assignment)) := by
   constructor
   · exact equation_value frame.definitions _ valid _
       ((GeneralNominalRebaseDefinitions241.member_iff ..).mpr ⟨name,named,different,Or.inl rfl⟩)
   · exact equation_value frame.definitions _ valid _
       ((GeneralNominalRebaseDefinitions241.member_iff ..).mpr ⟨name,named,different,Or.inr rfl⟩)
 cases found : occurrences bindings name with
 | nil => simpa only [bounds,found,TyTerm.eval] using many (by simp [found])
 | cons pair rest =>
   cases rest with
   | nil =>
     have one := congrArg Prod.fst (mapping_eval frame.definitions model assignment pair.1)
     have two := congrArg Prod.fst (mapping_eval frame.definitions model assignment pair.2)
     simp only [bounds,found,lower,upper,TyTerm.eval]
     change Equivalent _ (solve model frame.definitions assignment pair.1).1 ∧ Equivalent _ (solve model frame.definitions assignment pair.2).1
     rw [← one,← two]
     exact ⟨⟨subtype_refl _,subtype_refl _⟩,⟨subtype_refl _,subtype_refl _⟩⟩
   | cons other tail => simpa only [bounds,found,TyTerm.eval] using many (by simp [found])

theorem bounds_exact (frame : Frame) (handle : Handle) (bindings : Bindings)
 (assignment : Assignment)
 (valid : All model assignment (block (transform (mapping frame.definitions)
   (entries handle.seed handle.root handle.declaration bindings handle.names))))
 (name : Nat) (named : name ∈ handle.names) (nonempty : occurrences bindings name ≠ []) (actual : Ty) :
 (bounds frame handle bindings name).Fits assignment actual ↔
 ∀ original ∈ occurrences bindings name, GeneralNominalCaptureMerges.Fits (solve model frame.definitions assignment) original actual := by
 obtain ⟨lo,hi⟩ := bound_values frame handle bindings assignment valid name named
 have lowerBounds := GeneralNominalCaptureMerges.lower_exact (solve model frame.definitions assignment) _ nonempty actual
 have upperBounds := GeneralNominalCaptureMerges.upper_exact (solve model frame.definitions assignment) _ nonempty actual
 constructor
 · intro fits original member
   exact ⟨lowerBounds.mp (subtype_trans lo.2 fits.1) original member,
     upperBounds.mp (subtype_trans fits.2 hi.1) original member⟩
 · intro fits
   exact ⟨subtype_trans lo.1 (lowerBounds.mpr (fun original member => (fits original member).1)),
     subtype_trans (upperBounds.mpr (fun original member => (fits original member).2)) hi.2⟩
end Yulang.GeneralNominalStableCapture250
