import Yulang.GeneralNominalInputOccurrences256
import Yulang.GeneralPresenceCheckedNormal252
namespace Yulang.GeneralNominalAggregateAtoms256
open Core.PresenceGeneration GeneralNominalAllocation
open GeneralSourceState (Interval)
open GeneralPresenceCheckedNormal252

/-- Nonempty actual lower folds introduce no extra bottom atom. -/
theorem lower_atoms (bounds : List Interval) (nonempty : bounds ≠ []) (mapping : Nat → CompTerm Nat) :
 atoms .lower ((lower bounds).subst mapping) =
 bounds.flatMap (fun pair => atoms .lower (mapping pair.1).ty) := by
 induction bounds with
 | nil => exact False.elim (nonempty rfl)
 | cons pair rest ih =>
   cases rest with
   | nil => simp [lower,TyTerm.subst]
   | cons next tail =>
     simp only [lower,TyTerm.subst,atoms,GeneralPresenceUnionNormal252.atoms,List.flatMap_cons]
     have tailEq := ih (by simp)
     exact congrArg (fun terms => _ ++ terms) tailEq

theorem upper_atoms (bounds : List Interval) (nonempty : bounds ≠ []) (mapping : Nat → CompTerm Nat) :
 atoms .upper ((upper bounds).subst mapping) =
 bounds.flatMap (fun pair => atoms .upper (mapping pair.2).ty) := by
 induction bounds with
 | nil => exact False.elim (nonempty rfl)
 | cons pair rest ih =>
   cases rest with
   | nil => simp [upper,TyTerm.subst]
   | cons next tail =>
     simp only [upper,TyTerm.subst,atoms,GeneralPresenceInterNormal252.atoms,List.flatMap_cons]
     have tailEq := ih (by simp)
     exact congrArg (fun terms => _ ++ terms) tailEq

theorem lower_supported_iff (bounds : List Interval) (nonempty : bounds ≠ [])
 (mapping : Nat → CompTerm Nat) (pool : List (TyTerm Nat)) :
 atoms .lower ((lower bounds).subst mapping) ⊆ pool ↔
 ∀ pair ∈ bounds, atoms .lower (mapping pair.1).ty ⊆ pool := by
 rw [lower_atoms bounds nonempty mapping]
 constructor
 · intro supported pair member atom present
   exact supported (List.mem_flatMap.mpr ⟨pair,member,present⟩)
 · intro supported atom present
   obtain ⟨pair,member,present⟩ := List.mem_flatMap.mp present
   exact supported pair member present

theorem upper_supported_iff (bounds : List Interval) (nonempty : bounds ≠ [])
 (mapping : Nat → CompTerm Nat) (pool : List (TyTerm Nat)) :
 atoms .upper ((upper bounds).subst mapping) ⊆ pool ↔
 ∀ pair ∈ bounds, atoms .upper (mapping pair.2).ty ⊆ pool := by
 rw [upper_atoms bounds nonempty mapping]
 constructor
 · intro supported pair member atom present
   exact supported (List.mem_flatMap.mpr ⟨pair,member,present⟩)
 · intro supported atom present
   obtain ⟨pair,member,present⟩ := List.mem_flatMap.mp present
   exact supported pair member present
end Yulang.GeneralNominalAggregateAtoms256
