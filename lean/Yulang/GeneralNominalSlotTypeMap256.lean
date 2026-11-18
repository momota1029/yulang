import Yulang.GeneralNominalViewTypeMap255
namespace Yulang.GeneralNominalSlotTypeMap256
open Core.PresenceGeneration
open GeneralNominalRebaseRawView243
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalAssignmentCongruence238 (subtype_iff)
open GeneralNominalViewTypeMap255 (equivalent_iff)

/-- Change slot types only. Other type-valued consumers and all row-valued
consumers remain literal, rather than being passed through an unsafe check. -/
def map (view : View) (types : Fin view.slots → TyTerm Nat) : View :=
 { view with slot := fun index => ⟨types index,(view.slot index).row⟩ }

theorem models_exact (view : View) (types : Fin view.slots → TyTerm Nat) (assignment : Assignment)
 (same : ∀ index, Equivalent ((types index).eval model assignment) ((view.slot index).ty.eval model assignment)) :
 (map view types).Models assignment ↔ view.Models assignment := by
 unfold View.Models
 apply and_congr Iff.rfl
 apply and_congr
 · apply forall_congr'; intro index
   apply forall_congr'; intro term
   apply forall_congr'; intro found
   exact equivalent_iff (same index) ⟨subtype_refl _,subtype_refl _⟩
 apply and_congr
 · apply forall_congr'; intro pair
   apply forall_congr'; intro member
   exact subtype_iff (same pair.1) (same pair.2)
 · apply forall_congr'; intro index
   apply forall_congr'; intro descriptor
   apply forall_congr'; intro found
   unfold Descriptor.Denotes
   apply exists_congr; intro values
   exact and_congr Iff.rfl (equivalent_iff (same index) ⟨subtype_refl _,subtype_refl _⟩)

theorem ordinary_unchanged (view : View) (types : Fin view.slots → TyTerm Nat) :
 (map view types).ordinary = view.ordinary := rfl

theorem nominals_unchanged (view : View) (types : Fin view.slots → TyTerm Nat) :
 (map view types).nominals = view.nominals := rfl
end Yulang.GeneralNominalSlotTypeMap256
