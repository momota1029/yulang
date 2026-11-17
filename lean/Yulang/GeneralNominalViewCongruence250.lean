import Yulang.GeneralNominalAssignmentCongruence238
import Yulang.GeneralNominalRebaseRawView243
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalViewCongruence250
open GeneralNominalAssignmentCongruence238
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {first last : Assignment}

theorem equiv_trans (a : Equivalent x y) (b : Equivalent y z) : Equivalent x z :=
 ⟨subtype_trans a.1 b.1,subtype_trans b.2 a.2⟩
theorem equiv_iff (a : Equivalent x x') (b : Equivalent y y') :
 Equivalent x y ↔ Equivalent x' y' :=
 and_congr (subtype_iff a b) (subtype_iff b a)

theorem fits_iff (same : Same first last)
 (parameter : GeneralNominalRebaseRawView243.Parameter) (value : Argument) :
 parameter.Fits first value ↔ parameter.Fits last value := by
 cases parameter with
 | type lower upper =>
   cases value with
   | inl value =>
     exact and_congr (subtype_iff (type_eval same lower) ⟨subtype_refl _,subtype_refl _⟩)
       (subtype_iff ⟨subtype_refl _,subtype_refl _⟩ (type_eval same upper))
   | inr value => rfl
 | row lower upper =>
   cases value with
   | inl value => rfl
   | inr value => simp only [GeneralNominalRebaseRawView243.Parameter.Fits,row_eval same lower,row_eval same upper]

theorem fitsAll (same : Same first last)
 {parameters : List GeneralNominalRebaseRawView243.Parameter} {values : List Argument}
 (valid : GeneralNominalRebaseRawView243.FitsAll first parameters values) :
 GeneralNominalRebaseRawView243.FitsAll last parameters values := by
 induction valid with
 | nil => exact .nil
 | cons fit rest ih => exact .cons ((fits_iff same _ _).mp fit) ih

theorem denotes_iff (same : Same first last) (target : Core.PresenceGeneration.TyTerm Nat)
 (descriptor : GeneralNominalRebaseRawView243.Descriptor) :
 descriptor.Denotes first target ↔ descriptor.Denotes last target := by
 constructor
 · rintro ⟨values,fit,equal⟩
   exact ⟨values,fitsAll same fit,equiv_trans ⟨(type_eval same target).2,(type_eval same target).1⟩ equal⟩
 · rintro ⟨values,fit,equal⟩
   exact ⟨values,fitsAll (symm same) fit,equiv_trans (type_eval same target) equal⟩

theorem models_iff (view : GeneralNominalRebaseRawView243.View) (same : Same first last) :
 view.Models first ↔ view.Models last := by
 apply and_congr (all_iff same view.ordinary)
 apply and_congr
 · apply forall_congr'; intro index
   apply forall_congr'; intro term
   apply forall_congr'; intro found
   exact equiv_iff (type_eval same _) (type_eval same term)
 · apply and_congr
   · apply forall_congr'; intro pair
     apply forall_congr'; intro member
     exact subtype_iff (type_eval same _) (type_eval same _)
   · apply forall_congr'; intro index
     apply forall_congr'; intro descriptor
     apply forall_congr'; intro found
     exact denotes_iff same _ descriptor
end Yulang.GeneralNominalViewCongruence250
