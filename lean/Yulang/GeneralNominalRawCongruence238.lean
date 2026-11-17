import Yulang.GeneralNominalAssignmentCongruence238
import Yulang.GeneralNominalState
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRawCongruence238
open GeneralNominalAssignmentCongruence238
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {first last : Assignment}

theorem equiv_trans (a : Equivalent x y) (b : Equivalent y z) : Equivalent x z :=
 ⟨subtype_trans a.1 b.1,subtype_trans b.2 a.2⟩
theorem equiv_iff (a : Equivalent x x') (b : Equivalent y y') :
 Equivalent x y ↔ Equivalent x' y' :=
 and_congr (subtype_iff a b) (subtype_iff b a)

theorem assignment (state : GeneralSourceState.State) (same : Same first last) :
 Same (GeneralNominalCommonBridge.assignment state first) (GeneralNominalCommonBridge.assignment state last) :=
 fun slot => ⟨(same (state.source slot)).1,(same (state.rowSource slot)).2⟩

theorem base_iff (state : GeneralSourceState.State) (same : Same first last) :
 GeneralNominalCommonBridge.Models state first ↔ GeneralNominalCommonBridge.Models state last := by
 apply and_congr (all_iff (assignment state same) state.ordinary)
 apply and_congr
 · apply forall_congr'; intro slot
   apply forall_congr'; intro term
   apply forall_congr'; intro recorded
   exact equiv_iff (same (state.source slot)).1 (type_eval (assignment state same) term)
 · apply forall_congr'; intro pair
   apply forall_congr'; intro member
   exact subtype_iff (same (state.source pair.1)).1 (same (state.source pair.2)).1

theorem fits_iff (state : GeneralSourceState.State) (same : Same first last)
 (parameter : GeneralNominalState.Parameter state.slots) (value : Argument) :
 GeneralNominalState.Fits state first parameter value ↔ GeneralNominalState.Fits state last parameter value := by
 cases parameter with
 | type bounds =>
   cases value with
   | inl value =>
     exact and_congr (subtype_iff (same _).1 ⟨subtype_refl _,subtype_refl _⟩)
       (subtype_iff ⟨subtype_refl _,subtype_refl _⟩ (same _).1)
   | inr value => rfl
 | row bounds =>
   cases value with
   | inl value => rfl
   | inr value => simp only [GeneralNominalState.Fits,(same _).2]

theorem fitsAll (state : GeneralSourceState.State) (same : Same first last)
 {parameters : List (GeneralNominalState.Parameter state.slots)} {values : List Argument}
 (valid : GeneralNominalState.FitsAll state first parameters values) :
 GeneralNominalState.FitsAll state last parameters values := by
 induction valid with
 | nil => exact .nil
 | cons fit rest ih => exact .cons ((fits_iff state same _ _).mp fit) ih

theorem denotes_iff (state : GeneralSourceState.State) (same : Same first last)
 (slot : Fin state.slots) (descriptor : GeneralNominalState.Descriptor state.slots) :
 GeneralNominalState.Denotes state first slot descriptor ↔ GeneralNominalState.Denotes state last slot descriptor := by
 constructor
 · rintro ⟨values,fit,equal⟩
   exact ⟨values,fitsAll state same fit,equiv_trans ⟨(same _).1.2,(same _).1.1⟩ equal⟩
 · rintro ⟨values,fit,equal⟩
   exact ⟨values,fitsAll state (symm same) fit,equiv_trans (same _).1 equal⟩

theorem models_iff (state : GeneralNominalState.State) (same : Same first last) :
 GeneralNominalState.Models state first ↔ GeneralNominalState.Models state last := by
 apply and_congr (base_iff state.base same)
 apply and_congr
 · apply forall_congr'; intro slot
   apply forall_congr'; intro descriptor
   apply forall_congr'; intro recorded
   exact denotes_iff state.base same slot descriptor
 · exact all_iff same state.ordinary
end Yulang.GeneralNominalRawCongruence238
