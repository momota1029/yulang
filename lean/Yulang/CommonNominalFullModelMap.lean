import Yulang.CommonNominalFullConservativity
import Yulang.CommonNominalFullModel
import Yulang.CommonNominalModelMap

/-!
# Constructor-preserving old Common embedding in the full role carrier

The syntax translation and its literal retraction are shared with the earlier
candidate. All semantic claims here use the refined full-role order, proved
conservative independently. No order claim for the earlier nominal candidate
is used to transfer arbitrary new nominal types.
-/

namespace Yulang.CommonNominalFullModelMap

open CommonNominalFullCarrier

abbrev value := CommonNominalModelMap.value
abbrev retract := CommonNominalModelMap.retract

theorem retract_value (type : Common.Ty) : retract (value type) = type :=
  CommonNominalModelMap.retract_value type

theorem observe_value (depth : Nat) (type : Common.Ty) :
    observeTy depth (value type) = CommonNominalEmbedding.finite (Common.observeTy depth type) :=
  CommonNominalModelMap.observe_value depth type

theorem subtype_exact (first last : Common.Ty) :
    CommonNominalFullCarrier.Subtype (value first) (value last) ↔ Common.Subtype first last := by
  unfold CommonNominalFullCarrier.Subtype Common.Subtype
  simp only [observe_value]
  exact forall_congr' fun _ => CommonNominalFullConservativity.finite_order_conservative _ _

def modelMap : Inference.ModelMap Common.model.toModel model.toModel where
  value := value
  row := id
  base := fun _ => rfl
  bottom := rfl
  top := rfl
  union := fun _ _ => rfl
  inter := fun _ _ => rfl
  pair := fun _ _ => rfl
  emptyRecord := rfl
  record := fun _ _ _ => rfl
  variant := fun _ _ => rfl
  arrow := fun _ _ _ _ => rfl
  empty := rfl
  join := fun _ _ => rfl
  subtype := fun {first last} below => (subtype_exact first last).mpr below
  subrow := id

@[simp] theorem value_exactEmpty : value Common.exactEmpty = model.exactEmpty := rfl
@[simp] theorem value_required (label : Nat) (payload : Common.Ty) :
    value (Common.required label payload) = model.required label (value payload) := rfl
@[simp] theorem value_default (label : Nat) (source fallback : Common.Ty) :
    value (Common.recordDefault label source fallback) =
      model.recordDefault label (value source) (value fallback) := rfl

end Yulang.CommonNominalFullModelMap
