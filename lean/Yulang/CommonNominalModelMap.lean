import Yulang.CommonNominalConservativity
import Yulang.InferenceModelMap

/-!
# Constructor-preserving embedding of old Common

Node references are translated recursively, while old blocks stay shared in a
`common` state. This makes the actual model constructors commute literally.
The raw graph embedding's order theorem supplies the semantic preservation.
-/

namespace Yulang.CommonNominalModelMap

open CommonNominalCarrier

mutual
  def value : Common.Ty → Ty
    | .base scalar => .base scalar
    | .bottom => .bottom
    | .top => .top
    | .union first last => .union (value first) (value last)
    | .inter first last => .inter (value first) (value last)
    | .pair first last => .pair (state first) (state last)
    | .emptyRecord => .emptyRecord
    | .exactEmpty => .exactEmpty
    | .record label payload rest => .record label (state payload) (value rest)
    | .recordDefault label source fallback => .recordDefault label (value source) (state fallback)
    | .variant label payload => .variant label (state payload)
    | .arrow arg argRow result resultRow => .arrow (state arg) argRow (state result) resultRow
    | .mask hidden source => .mask hidden (value source)
  def state : CommonSyntax.State Common.Row → CommonNominalSyntax.State Common.Row
    | .node type => .node (value type)
    | .block body root => .common (.block body root)
    | .legacy old => .common (.legacy old)
end

private theorem eval_agrees (depth : Nat)
    (assignment : CommonNominalSyntax.State Common.Row → CommonNominalFinite.Ty Common.Row)
    (same : ∀ reference, assignment (state reference) = assignment (.common reference))
    (type : Common.Ty) :
    (value type).evalAt depth assignment =
      (CommonNominalEmbedding.embed type).evalAt depth assignment := by
  induction type <;> simp [value, CommonNominalEmbedding.embed,
    CommonNominalSyntax.ofCommonLayer, CommonNominalSyntax.Layer.map,
    CommonNominalSyntax.Layer.evalAt, *]
  case recordDefault => cases depth <;>
    simp_all [CommonNominalEmbedding.embed, CommonNominalSyntax.Layer.evalAt_map]

private theorem state_observe (depth : Nat) (reference : CommonSyntax.State Common.Row) :
    CommonNominalSyntax.observe (CommonNominalSyntax.graph Common.Row) depth (state reference) =
      CommonNominalSyntax.observe (CommonNominalSyntax.graph Common.Row) depth (.common reference) := by
  induction depth generalizing reference with
  | zero => rfl
  | succ depth ih =>
      cases reference with
      | node type => exact eval_agrees depth _ ih type
      | block | legacy => rfl

theorem observe_value (depth : Nat) (type : Common.Ty) :
    observeTy depth (value type) = CommonNominalEmbedding.finite (Common.observeTy depth type) := by
  rw [← CommonNominalEmbedding.observe_embed]
  exact eval_agrees depth _ (state_observe depth) type

theorem subtype_exact (first last : Common.Ty) :
    CommonNominalCarrier.Subtype (value first) (value last) ↔ Common.Subtype first last := by
  unfold CommonNominalCarrier.Subtype Common.Subtype
  simp only [observe_value]
  exact forall_congr' fun depth => CommonNominalConservativity.finite_order_conservative _ _

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
    value (Common.recordDefault label source fallback) = model.recordDefault label (value source) (value fallback) := rfl

end Yulang.CommonNominalModelMap

namespace Yulang.CommonNominalModelMap

open CommonNominalCarrier

mutual
  /-- A total syntactic retraction, used only to transport independently
  prescribed old signature binders. It is not an erasure soundness claim for
  arbitrary new nominal values. -/
  def retract : Ty → Common.Ty
    | .base scalar => .base scalar
    | .bottom => .bottom
    | .top => .top
    | .union first last => .union (retract first) (retract last)
    | .inter first last => .inter (retract first) (retract last)
    | .pair first last => .pair (retractState first) (retractState last)
    | .emptyRecord => .emptyRecord
    | .exactEmpty => .exactEmpty
    | .record label payload rest => .record label (retractState payload) (retract rest)
    | .recordDefault label source fallback => .recordDefault label (retract source) (retractState fallback)
    | .variant label payload => .variant label (retractState payload)
    | .arrow arg argRow result resultRow => .arrow (retractState arg) argRow (retractState result) resultRow
    | .mask hidden source => .mask hidden (retract source)
    | .float | .nominal _ _ => .top
  def retractState : CommonNominalSyntax.State Common.Row → CommonSyntax.State Common.Row
    | .node type => .node (retract type)
    | .common old => old
    | .legacy old => .legacy old
    | .block _ _ => .node .top
end

mutual
  @[simp] theorem retract_value (type : Common.Ty) : retract (value type) = type := by
    cases type <;> simp [value, retract, retract_value, retract_state]
  @[simp] theorem retract_state (reference : CommonSyntax.State Common.Row) :
      retractState (state reference) = reference := by
    cases reference <;> simp [state, retractState, retract_value]
end

end Yulang.CommonNominalModelMap
