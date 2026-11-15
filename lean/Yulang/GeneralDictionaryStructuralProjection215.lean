import Yulang.GeneralNominalFiniteBracket
import Yulang.GeneralNominalOriginTerms
set_option backward.isDefEq.respectTransparency false

/-! Checked structural intervals bound actual payload observations, without
assuming constructor injectivity or restricting the center to a finite term. -/
namespace Yulang.GeneralDictionaryStructuralProjection215
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Bounds)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFiniteBracket (reindex structural_slot shape_payload_below)
open CommonNominalFullCarrier

def Bounded (state : GeneralNominalState.State) (model : Assignment) (bounds : Bounds state) (origin : Origin) : Prop :=
  (∃ value, Observes model origin value) ∧ ∀ value, Observes model origin value → Fits state model bounds value

theorem structural_child (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (bounds : Bounds state)
    (lowerKind upperKind : Fin state.view.kinds)
    (lower : Fin (state.view.shapes lowerKind).arity → Fin state.base.slots)
    (upper : Fin (state.view.shapes upperKind).arity → Fin state.base.slots)
    (lowerAt : state.view.heads bounds.1 = .structural lowerKind lower)
    (upperAt : state.view.heads bounds.2 = .structural upperKind upper)
    (lowerShape : state.view.shapes lowerKind = shape) (upperShape : state.view.shapes upperKind = shape)
    (bounded : Bounded state model bounds origin)
    (tested : GeneralNominalOriginTerms.Head model origin (.structural shape))
    (index : Fin shape.arity) :
    Bounded state model (reindex lowerShape lower index,reindex upperShape upper index)
      (.structural origin shape index.val) := by
  have canonical : shape.Canonical := lowerShape ▸ state.view.canonical lowerKind
  have low := structural_slot state model valid bounds.1 lowerKind lower lowerAt lowerShape
  have high := structural_slot state model valid bounds.2 upperKind upper upperAt upperShape
  let lowValues := List.ofFn fun i => (model (state.base.source (reindex lowerShape lower i))).1
  let highValues := List.ofFn fun i => (model (state.base.source (reindex upperShape upper i))).1
  change Equivalent _ (shapeValue shape lowValues) at low
  change Equivalent _ (shapeValue shape highValues) at high
  constructor
  · obtain ⟨value,seen⟩ := tested.1
    obtain ⟨values,length,equal⟩ := tested.2 value seen
    have within : index.val < values.length := by rw [length]; exact index.isLt
    exact ⟨values[index.val],.structural seen length equal (List.getElem?_eq_getElem within)⟩
  · intro value seen
    cases seen with
    | structural parent length equal found =>
      have fits := bounded.2 _ parent
      constructor
      · exact shape_payload_below shape canonical lowValues _ (List.length_ofFn ..) length
          (by simp only [lowValues,List.getElem?_ofFn,index.isLt,↓reduceDIte]) found
          (subtype_trans low.2 (subtype_trans fits.1 equal.1))
      · exact shape_payload_below shape canonical _ highValues length (List.length_ofFn ..)
          found (by simp only [highValues,List.getElem?_ofFn,index.isLt,↓reduceDIte])
          (subtype_trans equal.2 (subtype_trans fits.2 high.1))
end Yulang.GeneralDictionaryStructuralProjection215
