import Yulang.GeneralNominalPointOriginEnrichment188
import Yulang.GeneralNominalOriginAlias181
import Yulang.GeneralNominalFiniteBracket

/-! Actual structural projections of a point source agree semantically with
its physical child slots. Canonical shape injectivity is taken from the actual
checked observation, not assumed for arbitrary record label sequences. -/
namespace Yulang.GeneralNominalStructuralOrigin188
open GeneralNominalRecursiveInspection GeneralNominalOriginAlias181
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {model : Assignment}

 theorem similar_refl (model : Assignment) (origin : Origin) : Similar model origin origin :=
  ⟨fun value seen => ⟨value,seen,⟨subtype_refl _,subtype_refl _⟩⟩,
    fun value seen => ⟨value,seen,⟨subtype_refl _,subtype_refl _⟩⟩⟩

 theorem similar_symm (same : Similar model first last) : Similar model last first := ⟨same.2,same.1⟩

 theorem structural_slot_same (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (kind : Fin state.view.kinds)
    (children : Fin (state.view.shapes kind).arity → Fin state.base.slots)
    (recorded : state.view.heads slot = .structural kind children)
    (index : Fin (state.view.shapes kind).arity) :
    GeneralNominalOriginTerms.Same model
      (.structural (.source (state.base.source slot)) (state.view.shapes kind) index.val)
      (.source (state.base.source (children index))) := by
  let values := List.ofFn fun i => (model (state.base.source (children i))).1
  have length : values.length = (state.view.shapes kind).arity := List.length_ofFn
  have found : values[index.val]? = some (model (state.base.source (children index))).1 := by
    simp only [values,List.getElem?_ofFn,index.isLt,↓reduceDIte]
  have shape : Equivalent (model (state.base.source slot)).1 (shapeValue (state.view.shapes kind) values) :=
    GeneralNominalFiniteBracket.structural_slot state model valid slot kind children recorded rfl
  refine ⟨⟨_,.structural (.source _) length shape found⟩,⟨_,.source _⟩,?_⟩
  intro first last one two
  cases two
  cases one with
  | structural parent size same atIndex =>
    cases parent
    exact ⟨GeneralNominalFiniteBracket.shape_payload_below _ (state.view.canonical kind) _ _ size length atIndex found
        (subtype_trans same.2 shape.1),
      GeneralNominalFiniteBracket.shape_payload_below _ (state.view.canonical kind) _ _ length size found atIndex
        (subtype_trans shape.2 same.1)⟩

 theorem same_similar (same : GeneralNominalOriginTerms.Same model first last) : Similar model first last := by
  constructor
  · intro value seen
    obtain ⟨other,observed⟩ := same.2.1
    exact ⟨other,observed,same.2.2 value other seen observed⟩
  · intro value seen
    obtain ⟨other,observed⟩ := same.1
    have equal := same.2.2 other value observed seen
    exact ⟨other,observed,⟨equal.2,equal.1⟩⟩

 theorem structural_origin_same (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (kind : Fin state.view.kinds)
    (children : Fin (state.view.shapes kind).arity → Fin state.base.slots)
    (recorded : state.view.heads slot = .structural kind children)
    (index : Fin (state.view.shapes kind).arity) (origin : Origin)
    (parent : Similar model origin (.source (state.base.source slot))) :
    GeneralNominalOriginTerms.Same model
      (.structural origin (state.view.shapes kind) index.val)
      (.source (state.base.source (children index))) := by
  have canonical := structural_slot_same state model valid slot kind children recorded index
  have transport := structural_congr model origin (.source (state.base.source slot)) parent (state.view.shapes kind) index.val
  refine ⟨?_,canonical.2.1,?_⟩
  · obtain ⟨value,seen⟩ := canonical.1
    exact ⟨value,(transport value).mpr seen⟩
  · intro a b one two
    exact canonical.2.2 a b ((transport a).mp one) two

end Yulang.GeneralNominalStructuralOrigin188
