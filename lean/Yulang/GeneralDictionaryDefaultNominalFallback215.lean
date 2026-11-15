import Yulang.GeneralDictionaryDefaultNominalProjection215

/-! Nominal fallback endpoints and actual centers agree semantically under
one-sided bounds. No point descriptor or finite reification is required. -/
namespace Yulang.GeneralDictionaryDefaultNominalFallback215
open CommonNominalFullCarrier GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralNominalCommonBridge (Assignment)
variable {state : GeneralNominalState.State} {model : Assignment}

theorem nominal_reverse (below : Subtype (nominal name first) (nominal other last)) :
    Subtype (nominal other last) (nominal name first) := by
  obtain ⟨names,length,args⟩ := (nominal_regular_invariant_exact ..).mp below
  apply (nominal_regular_invariant_exact ..).mpr
  exact ⟨names.symm,length.symm,fun index a b one two =>
    GeneralDictionaryDefaultNominalProjection215.argument_symm (args index b a two one)⟩

theorem parent_same
    (valid : GeneralNominalState.Models state model)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor)
    (related : ∀ value, Observes model parent value →
      Subtype (model (state.base.source slot)).1 value ∨ Subtype value (model (state.base.source slot)).1)
    (head : Head model parent (.nominal name count)) :
    Same model parent (.source (state.base.source slot)) := by
  obtain ⟨arguments,_,denoted⟩ := valid.2.1 slot descriptor recorded
  refine ⟨head.1,⟨_,.source _⟩,?_⟩
  intro value other seen source
  cases source
  obtain ⟨args,_,equal⟩ := head.2 value seen
  rcases related value seen with below | above
  · have comp := subtype_trans denoted.2 (subtype_trans below equal.1)
    exact ⟨subtype_trans equal.1 (subtype_trans (nominal_reverse comp) denoted.2),below⟩
  · have comp := subtype_trans equal.2 (subtype_trans above denoted.1)
    exact ⟨above,subtype_trans denoted.1 (subtype_trans (nominal_reverse comp) equal.2)⟩

end Yulang.GeneralDictionaryDefaultNominalFallback215
