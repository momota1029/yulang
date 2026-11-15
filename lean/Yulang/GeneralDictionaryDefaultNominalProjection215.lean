import Yulang.GeneralNominalFiniteBracket
import Yulang.GeneralNominalHeadTestSemantic186

/-! Raw nominal descriptors constrain arbitrary actual observations, without
finite-expression reification, equal descriptor slots or a legacy trace. -/
namespace Yulang.GeneralDictionaryDefaultNominalProjection215
open CommonNominalFullCarrier GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOriginTerms (Head)
variable {state : GeneralNominalState.State} {model : Assignment}

theorem argument_symm {first last : Argument} (same : ArgumentEquivalent first last) : ArgumentEquivalent last first := by
  cases first <;> cases last
  · exact ⟨same.2,same.1⟩
  · exact False.elim same
  · exact False.elim same
  · exact same.symm

theorem child_fits
    (valid : GeneralNominalState.Models state model)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor)
    (found : descriptor.arguments[index]? = some (.type bounds))
    (related : ∀ value, Observes model parent value →
      Subtype (model (state.base.source slot)).1 value ∨ Subtype value (model (state.base.source slot)).1)
    (seen : Observes model (.nominal parent descriptor.declaration.name index) actual) :
    Fits state model bounds actual := by
  obtain ⟨arguments,fits,denoted⟩ := valid.2.1 slot descriptor recorded
  obtain ⟨value,located,fitted⟩ := GeneralNominalIntervalLaws.fitsAll_at state.base model
    descriptor.arguments arguments fits index (.type bounds) found
  cases seen with
  | nominal parentSeen equal atIndex =>
      have equivalent : ArgumentEquivalent value (.inl actual) := by
        rcases related _ parentSeen with below | above
        · exact ((nominal_regular_invariant_exact ..).mp
            (subtype_trans denoted.2 (subtype_trans below equal.1))).2.2 index _ _ located atIndex
        · have reverse := ((nominal_regular_invariant_exact ..).mp
            (subtype_trans equal.2 (subtype_trans above denoted.1))).2.2 index _ _ atIndex located
          cases value with
          | inl value => exact ⟨reverse.2,reverse.1⟩
          | inr row => exact False.elim reverse
      exact (GeneralNominalIntervalLaws.fits_equivalent state.base model (.type bounds)
        value (.inl actual) equivalent).mp fitted

def Bounded (state : GeneralNominalState.State) (model : Assignment)
    (bounds : GeneralNominalInspection.Bounds state) (origin : Origin) : Prop :=
  (∃ value, Observes model origin value) ∧ ∀ value, Observes model origin value → Fits state model bounds value

theorem child_inhabited
    (valid : GeneralNominalState.Models state model)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor)
    (found : descriptor.arguments[index]? = some (.type bounds))
    (related : ∀ value, Observes model parent value →
      Subtype (model (state.base.source slot)).1 value ∨ Subtype value (model (state.base.source slot)).1)
    (head : Head model parent (.nominal descriptor.declaration.name count)) :
    ∃ actual, Observes model (.nominal parent descriptor.declaration.name index) actual := by
  obtain ⟨observed,seen⟩ := head.1
  obtain ⟨args,_,equal⟩ := head.2 observed seen
  obtain ⟨arguments,fits,denoted⟩ := valid.2.1 slot descriptor recorded
  obtain ⟨value,located,fitted⟩ := GeneralNominalIntervalLaws.fitsAll_at state.base model
    descriptor.arguments arguments fits index (.type bounds) found
  have compared : Subtype (nominal descriptor.declaration.name arguments) (nominal descriptor.declaration.name args) ∨
      Subtype (nominal descriptor.declaration.name args) (nominal descriptor.declaration.name arguments) := by
    rcases related observed seen with below | above
    · exact Or.inl (subtype_trans denoted.2 (subtype_trans below equal.1))
    · exact Or.inr (subtype_trans equal.2 (subtype_trans above denoted.1))
  have sameLength : arguments.length = args.length := compared.elim
    (fun h => ((nominal_regular_invariant_exact ..).mp h).2.1)
    (fun h => ((nominal_regular_invariant_exact ..).mp h).2.1.symm)
  have within : index < args.length := sameLength ▸ (List.getElem?_eq_some_iff.mp located).1
  have atIndex : args[index]? = some args[index] := List.getElem?_eq_getElem within
  have equivalent : ArgumentEquivalent value args[index] := by
    rcases compared with below | above
    · exact ((nominal_regular_invariant_exact ..).mp below).2.2 index _ _ located atIndex
    · have reverse := ((nominal_regular_invariant_exact ..).mp above).2.2 index _ _ atIndex located
      exact argument_symm reverse
  cases value with
  | inr row => cases fitted
  | inl value =>
      cases h : args[index] with
      | inl actual => exact ⟨actual,.nominal seen equal (h ▸ atIndex)⟩
      | inr row => simp [h,ArgumentEquivalent] at equivalent

theorem nominal_bounded
    (valid : GeneralNominalState.Models state model)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor)
    (found : typeArguments descriptor.arguments = some intervals)
    (related : ∀ value, Observes model parent value →
      Subtype (model (state.base.source slot)).1 value ∨ Subtype value (model (state.base.source slot)).1)
    (head : Head model parent (.nominal descriptor.declaration.name count))
    (index : Fin intervals.length) :
    Bounded state model intervals[index] (.nominal parent descriptor.declaration.name index.val) := by
  have parameter : descriptor.arguments[index.val]? = some (.type intervals[index]) := by
    rw [GeneralNominalInspectionFiniteValues.type_arguments _ found]
    simp
  exact ⟨child_inhabited valid slot descriptor recorded parameter related head,
    fun _ seen => child_fits valid slot descriptor recorded parameter related seen⟩

end Yulang.GeneralDictionaryDefaultNominalProjection215
