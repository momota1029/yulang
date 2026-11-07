import Yulang.CommonNominalRegularErasure
import Yulang.CommonNominalFullTypingPreservation

/-!
# Old Core typing reflected from arbitrary new intermediate witnesses

The block-preserving erasure transports all structural typing rules. Captured
polymorphism is retained. A prescribed new signature is related only when each
of its selected instances has an old preimage after erasure; the actual mapped
old signatures satisfy this by freezing their original retract-selected tuple.
No commutation law for arbitrary user-supplied signature functions is assumed.
-/

namespace Yulang.CommonNominalFullTypingReflection

open Core.PresenceGeneration (Comp)

abbrev Full := CommonNominalFullCarrier.model
abbrev comp (result : Comp Full) : Comp Common.model :=
  (CommonNominalRegularErasure.layer result.1, result.2)

theorem comp_le {first last : Comp Full} (below : Comp.le Full first last) :
    Comp.le Common.model (comp first) (comp last) :=
  ⟨CommonNominalRegularErasure.subtype_monotone _ _ below.1, below.2⟩

mutual
  inductive Related : Core.CommonSyntax.Binding Common.model → Core.CommonSyntax.Binding Full → Prop where
    | mono (result : Comp Full) : Related (.mono (comp result)) (.mono result)
    | poly {expression oldCaptured newCaptured} : Environments oldCaptured newCaptured →
        Related (.poly expression oldCaptured) (.poly expression newCaptured)
    | signature {oldCount newCount : Nat}
        {oldInstantiate : (Fin oldCount → Common.model.Ty) → Comp Common.model}
        {newInstantiate : (Fin newCount → Full.Ty) → Comp Full} :
        (∀ parameters, ∃ oldParameters,
          oldInstantiate oldParameters = comp (newInstantiate parameters)) →
        Related (.signature oldCount oldInstantiate) (.signature newCount newInstantiate)

  inductive Environments : List (Core.CommonSyntax.Binding Common.model) →
      List (Core.CommonSyntax.Binding Full) → Prop where
    | nil : Environments [] []
    | cons : Related oldBinding newBinding → Environments oldRest newRest →
        Environments (oldBinding :: oldRest) (newBinding :: newRest)
end

private theorem environments_at {oldEnvironment newEnvironment} {index : Nat}
    (related : Environments oldEnvironment newEnvironment) {newBinding}
    (found : newEnvironment[index]? = some newBinding) :
    ∃ oldBinding, oldEnvironment[index]? = some oldBinding ∧ Related oldBinding newBinding := by
  induction index generalizing oldEnvironment newEnvironment with
  | zero =>
      cases related with
      | nil => simp at found
      | cons head rest =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst newBinding
          exact ⟨_, rfl, head⟩
  | succ index ih =>
      cases related with
      | nil => simp at found
      | cons head rest => exact ih rest found

private theorem data_erased {value : Core.CommonData.Value} {result : Comp Full}
    (typed : Core.CommonData.ValueTyping Full value result) :
    Core.CommonData.ValueTyping Common.model value (comp result) := by
  induction typed with
  | literal bounded => exact .literal (comp_le bounded)
  | pair _ _ bounded first last => exact .pair first last (comp_le bounded)
  | emptyRecord bounded => exact .emptyRecord (comp_le bounded)
  | record _ _ recordType bounded head rest =>
      exact .record head rest (CommonNominalRegularErasure.subtype_monotone _ _ recordType) (comp_le bounded)
  | variant _ bounded payload => exact .variant payload (comp_le bounded)

/-- Every full-carrier derivation, with arbitrary new intermediate regular
types. The environment relation handles mixed mono/poly/signature captures;
only the explicit signature instance preimage property is required there. -/
theorem typing_erased {newEnvironment : List (Core.CommonSyntax.Binding Full)}
    {expression : Core.CommonSyntax.Term} {result : Comp Full}
    (typed : Core.CommonSyntax.Typing Full newEnvironment expression result) :
    ∀ oldEnvironment, Environments oldEnvironment newEnvironment →
      Core.CommonSyntax.Typing Common.model oldEnvironment expression (comp result) := by
  induction typed using Core.CommonSyntax.Typing.rec
    (motive_2 := fun binding result _ => ∀ oldBinding, Related oldBinding binding →
      Core.CommonSyntax.BindingTyping Common.model oldBinding (comp result))
  all_goals try (intro old related)
  case var found _ ih =>
    obtain ⟨oldBinding, oldFound, bindingRelated⟩ := environments_at related found
    exact .var oldFound (ih oldBinding bindingRelated)
  case lit bounded => exact .lit (comp_le bounded)
  case literal bounded => exact .literal (comp_le bounded)
  case data typed => exact .data (data_erased typed)
  case lam bounded ih => exact .lam (ih _ (.cons (.mono _) related)) (comp_le bounded)
  case app =>
    rename_i Γ f a b ef x c typedF typedX bounded ihf ihx
    exact .app (a := comp a) (b := comp b) (ihf old related) (ihx old related) (comp_le bounded)
  case strictApp =>
    rename_i Γ f a b ef x actual c typedF typedX compatible bounded ihf ihx
    exact .strictApp (a := comp a) (b := comp b) (actual := comp actual)
      (ihf old related) (ihx old related) (comp_le compatible) (comp_le bounded)
  case letValue nonexpansive _ _ ihv ihb =>
    exact .letValue nonexpansive (ihv old related) (ihb _ (.cons (.poly related) related))
  case letComputed _ _ bounded ihv ihb =>
    exact .letComputed (ihv old related) (ihb _ (.cons (.mono _) related)) (comp_le bounded)
  case leaf _ ih => exact .leaf (ih old related)
  case caseName _ _ bounded ihs ihb =>
    exact .caseName (ihs old related) (ihb _ (.cons (.mono _) related)) (comp_le bounded)
  case branch _ _ _ bounded ihg ihy ihn =>
    exact .branch (ihg old related) (ihy old related) (ihn old related) (comp_le bounded)
  case pair _ _ bounded ihf ihl => exact .pair (ihf old related) (ihl old related) (comp_le bounded)
  case fst _ bounded ih => exact .fst (ih old related) (comp_le bounded)
  case snd _ bounded ih => exact .snd (ih old related) (comp_le bounded)
  case emptyRecord bounded => exact .emptyRecord (comp_le bounded)
  case record _ _ recordType bounded ihf ihl =>
    exact .record (ihf old related) (ihl old related)
      (CommonNominalRegularErasure.subtype_monotone _ _ recordType) (comp_le bounded)
  case recordDefault _ _ recordType bounded ihs ihf =>
    exact .recordDefault (ihs old related) (ihf old related)
      (CommonNominalRegularErasure.subtype_monotone _ _ recordType) (comp_le bounded)
  case field _ bounded ih => exact .field (ih old related) (comp_le bounded)
  case variant _ bounded ih => exact .variant (ih old related) (comp_le bounded)
  case mono bounded old related =>
    cases related with
    | mono => exact .mono (comp_le bounded)
  case poly _ rowBound ih old related =>
    cases related with
    | poly captured => exact .poly (ih _ captured) rowBound
  case signature =>
    rename_i result count instantiate parameters bounded old related
    cases related with
    | signature covers =>
        obtain ⟨oldParameters, same⟩ := covers parameters
        apply Core.CommonSyntax.BindingTyping.signature (ι := oldParameters)
        simpa only [same] using comp_le bounded

mutual
  /-- Every actually transported old binding has the required preimage
  property, including arbitrary prescribed signature functions. -/
  theorem binding_related (binding : Core.CommonSyntax.Binding Common.model) :
      Related binding (CommonNominalFullTypingPreservation.coreBinding binding) := by
    cases binding with
    | mono result =>
        have same : comp (CommonNominalFullTypingPreservation.comp result) = result := by
          exact Prod.ext (CommonNominalRegularErasure.layer_value result.1) rfl
        simpa only [CommonNominalFullTypingPreservation.coreBinding, same] using
          (Related.mono (CommonNominalFullTypingPreservation.comp result))
    | poly expression captured =>
        rw [CommonNominalFullTypingPreservation.coreBinding.eq_2]
        exact .poly (environment_related captured)
    | signature count instantiate =>
        rw [CommonNominalFullTypingPreservation.coreBinding.eq_3]
        apply Related.signature
        intro parameters
        refine ⟨fun index => CommonNominalFullModelMap.retract (parameters index), ?_⟩
        exact (Prod.ext (CommonNominalRegularErasure.layer_value _) rfl).symm

  theorem environment_related (environment : List (Core.CommonSyntax.Binding Common.model)) :
      Environments environment (environment.map CommonNominalFullTypingPreservation.coreBinding) := by
    cases environment with
    | nil => exact .nil
    | cons binding rest => exact .cons (binding_related binding) (environment_related rest)
end

/-- Every old environment, original source expression and old result. New
intermediate witnesses are arbitrary full regular nominal/Float carrier values;
they are not assumed to be old images. Captured signatures remain arbitrary. -/
theorem core_typing_reflected (environment : List (Core.CommonSyntax.Binding Common.model))
    (expression : Core.CommonSyntax.Term) (result : Comp Common.model)
    (typed : Core.CommonSyntax.Typing Full
      (environment.map CommonNominalFullTypingPreservation.coreBinding) expression
      (CommonNominalFullTypingPreservation.comp result)) :
    Core.CommonSyntax.Typing Common.model environment expression result := by
  have erased := typing_erased typed environment (environment_related environment)
  simpa only [comp, CommonNominalFullTypingPreservation.comp,
    CommonNominalRegularErasure.layer_value] using erased

theorem core_typing_exact (environment : List (Core.CommonSyntax.Binding Common.model))
    (expression : Core.CommonSyntax.Term) (result : Comp Common.model) :
    Core.CommonSyntax.Typing Full
      (environment.map CommonNominalFullTypingPreservation.coreBinding) expression
      (CommonNominalFullTypingPreservation.comp result) ↔
        Core.CommonSyntax.Typing Common.model environment expression result :=
  ⟨core_typing_reflected environment expression result,
    CommonNominalFullTypingPreservation.core_typing_preserved_in_environment⟩

end Yulang.CommonNominalFullTypingReflection
