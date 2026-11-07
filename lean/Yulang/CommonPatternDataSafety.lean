import Yulang.CommonPatternConcreteValueTypes
import Yulang.CommonPatternSourceScope
import Yulang.CommonPatternTyping

/-! Logical environments for the concrete finite data evaluator. A captured
binding retains all of its Common instances, including captured poly lets.
This does not assert success or termination for effectful source languages. -/

namespace Yulang.CommonPatternDataSafety

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration (Comp)
open CommonData (Value ValueTyping)
open CaseValues (Bindings lookup)
open EvaluationTrace (Logged)

@[local simp] private theorem except_bind_ok (value : A) (next : A → Except R B) :
    (Except.ok value).bind next = next value := rfl

def EnvironmentHolds (scope : List Nat) (environment : List (CommonSyntax.Binding Common.model))
    (actual : Bindings Empty) : Prop :=
  ∀ name index result, Data.resolve name scope = some index →
    CommonSyntax.Lookup Common.model environment index result →
      ∃ value, lookup name actual = some value ∧ ValueTyping Common.model value result

theorem EnvironmentHolds.nil (scope : List Nat) (actual : Bindings Empty) : EnvironmentHolds scope [] actual := by
  intro name index result resolved typed
  rcases typed with ⟨binding, found, typed⟩
  simp at found

theorem EnvironmentHolds.cons (holds : EnvironmentHolds scope environment actual)
    (name : Nat) (value : Value) (binding : CommonSyntax.Binding Common.model)
    (instances : ∀ result, CommonSyntax.BindingTyping Common.model binding result → ValueTyping Common.model value result) :
    EnvironmentHolds (name :: scope) (binding :: environment) ((name, value) :: actual) := by
  intro queried index result resolved typed
  by_cases same : queried = name
  · subst queried
    have zero : index = 0 := by simpa only [Data.resolve, ↓reduceIte, Option.some.injEq] using resolved.symm
    subst index
    have bindingTyped : CommonSyntax.BindingTyping Common.model binding result := by simpa [CommonSyntax.Lookup] using typed
    exact ⟨value, by simp [lookup], instances result bindingTyped⟩
  · simp only [Data.resolve, same, ↓reduceIte] at resolved
    cases found : Data.resolve queried scope with
    | none => simp [found] at resolved
    | some previous =>
        have successor : index = previous + 1 := by simpa [found] using resolved.symm
        subst index
        obtain ⟨item, present, valid⟩ := holds queried previous result found
          (by simpa [CommonSyntax.Lookup] using typed)
        exact ⟨item, by simpa [lookup, same] using present, valid⟩

private theorem record_below_width (label : Nat) (payload tail : Common.Ty) :
    Common.Subtype (Common.record label payload tail) Common.emptyRecord := by
  intro depth
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank environment observation accepted
  cases rank <;> cases observation <;>
    simp_all [Common.observeTy, Common.record, Common.emptyRecord, CommonSyntax.Layer.evalAt,
      CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

private theorem eval_pair (first last : CaseDataTerms.Expr Empty) (actual : Bindings Empty)
    (left : (CaseDataTerms.eval actual first).result = .ok a)
    (right : (CaseDataTerms.eval actual last).result = .ok b) :
    (CaseDataTerms.eval actual (.pair first last)).result = .ok (.pair a b) := by
  simp [CaseDataTerms.eval, Logged.bind_result, left, right, CaseDataTerms.pure, Logged.ofResult]

theorem typing_evaluates (expression : CaseDataTerms.Expr Empty) :
    ∀ scope environment actual result, EnvironmentHolds scope environment actual →
      CommonSyntax.Typing Common.model environment (Data.embed scope expression) result →
      ∃ value, (CaseDataTerms.eval actual expression).result = .ok value ∧ ValueTyping Common.model value result := by
  induction expression with
  | value value =>
      intro scope environment actual result valid typed
      cases typed with | data typed => exact ⟨value, rfl, typed⟩
  | var name =>
      intro scope environment actual result valid typed
      simp only [Data.embed, Data.localVar] at typed
      cases resolved : Data.resolve name scope with
      | none => rw [resolved] at typed; cases typed
      | some index =>
          rw [resolved] at typed
          obtain ⟨value, present, safe⟩ := valid name index result resolved ((CommonSyntax.var_iff _ _ _).mp typed)
          exact ⟨value, by simp [CaseDataTerms.eval, present, CaseDataTerms.pure, Logged.ofResult], safe⟩
  | pair first last ihf ihl =>
      intro scope environment actual result valid typed
      cases typed with
      | pair left right bounded =>
          obtain ⟨a, leftEval, leftType⟩ := ihf scope environment actual _ valid left
          obtain ⟨b, rightEval, rightType⟩ := ihl scope environment actual _ valid right
          exact ⟨.pair a b, eval_pair first last actual leftEval rightEval, .pair leftType rightType bounded⟩
  | fst source ih =>
      intro scope environment actual result valid typed
      cases typed with
      | fst pair bounded =>
          obtain ⟨value, evaluated, safe⟩ := ih scope environment actual _ valid pair
          obtain ⟨first, last, rfl, left, right⟩ := CommonPatternLookup.pair_components safe _ _ (Common.subtype_refl _)
          exact ⟨first, by simp [CaseDataTerms.eval, Logged.bind_result, evaluated, CaseDataTerms.pure, Logged.ofResult],
            CommonPatternLookup.typing_change_result left result bounded.1⟩
  | snd source ih =>
      intro scope environment actual result valid typed
      cases typed with
      | snd pair bounded =>
          obtain ⟨value, evaluated, safe⟩ := ih scope environment actual _ valid pair
          obtain ⟨first, last, rfl, left, right⟩ := CommonPatternLookup.pair_components safe _ _ (Common.subtype_refl _)
          exact ⟨last, by simp [CaseDataTerms.eval, Logged.bind_result, evaluated, CaseDataTerms.pure, Logged.ofResult],
            CommonPatternLookup.typing_change_result right result bounded.1⟩
  | emptyRecord =>
      intro scope environment actual result valid typed
      cases typed with | emptyRecord bounded => exact ⟨.record [], rfl, .emptyRecord bounded⟩
  | record name first last ihf ihl =>
      intro scope environment actual result valid typed
      cases typed with
      | record left right width bounded =>
          obtain ⟨a, leftEval, leftType⟩ := ihf scope environment actual _ valid left
          obtain ⟨b, rightEval, rightType⟩ := ihl scope environment actual _ valid right
          obtain ⟨fields, rfl⟩ := CommonPatternLookup.records_of_width rightType width
          refine ⟨.record (CaseDataTerms.insert name a fields), ?_, ?_⟩
          · simp [CaseDataTerms.eval, Logged.bind_result, leftEval, rightEval, CaseDataTerms.pure, Logged.ofResult]
          · exact CommonPatternLookup.typing_change_result
              (CommonPatternConcreteValueTypes.insertion_typed name a fields leftType rightType) result bounded.1
  | recordDefault name source fallback ihs ihf =>
      intro scope environment actual result valid typed
      cases typed with
      | recordDefault base default width bounded =>
          obtain ⟨a, baseEval, baseType⟩ := ihs scope environment actual _ valid base
          obtain ⟨b, fallbackEval, fallbackType⟩ := ihf scope environment actual _ valid default
          obtain ⟨fields, rfl⟩ := CommonPatternLookup.records_of_width baseType width
          refine ⟨.record (CaseDataTerms.insertDefault name b fields), ?_, ?_⟩
          · simp [CaseDataTerms.eval, Logged.bind_result, baseEval, fallbackEval, CaseDataTerms.pure, Logged.ofResult]
          · exact CommonPatternLookup.typing_change_result
              (CommonPatternConcreteValueTypes.default_insertion_typed name b fields baseType fallbackType) result bounded.1
  | field name source ih =>
      intro scope environment actual result valid typed
      cases typed with
      | field sourceTyped bounded =>
          obtain ⟨value, evaluated, safe⟩ := ih scope environment actual _ valid sourceTyped
          obtain ⟨fields, rfl⟩ := CommonPatternLookup.records_of_width safe (record_below_width name _ _)
          obtain ⟨item, present, itemType⟩ := CommonPatternLookup.required_lookup fields _ name _ safe (Common.subtype_refl _)
          exact ⟨item, by simp [CaseDataTerms.eval, Logged.bind_result, evaluated, present, CaseDataTerms.pure, Logged.ofResult],
            CommonPatternLookup.typing_change_result itemType result bounded.1⟩
  | variant tag payload ih =>
      intro scope environment actual result valid typed
      cases typed with
      | variant child bounded =>
          obtain ⟨value, evaluated, safe⟩ := ih scope environment actual _ valid child
          exact ⟨.variant tag value,
            by simp [CaseDataTerms.eval, Logged.bind_result, evaluated, CaseDataTerms.pure, Logged.ofResult], .variant safe bounded⟩
  | nominal | nil | cons =>
      intro scope environment actual result valid typed
      have accepted := CommonSyntax.typing_covered typed
      simp [Data.embed, CommonSyntax.covered] at accepted
  | letE name definition body ihd ihb =>
      intro scope environment actual result valid typed
      cases typed with
      | letComputed definitionTyped bodyTyped bounded =>
          rename_i input bodyResult
          obtain ⟨value, evaluated, safe⟩ := ihd scope environment actual _ valid definitionTyped
          have extended := valid.cons name value (.mono (Comp.pure Common.model input.1)) (fun computation bindingTyped =>
            CommonPatternLookup.typing_change_result safe computation ((CommonSyntax.mono_iff _ _).mp bindingTyped).1)
          obtain ⟨output, bodyEval, bodyType⟩ := ihb (name :: scope) _ ((name, value) :: actual) _ extended bodyTyped
          exact ⟨output, by simp [CaseDataTerms.eval, Logged.bind_result, evaluated, bodyEval],
            CommonPatternLookup.typing_change_result bodyType result bounded.1⟩
      | letValue isValue definitionTyped bodyTyped =>
          obtain ⟨value, evaluated, safe⟩ := ihd scope environment actual _ valid definitionTyped
          have instances : ∀ computation,
              CommonSyntax.BindingTyping Common.model (.poly (Data.embed scope definition) environment) computation →
                ValueTyping Common.model value computation := by
            intro computation bindingTyped
            have definitionInstance := ((CommonSyntax.poly_iff _ _ _).mp bindingTyped).1
            obtain ⟨other, otherEval, otherType⟩ := ihd scope environment actual _ valid definitionInstance
            have same : other = value := Except.ok.inj (otherEval.symm.trans evaluated)
            subst other
            exact CommonPatternLookup.typing_change_result otherType computation (Common.subtype_refl _)
          obtain ⟨output, bodyEval, bodyType⟩ := ihb (name :: scope) _ ((name, value) :: actual) _
            (valid.cons name value _ instances) bodyTyped
          exact ⟨output, by simp [CaseDataTerms.eval, Logged.bind_result, evaluated, bodyEval], bodyType⟩

open CommonPatternEnvironment (NamedTypes)
open CommonPatternTyping (bindingTypes)
open CommonPatternSourceScope (corePrefix)

/-- The actual ordered mono prefix extends an arbitrary captured logical
environment. Names may shadow the suffix; prefix order is unchanged. -/
theorem prefix_environment (types : NamedTypes) (actualPrefix : Bindings Empty)
    (valid : CaseValues.BindingsHold (bindingTypes types) actualPrefix)
    (outer : EnvironmentHolds outerNames environment actualOuter) :
    EnvironmentHolds (types.map Prod.fst ++ outerNames) (corePrefix types ++ environment)
      (actualPrefix ++ actualOuter) := by
  induction types generalizing actualPrefix with
  | nil => cases valid; exact outer
  | cons binding rest ih =>
      rcases binding with ⟨name, type⟩
      cases valid with
      | cons head tail =>
          exact (ih _ tail).cons name _ (.mono (Comp.pure Common.model type))
            (fun result typed => CommonPatternLookup.typing_change_result head result
              ((CommonSyntax.mono_iff _ _).mp typed).1)

end Yulang.CommonPatternDataSafety
