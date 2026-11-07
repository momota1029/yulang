import Yulang.CommonPatternDataSafety

/-! An actual evaluator for the original indexed Core data fragment.
Every source visit is retained, projections use the real value, and record
operands run in written order. Pattern defaults remain lazy in the separate
canonical matcher. Core constructors without an evaluation clause report an
explicit unsupported error; they are never represented by silent computation
to discharge a safety contract. The source gate also rejects embedded values
outside the Common data fragment, although their runtime clause returns them.

This fragment includes literals, embedded data, indexed variables, products,
records, projections, variants and transparent leaves. It does not implement
functions, recursion, effects, lets or nested cases. -/

namespace Yulang.CommonCoreDataEvaluation

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration (Comp)
open CommonData (Value ValueTyping)
open CaseValues (Bindings)
open EvaluationTrace (Logged)

inductive Error where
  | unsupported
  | data : CaseDataTerms.Error → Error
  deriving DecidableEq, Repr

abbrev Result := Logged (CaseEvaluation.Event Required.Term) Error Value

def pure (value : Value) : Result := Logged.ofResult (.ok value)
def fail (error : CaseDataTerms.Error) : Result := Logged.ofResult (.error (.data error))

def eval (environment : Bindings Empty) (code : Required.Term) : Result :=
  Logged.prepend [.source code] <|
    match code with
    | .literal value => pure (.literal value)
    | .data value => pure value
    | .var index => match environment[index]? with
      | some (_, value) => pure value
      | none => fail (.unboundVariable index)
    | .pair first last => (eval environment first).bind fun left =>
        (eval environment last).bind fun right => pure (.pair left right)
    | .fst source => (eval environment source).bind fun value => match value with
      | .pair first _ => pure first
      | _ => fail .expectedPair
    | .snd source => (eval environment source).bind fun value => match value with
      | .pair _ last => pure last
      | _ => fail .expectedPair
    | .emptyRecord => pure (.record [])
    | .record name head tail => (eval environment head).bind fun first =>
        (eval environment tail).bind fun rest => match rest with
          | .record fields => pure (.record (CaseDataTerms.insert name first fields))
          | _ => fail .expectedRecord
    | .recordDefault name source fallback => (eval environment source).bind fun base =>
        (eval environment fallback).bind fun value => match base with
          | .record fields => pure (.record (CaseDataTerms.insertDefault name value fields))
          | _ => fail .expectedRecord
    | .field name source => (eval environment source).bind fun value => match value with
      | .record fields => match CaseValues.lookup name fields with
        | some item => pure item
        | none => fail (.missingField name)
      | _ => fail .expectedRecord
    | .variant tag payload => (eval environment payload).bind fun value => pure (.variant tag value)
    | .leaf source => eval environment source
    | _ => Logged.ofResult (.error .unsupported)

inductive Supported : Required.Term → Prop where
  | literal (value) : Supported (.literal value)
  | data (value) : CommonData.covered value = true → Supported (.data value)
  | var (index) : Supported (.var index)
  | pair : Supported first → Supported last → Supported (.pair first last)
  | fst : Supported source → Supported (.fst source)
  | snd : Supported source → Supported (.snd source)
  | emptyRecord : Supported .emptyRecord
  | record (name) : Supported head → Supported tail → Supported (.record name head tail)
  | recordDefault (name) : Supported source → Supported fallback → Supported (.recordDefault name source fallback)
  | field (name) : Supported source → Supported (.field name source)
  | variant (tag) : Supported payload → Supported (.variant tag payload)
  | leaf : Supported source → Supported (.leaf source)

def supported : Required.Term → Bool
  | .literal _ | .var _ | .emptyRecord => true
  | .data value => CommonData.covered value
  | .pair first last | .record _ first last | .recordDefault _ first last => supported first && supported last
  | .fst source | .snd source | .field _ source | .variant _ source | .leaf source => supported source
  | _ => false

theorem supported_of_check (code : Required.Term) (checked : supported code = true) : Supported code := by
  cases code <;> simp only [supported, Bool.and_eq_true] at checked
  case literal value => exact .literal value
  case data value => exact .data value checked
  case var index => exact .var index
  case pair first last => exact .pair (supported_of_check first checked.1) (supported_of_check last checked.2)
  case fst source => exact .fst (supported_of_check source checked)
  case snd source => exact .snd (supported_of_check source checked)
  case emptyRecord => exact .emptyRecord
  case record name head tail => exact .record name (supported_of_check head checked.1) (supported_of_check tail checked.2)
  case recordDefault name source fallback =>
    exact .recordDefault name (supported_of_check source checked.1) (supported_of_check fallback checked.2)
  case field name source => exact .field name (supported_of_check source checked)
  case variant tag payload => exact .variant tag (supported_of_check payload checked)
  case leaf source => exact .leaf (supported_of_check source checked)
  all_goals cases checked

theorem supported_exact (code : Required.Term) : supported code = true ↔ Supported code := by
  constructor
  · exact supported_of_check code
  · intro within
    induction within <;> simp_all [supported]

/-- Indexed environments validate every instance of each original binding.
The runtime never resolves a Core index again by a possibly shadowed name. -/
def EnvironmentHolds (environment : List (CommonSyntax.Binding Common.model))
    (actual : Bindings Empty) : Prop :=
  ∀ index result, CommonSyntax.Lookup Common.model environment index result →
    ∃ name value, actual[index]? = some (name, value) ∧ ValueTyping Common.model value result

@[local simp] private theorem except_bind_ok (value : A) (next : A → Except R B) :
    (Except.ok value).bind next = next value := rfl

/-- Ordinary independent typing of the supported original Core term derives
actual successful evaluation and value typing. No success or interpreter
soundness is assumed, and every indexed captured environment is quantified. -/
theorem typing_evaluates (within : Supported code) :
    ∀ environment actual result, EnvironmentHolds environment actual →
      CommonSyntax.Typing Common.model environment code result →
      ∃ value, (eval actual code).result = .ok value ∧ ValueTyping Common.model value result := by
  induction within with
  | literal literal =>
      intro environment actual result valid typed
      cases typed with | literal bounded => exact ⟨.literal literal, rfl, .literal bounded⟩
  | data value _ =>
      intro environment actual result valid typed
      cases typed with | data typed => exact ⟨value, rfl, typed⟩
  | var index =>
      intro environment actual result valid typed
      obtain ⟨name, value, found, safe⟩ := valid index result ((CommonSyntax.var_iff _ _ _).mp typed)
      exact ⟨value, by simp [eval, found, pure, Logged.ofResult], safe⟩
  | pair _ _ ihf ihl =>
      intro environment actual result valid typed
      cases typed with
      | pair left right bounded =>
          obtain ⟨a, leftEval, leftType⟩ := ihf environment actual _ valid left
          obtain ⟨b, rightEval, rightType⟩ := ihl environment actual _ valid right
          exact ⟨.pair a b,
            by simp [eval, Logged.bind_result, leftEval, rightEval, pure, Logged.ofResult],
            .pair leftType rightType bounded⟩
  | fst _ ih =>
      intro environment actual result valid typed
      cases typed with
      | fst child bounded =>
          obtain ⟨value, evaluated, safe⟩ := ih environment actual _ valid child
          obtain ⟨first, last, rfl, left, _⟩ := CommonPatternLookup.pair_components safe _ _ (Common.subtype_refl _)
          exact ⟨first, by simp [eval, Logged.bind_result, evaluated, pure, Logged.ofResult],
            CommonPatternLookup.typing_change_result left result bounded.1⟩
  | snd _ ih =>
      intro environment actual result valid typed
      cases typed with
      | snd child bounded =>
          obtain ⟨value, evaluated, safe⟩ := ih environment actual _ valid child
          obtain ⟨first, last, rfl, _, right⟩ := CommonPatternLookup.pair_components safe _ _ (Common.subtype_refl _)
          exact ⟨last, by simp [eval, Logged.bind_result, evaluated, pure, Logged.ofResult],
            CommonPatternLookup.typing_change_result right result bounded.1⟩
  | emptyRecord =>
      intro environment actual result valid typed
      cases typed with | emptyRecord bounded => exact ⟨.record [], rfl, .emptyRecord bounded⟩
  | record name _ _ ihh iht =>
      intro environment actual result valid typed
      cases typed with
      | record head tail width bounded =>
          obtain ⟨a, headEval, headType⟩ := ihh environment actual _ valid head
          obtain ⟨b, tailEval, tailType⟩ := iht environment actual _ valid tail
          obtain ⟨fields, rfl⟩ := CommonPatternLookup.records_of_width tailType width
          exact ⟨.record (CaseDataTerms.insert name a fields),
            by simp [eval, Logged.bind_result, headEval, tailEval, pure, Logged.ofResult],
            CommonPatternLookup.typing_change_result
              (CommonPatternConcreteValueTypes.insertion_typed name a fields headType tailType) result bounded.1⟩
  | recordDefault name _ _ ihs ihf =>
      intro environment actual result valid typed
      cases typed with
      | recordDefault source fallback width bounded =>
          obtain ⟨a, sourceEval, sourceType⟩ := ihs environment actual _ valid source
          obtain ⟨b, fallbackEval, fallbackType⟩ := ihf environment actual _ valid fallback
          obtain ⟨fields, rfl⟩ := CommonPatternLookup.records_of_width sourceType width
          exact ⟨.record (CaseDataTerms.insertDefault name b fields),
            by simp [eval, Logged.bind_result, sourceEval, fallbackEval, pure, Logged.ofResult],
            CommonPatternLookup.typing_change_result
              (CommonPatternConcreteValueTypes.default_insertion_typed name b fields sourceType fallbackType)
              result bounded.1⟩
  | field name _ ih =>
      intro environment actual result valid typed
      cases typed with
      | field child bounded =>
          rename_i payload row
          obtain ⟨value, evaluated, safe⟩ := ih environment actual _ valid child
          have width : Common.Subtype (Common.required name payload) Common.emptyRecord :=
            (CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr rfl
          obtain ⟨fields, rfl⟩ := CommonPatternLookup.records_of_width safe width
          obtain ⟨item, present, itemType⟩ := CommonPatternLookup.required_lookup fields _ name _ safe (Common.subtype_refl _)
          exact ⟨item, by simp [eval, Logged.bind_result, evaluated, present, pure, Logged.ofResult],
            CommonPatternLookup.typing_change_result itemType result bounded.1⟩
  | variant tag _ ih =>
      intro environment actual result valid typed
      cases typed with
      | variant child bounded =>
          obtain ⟨value, evaluated, safe⟩ := ih environment actual _ valid child
          exact ⟨.variant tag value, by simp [eval, Logged.bind_result, evaluated, pure, Logged.ofResult], .variant safe bounded⟩
  | leaf _ ih =>
      intro environment actual result valid typed
      cases typed with
      | leaf child =>
          obtain ⟨value, evaluated, safe⟩ := ih environment actual result valid child
          exact ⟨value, evaluated, safe⟩

end Yulang.CommonCoreDataEvaluation
