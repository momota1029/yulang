import Yulang.PresenceDataInference

/-!
# Presence-aware data typing and the actual source evaluator

Typing soundness is proved by induction on the independent judgment, for every
runtime environment satisfying its declared semantic types. It does not assume
that inference succeeds. The computed principal descriptor then yields a
separate execution theorem, including unconditional evaluation of both default
operands in the existing `SourceDataRuntime.eval`.

The open two-input default operator also has an exact semantic-image principal
type. Thus the unknown optional-field contract is not merely a collection of
closed, statically known examples. These are data-model theorems, not a claim
that the legacy function/regular/effect solver now handles optional records.
-/

namespace Yulang.PresenceDataSafety

open Inference (Expr)
open SourceDataRuntime (Value eval)
open PresenceDataTypes
open PresenceDataShapes (Shape)
open PresenceDataInference (Typing infer Result)

@[local simp] private theorem bind_ok (value : α) (next : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= next) = next value := rfl

@[local simp] private theorem map_ok (value : α) (map : α → β) :
    map <$> (Except.ok value : Except ε α) = Except.ok (map value) := rfl

@[local simp] private theorem pure_ok (value : α) :
    (pure value : Except ε α) = Except.ok value := rfl

def EnvironmentHolds (context : List Ty) (environment : List Value) : Prop :=
  ∀ (index : Nat) (type : Ty), context[index]? = some type →
    ∃ value, environment[index]? = some value ∧ type value

theorem EnvironmentHolds.nil : EnvironmentHolds [] [] := by
  intro index type found
  simp at found

theorem EnvironmentHolds.cons {context : List Ty} {environment : List Value}
    {type : Ty} {value : Value} (valid : type value)
    (rest : EnvironmentHolds context environment) :
    EnvironmentHolds (type :: context) (value :: environment) := by
  intro index target found
  cases index with
  | zero =>
      have same : type = target := by simpa using found
      subst target
      exact ⟨value, rfl, valid⟩
  | succ index => exact rest index target found

/-- Every data typing runs successfully and produces a value in the declared
type. No runtime type, shape, inferred plan, or evaluation fuel is supplied. -/
theorem typing_evaluates {context : List Ty} {expression : Expr} {type : Ty}
    (typed : Typing context expression type) (environment : List Value)
    (valid : EnvironmentHolds context environment) :
    ∃ value, eval environment expression = .ok value ∧ type value := by
  induction typed generalizing environment with
  | var found =>
      obtain ⟨value, present, valueValid⟩ := valid _ _ found
      exact ⟨value, by simp [eval, present], valueValid⟩
  | lit name => exact ⟨.base name, rfl, rfl⟩
  | emptyRecord => exact ⟨.record [], rfl, rfl⟩
  | letE _ _ first last =>
      obtain ⟨initial, firstRan, initialValid⟩ := first environment valid
      obtain ⟨result, lastRan, resultValid⟩ :=
        last (initial :: environment) (EnvironmentHolds.cons initialValid valid)
      exact ⟨result, by simp [eval, firstRan, lastRan], resultValid⟩
  | pair _ _ first last =>
      obtain ⟨left, leftRan, leftValid⟩ := first environment valid
      obtain ⟨right, rightRan, rightValid⟩ := last environment valid
      exact ⟨.pair left right, by simp [eval, leftRan, rightRan], leftValid, rightValid⟩
  | fst _ child =>
      obtain ⟨value, ran, valueValid⟩ := child environment valid
      cases value with
      | pair first last => exact ⟨first, by simp [eval, ran], valueValid.1⟩
      | base | record | variant => cases valueValid
  | snd _ child =>
      obtain ⟨value, ran, valueValid⟩ := child environment valid
      cases value with
      | pair first last => exact ⟨last, by simp [eval, ran], valueValid.2⟩
      | base | record | variant => cases valueValid
  | @record context headExpr headType tailExpr tailType label _ _ admissible head tail =>
      obtain ⟨first, firstRan, firstValid⟩ := head environment valid
      obtain ⟨last, lastRan, lastValid⟩ := tail environment valid
      have recordShape := admissible _ lastValid
      cases last with
      | record fields =>
          refine ⟨.record (SourceDataRuntime.Fields.insert label first fields),
            by simp [eval, firstRan, lastRan], ?_⟩
          exact ⟨first, fields, firstValid, lastValid, rfl⟩
      | base | pair | variant => cases recordShape
  | @recordDefault context sourceExpr sourceType fallbackExpr fallbackType label _ _ admissible source fallback =>
      obtain ⟨first, firstRan, firstValid⟩ := source environment valid
      obtain ⟨last, lastRan, lastValid⟩ := fallback environment valid
      have recordShape := admissible _ firstValid
      cases first with
      | record fields =>
          refine ⟨.record (SourceDataRuntime.Fields.insertDefault label last fields),
            by simp [eval, firstRan, lastRan], ?_⟩
          exact ⟨fields, last, firstValid, lastValid, rfl⟩
      | base | pair | variant => cases recordShape
  | @field context expression label payload _ child =>
      obtain ⟨value, ran, valueValid⟩ := child environment valid
      cases value with
      | record fields =>
          obtain ⟨_, result, found, resultValid⟩ := valueValid
          change SourceDataRuntime.Fields.lookup label fields = some result at found
          exact ⟨result, by simp [eval, ran, found], resultValid⟩
      | base | pair | variant => cases valueValid.1
  | variant _ child =>
      obtain ⟨value, ran, valueValid⟩ := child environment valid
      exact ⟨.variant _ value, by simp [eval, ran], rfl, valueValid⟩
  | subsume _ below child =>
      obtain ⟨value, ran, valueValid⟩ := child environment valid
      exact ⟨value, ran, below _ valueValid⟩

theorem closed_typing_evaluates (expression : Expr) (type : Ty)
    (typed : Typing [] expression type) :
    ∃ value, eval [] expression = .ok value ∧ type value :=
  typing_evaluates typed [] .nil

/-- The real returned descriptor describes the real runtime result, for every
closed expression accepted by this entry. No evaluator is used by `infer`. -/
theorem inferred_evaluates (expression : Expr) (shape : Shape)
    (inferred : infer expression = .solved shape) :
    eval [] expression = .ok shape.value := by
  have typed := (PresenceDataInference.infer_instances_exact expression shape.denote).mpr
    ⟨shape, inferred, le_refl _⟩
  obtain ⟨value, ran, same⟩ := closed_typing_evaluates expression shape.denote typed
  exact same ▸ ran

theorem inferred_no_error (expression : Expr) (shape : Shape)
    (inferred : infer expression = .solved shape) (error : SourceDataRuntime.Error) :
    eval [] expression ≠ .error error := by
  rw [inferred_evaluates expression shape inferred]
  intro impossible
  cases impossible

theorem instance_evaluates (expression : Expr) (target : Ty)
    (accepted : ∃ shape, infer expression = .solved shape ∧ Le shape.denote target) :
    ∃ value, eval [] expression = .ok value ∧ target value :=
  closed_typing_evaluates expression target
    ((PresenceDataInference.infer_instances_exact expression target).mpr accepted)

/-! ## A principal contract for an unknown base and fallback -/

def defaultOperator (label : Nat) : Expr := .recordDefault label (.var 0) (.var 1)

/-- The semantic image is the least possible result type of the actual open
default expression, for arbitrary input types and every target predicate.
Record admissibility is an input-kind condition, not a residual solver premise. -/
theorem default_operator_principal (label : Nat) (source fallback target : Ty)
    (admissible : Le source records) :
    Typing [source, fallback] (defaultOperator label) target ↔
      Le (recordDefault label source fallback) target := by
  constructor
  · intro typed result accepted
    obtain ⟨fields, value, sourceValid, fallbackValid, rfl⟩ := accepted
    have environment := EnvironmentHolds.cons sourceValid (EnvironmentHolds.cons fallbackValid .nil)
    obtain ⟨actual, ran, valid⟩ := typing_evaluates typed [.record fields, value] environment
    have same : Value.record (SourceDataRuntime.Fields.insertDefault label value fields) = actual := by
      simpa [defaultOperator, eval] using ran
    simpa [← same] using valid
  · intro below
    exact .subsume (.recordDefault (.var rfl) (.var rfl) admissible) below

/-- Unknown optional fields use precisely the same open-expression principal
contract; no finite exact base shape or witness of field presence is supplied. -/
theorem optional_operator_principal (label : Nat) (payload fallback target : Ty) :
    Typing [optional label payload, fallback] (defaultOperator label) target ↔
      Le (recordDefault label (optional label payload) fallback) target :=
  default_operator_principal label _ _ _ (optional_records label payload)

theorem optional_operator_union (label : Nat) (payload fallback : Ty) :
    Typing [optional label payload, fallback] (defaultOperator label)
      (required label (union payload fallback)) :=
  (optional_operator_principal label payload fallback _).mpr
    (recordDefault_optional label _ payload fallback (le_refl _))

end Yulang.PresenceDataSafety
