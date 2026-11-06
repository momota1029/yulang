import Yulang.PresenceDataSafety
import Yulang.ShadowDataSafety

/-!
# Agreement between exact data inference and the source runtime

The two executable algorithms remain independent: `synth` inspects source
expressions and type descriptors; `eval` inspects source expressions and runtime
values. Structural induction proves their success results agree for every
expression and every exact descriptor environment, including malformed data
operations and the explicitly unsupported constructors.

This yields a compatibility theorem with the earlier Shadow record models.
Their independent typing judgments imply that the new inference succeeds and
that its principal descriptor's value satisfies the earlier target type.
This does not identify the two type universes, their subtype relations, or
their notions of principal type.
-/

namespace Yulang.PresenceDataCompatibility

open Inference (Expr)
open SourceDataRuntime (Value eval)
open PresenceDataShapes (Shape ShapeFields)
open PresenceDataInference (synth infer)

@[local simp] private theorem toOption_bind (first : Except ε α)
    (next : α → Except ε β) :
    (first >>= next).toOption = first.toOption.bind (fun value => (next value).toOption) := by
  cases first <;> rfl

@[local simp] private theorem toOption_pure (value : α) :
    (pure value : Except ε α).toOption = some value := rfl

/-- Projecting away the runtime error code makes the separately executable
algorithms agree. The statement has no support, typing or success hypothesis. -/
theorem eval_toOption (environment : List Shape) (expression : Expr) :
    (eval (environment.map Shape.value) expression).toOption =
      (synth environment expression).map Shape.value := by
  induction expression generalizing environment with
  | var index =>
      simp only [eval, synth, List.getElem?_map]
      cases environment[index]? <;> rfl
  | lit name => rfl
  | emptyRecord => rfl
  | lam body child => rfl
  | app function argument first last => rfl
  | branch condition yes no conditionIH yesIH noIH => rfl
  | letE value body first last =>
      simp only [eval, synth, toOption_bind, first, Option.bind_eq_bind,
        Option.bind_map, Option.map_bind, Function.comp_def]
      apply Option.bind_congr
      intro shape _
      exact last (shape :: environment)
  | pair left right first last =>
      simp only [eval, synth, toOption_bind, toOption_pure, first, last,
        Option.bind_eq_bind, Option.bind_map, Option.map_bind, Function.comp_def]
      rfl
  | fst expression child =>
      simp only [eval, synth, toOption_bind, child, Option.bind_eq_bind,
        Option.bind_map, Option.map_bind, Function.comp_def]
      apply Option.bind_congr
      intro shape _
      cases shape <;> rfl
  | snd expression child =>
      simp only [eval, synth, toOption_bind, child, Option.bind_eq_bind,
        Option.bind_map, Option.map_bind, Function.comp_def]
      apply Option.bind_congr
      intro shape _
      cases shape <;> rfl
  | record label head tail first last =>
      simp only [eval, synth, toOption_bind, first, last, Option.bind_eq_bind,
        Option.bind_map, Option.map_bind, Function.comp_def]
      apply Option.bind_congr
      intro headShape _
      apply Option.bind_congr
      intro tailShape _
      cases tailShape <;> simp [Shape.value, Except.toOption] <;> rfl
  | recordDefault label source fallback first last =>
      simp only [eval, synth, toOption_bind, first, last, Option.bind_eq_bind,
        Option.bind_map, Option.map_bind, Function.comp_def]
      apply Option.bind_congr
      intro sourceShape _
      apply Option.bind_congr
      intro fallbackShape _
      cases sourceShape <;> simp [Shape.value, Except.toOption] <;> rfl
  | field label expression child =>
      simp only [eval, synth, toOption_bind, child, Option.bind_eq_bind,
        Option.bind_map, Option.map_bind, Function.comp_def]
      apply Option.bind_congr
      intro shape _
      cases shape with
      | base | pair | variant => rfl
      | record fields =>
          simp only [Shape.value, ShapeFields.lookup_values]
          cases fields.lookup label <;> rfl
  | variant label expression child =>
      simp only [eval, synth, toOption_bind, toOption_pure, child,
        Option.bind_eq_bind, Option.bind_map, Option.map_bind, Function.comp_def]
      rfl

private theorem toOption_some (result : Except ε α) (value : α) :
    result.toOption = some value ↔ result = .ok value := by
  cases result <;> simp [Except.toOption]

private theorem toOption_none (result : Except ε α) :
    result.toOption = none ↔ ∃ error, result = .error error := by
  cases result <;> simp [Except.toOption]

/-- Exact success agreement for arbitrary source syntax and exact input
descriptors. Neither implication assumes typing or successful inference. -/
theorem eval_success_iff_synth (environment : List Shape) (expression : Expr)
    (value : Value) :
    eval (environment.map Shape.value) expression = .ok value ↔
      ∃ shape, synth environment expression = some shape ∧ shape.value = value := by
  rw [← toOption_some, eval_toOption, Option.map_eq_some_iff]

/-- Failed synthesis includes every runtime failure in this evaluator;
the distinct error codes are intentionally not identified. -/
theorem synth_none_iff_eval_error (environment : List Shape) (expression : Expr) :
    synth environment expression = none ↔
      ∃ error, eval (environment.map Shape.value) expression = .error error := by
  rw [← toOption_none, eval_toOption, Option.map_eq_none_iff]

/-- On closed source expressions, the public inference result and the
actual successful runtime result determine the same descriptor value. -/
theorem eval_success_iff_infer (expression : Expr) (value : Value) :
    eval [] expression = .ok value ↔
      ∃ shape, infer expression = .solved shape ∧ shape.value = value := by
  simpa only [List.map_nil, PresenceDataInference.infer_solved_iff] using
    eval_success_iff_synth [] expression value

/-- For supported data syntax, rejection is equivalent to an actual
runtime error. Unsupported source syntax retains its separate inference result. -/
theorem infer_rejected_iff_eval_error (expression : Expr)
    (data : PresenceDataInference.Data expression) :
    infer expression = .rejected ↔ ∃ error, eval [] expression = .error error := by
  calc
    infer expression = .rejected ↔ synth [] expression = none := by
      unfold infer
      rw [show PresenceDataInference.supported expression = true from data]
      cases synth [] expression <;> simp
    _ ↔ ∃ error, eval [] expression = .error error := by
      simpa only [List.map_nil] using synth_none_iff_eval_error [] expression

/-- An exact descriptor environment is enough for a semantic completeness
statement for the independent presence-data judgment, at every target predicate.
This says nothing about completeness of legacy structural subtyping. -/
theorem exact_typing_iff_evaluates (environment : List Shape) (expression : Expr)
    (target : PresenceDataTypes.Ty) :
    PresenceDataInference.Typing (PresenceDataInference.exactContext environment)
      expression target ↔
      ∃ value, eval (environment.map Shape.value) expression = .ok value ∧ target value := by
  rw [PresenceDataInference.synth_instances_exact]
  constructor
  · rintro ⟨shape, found, below⟩
    exact ⟨shape.value, (eval_success_iff_synth environment expression shape.value).mpr
      ⟨shape, found, rfl⟩, (shape.denote_le_iff target).mp below⟩
  · rintro ⟨value, evaluated, valid⟩
    obtain ⟨shape, found, same⟩ :=
      (eval_success_iff_synth environment expression value).mp evaluated
    exact ⟨shape, found, (shape.denote_le_iff target).mpr (same ▸ valid)⟩

/-! ## Compatibility with the earlier Shadow data models -/

universe u
variable {Row : Type u}

/-- Every earlier raw Shadow typing of a closed supported data expression
is accepted by the new inference. Its exact principal value satisfies the
earlier target's data meaning, including all earlier subsumption steps. -/
theorem shadow_typing_infers (algebra : RowFlowSchemes.Algebra Row)
    (expression : Expr) (supported : SourceDataRuntime.Supported expression)
    (target : Inference.Comp (ShadowRecordValueInference.model algebra))
    (typed : Inference.Typing (ShadowRecordValueInference.model algebra) [] expression target) :
    ∃ shape, infer expression = .solved shape ∧
      DataTypeSemantics.Holds target.1 DataTypeSemantics.visible shape.value := by
  obtain ⟨value, evaluated, valid⟩ :=
    ShadowDataSafety.typing_evaluates algebra expression supported target typed
  obtain ⟨shape, inferred, same⟩ := (eval_success_iff_infer expression value).mp evaluated
  exact ⟨shape, inferred, same ▸ valid⟩

/-- The same compatibility is independent of the representative of a
Shadow semantic quotient type. -/
theorem shadow_quotient_typing_infers (algebra : RowFlowSchemes.Algebra Row)
    (expression : Expr) (supported : SourceDataRuntime.Supported expression)
    (target : Inference.Comp (ShadowRecordValueQuotient.model algebra))
    (typed : Inference.Typing (ShadowRecordValueQuotient.model algebra) [] expression target) :
    ∃ shape, infer expression = .solved shape ∧
      ShadowDataSafety.QuotientHolds target.1 DataTypeSemantics.visible shape.value := by
  obtain ⟨value, evaluated, valid⟩ :=
    ShadowDataSafety.quotient_typing_evaluates algebra expression supported target typed
  obtain ⟨shape, inferred, same⟩ := (eval_success_iff_infer expression value).mp evaluated
  exact ⟨shape, inferred, same ▸ valid⟩

/-- A solved original principal constraint formula also supplies new
inference success; no precomputed descriptor is supplied by the caller. -/
theorem shadow_principal_infers (algebra : RowFlowSchemes.Algebra Row)
    (expression : Expr) (supported : SourceDataRuntime.Supported expression)
    (target : Inference.Comp (ShadowRecordValueQuotient.model algebra))
    (solved : (Inference.principal ([] : Inference.SchemeEnv Empty) expression).Holds
      (ShadowRecordValueQuotient.model algebra) (Inference.extend Empty.elim target)) :
    ∃ shape, infer expression = .solved shape ∧
      ShadowDataSafety.QuotientHolds target.1 DataTypeSemantics.visible shape.value := by
  obtain ⟨value, evaluated, valid⟩ :=
    ShadowDataSafety.principal_evaluates algebra expression supported target solved
  obtain ⟨shape, inferred, same⟩ := (eval_success_iff_infer expression value).mp evaluated
  exact ⟨shape, inferred, same ▸ valid⟩

/-- The older executable record-value inference's entire family of
parameter instances validates one and the same new exact principal value. -/
theorem shadow_plan_infers (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (plan : RigidRecordValueInference.Plan)
    (inferred : RigidRecordValueInference.infer expression = .inferred plan) :
    ∃ shape, infer expression = .solved shape ∧
      ∀ parameter : plan.Parameters (ShadowRecordValueQuotient.model algebra).Ty,
        ShadowDataSafety.QuotientHolds
          (plan.evalWith (ShadowRecordValueQuotient.model algebra) parameter)
          DataTypeSemantics.visible shape.value := by
  obtain ⟨value, evaluated, valid⟩ := ShadowDataSafety.inferred_evaluates algebra expression plan inferred
  obtain ⟨shape, found, same⟩ := (eval_success_iff_infer expression value).mp evaluated
  exact ⟨shape, found, same ▸ valid⟩

end Yulang.PresenceDataCompatibility
