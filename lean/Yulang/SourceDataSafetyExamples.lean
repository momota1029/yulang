import Yulang.ShadowDataSafety

/-! Original-source computations exercising inference, stored shadow erasure,
field selection, both let typings, and genuine runtime shape failures. -/

namespace Yulang.SourceDataSafetyExamples

open Inference
open StructuralBase (Ty)
open SourceDataRuntime
open RigidRecordValueInference (Plan infer)

universe u
variable {Row : Type u}

def repeated : Expr :=
  .record 0 (.lit .int) (.record 0 (.lit .str) (.record 1 (.lit .bool) .emptyRecord))

def repeatedPlan : Plan :=
  .record 0 (.lit .int) (.record 0 (.lit .str) (.record 1 (.lit .bool) .emptyRecord))

def selected : Expr := .letE repeated (.field 0 (.var 0))

def result : Value := .record [(0, .base .int), (1, .base .bool)]

theorem repeated_inferred : infer repeated = .inferred repeatedPlan := rfl
theorem repeated_evaluates : eval [] repeated = .ok result := rfl
theorem selected_evaluates : eval [] selected = .ok (.base .int) := rfl
theorem other_field_evaluates : eval [] (.field 1 repeated) = .ok (.base .bool) := rfl

/-- The hidden string is absent from the actual stored result. -/
theorem stored_payload_erased :
    eval [] repeated = .ok (.record [(0, .base .int), (1, .base .bool)]) := rfl

/-- The actual calculated scheme describes this same concrete runtime value
for every freely chosen semantic quotient parameter. -/
theorem all_inferred_parameters_describe_result (algebra : RowFlowSchemes.Algebra Row)
    (parameter : repeatedPlan.Parameters (ShadowRecordValueQuotient.model algebra).Ty) :
    ShadowDataSafety.QuotientHolds
      (repeatedPlan.evalWith (ShadowRecordValueQuotient.model algebra) parameter)
      DataTypeSemantics.visible result := by
  obtain ⟨value, evaluated, valid⟩ :=
    ShadowDataSafety.inferred_evaluates algebra repeated repeatedPlan repeated_inferred
  have same : value = result := Except.ok.inj (evaluated.symm.trans repeated_evaluates)
  simpa [same] using valid parameter

private theorem join_empty (algebra : RowFlowSchemes.Algebra Row) :
    algebra.le (algebra.join algebra.empty algebra.empty) algebra.empty :=
  (algebra.join_le_iff _ _ _).mpr ⟨algebra.refl _, algebra.refl _⟩

abbrev model (algebra : RowFlowSchemes.Algebra Row) := ShadowRecordValueInference.model algebra

def repeatedType : Ty Row :=
  .record 0 (.base .int) (.record 0 (.base .str) (.record 1 (.base .bool) .emptyRecord))

theorem repeated_typed (algebra : RowFlowSchemes.Algebra Row) :
    Typing (model algebra) [] repeated (repeatedType, algebra.empty) := by
  refine Typing.record (m := model algebra)
    (a := (.base .int, algebra.empty))
    (b := (.record 0 (.base .str) (.record 1 (.base .bool) .emptyRecord), algebra.empty))
    (.lit ⟨.refl _, algebra.refl _⟩) ?_ ?_ ⟨.refl _, join_empty algebra⟩
  · refine Typing.record (m := model algebra)
      (a := (.base .str, algebra.empty)) (b := (.record 1 (.base .bool) .emptyRecord, algebra.empty))
      (.lit ⟨.refl _, algebra.refl _⟩) ?_ ?_ ⟨.refl _, join_empty algebra⟩
    · exact .record (.lit ⟨.refl _, algebra.refl _⟩)
        (.emptyRecord ⟨.refl _, algebra.refl _⟩) (.refl _) ⟨.refl _, join_empty algebra⟩
    · exact ShadowSemanticRecords.record_width 1 _ (.refl _)
  · exact ShadowSemanticRecords.record_width 0 _
      (ShadowSemanticRecords.record_width 1 _ (.refl _))

private theorem selected_head (algebra : RowFlowSchemes.Algebra Row) :
    ShadowSemanticRecords.Subtype algebra.le repeatedType (.record 0 (.base .int) .emptyRecord) :=
  ShadowSemanticRecords.record_head 0 _
    (ShadowSemanticRecords.record_width 0 _ (ShadowSemanticRecords.record_width 1 _ (.refl _)))

/-- The computed-let route evaluates the RHS and stores a monomorphic value. -/
theorem selected_computed_typed (algebra : RowFlowSchemes.Algebra Row) :
    Typing (model algebra) [] selected (.base .int, algebra.empty) := by
  refine Typing.letComputed (m := model algebra) (b := (.base .int, algebra.empty))
    (repeated_typed algebra) ?_ ⟨.refl _, join_empty algebra⟩
  exact .field (.var rfl (.mono ⟨selected_head algebra, algebra.refl _⟩))
    ⟨.refl _, algebra.refl _⟩

/-- The value-restricted polymorphic route describes the identical execution. -/
theorem selected_polymorphic_typed (algebra : RowFlowSchemes.Algebra Row) :
    Typing (model algebra) [] selected (.base .int, algebra.empty) := by
  refine .letValue (by rfl) (repeated_typed algebra) ?_
  apply Typing.field (er := algebra.empty)
  · apply Typing.var (b := .poly repeated []) rfl
    apply BindingTyping.poly
    · exact ConstraintProblems.typing_subsumption (model algebra)
        ShadowSemanticRecords.Subtype.trans algebra.refl
        (fun first last => algebra.trans first last) (repeated_typed algebra)
        ⟨selected_head algebra, algebra.refl _⟩
    · exact algebra.refl _
  · exact ⟨.refl _, algebra.refl _⟩

/-- Runtime interpretation rules out pretending the selected integer is a string. -/
theorem selected_not_string (algebra : RowFlowSchemes.Algebra Row) (row : Row) :
    ¬ Typing (model algebra) [] selected (.base .str, row) := by
  intro typed
  obtain ⟨value, evaluated, valid⟩ :=
    ShadowDataSafety.typing_evaluates algebra selected (by trivial) (.base .str, row) typed
  have same : value = .base .int := Except.ok.inj (evaluated.symm.trans selected_evaluates)
  rw [same] at valid
  cases valid

theorem scalar_tail_errors :
    eval [] (.record 0 (.lit .int) (.lit .str)) = .error .expectedRecord := rfl
theorem missing_field_errors :
    eval [] (.field 7 repeated) = .error (.missingField 7) := rfl
theorem scalar_projection_errors :
    eval [] (.fst (.lit .int)) = .error .expectedPair := rfl
theorem strict_unused_rhs_errors :
    eval [] (.letE (.field 7 repeated) (.lit .unit)) = .error (.missingField 7) := rfl
theorem function_is_unsupported :
    eval [] (.lam (.var 0)) = .error .unsupported := rfl

end Yulang.SourceDataSafetyExamples
