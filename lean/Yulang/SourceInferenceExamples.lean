import Yulang.SourcePrincipalInference

/-!
# Complete source instance families for identity and a constant function

The canonical families below are proved directly from the original `Typing`
constructors in the common regular-type model. Identity retains the same value
and row parameter at its input and output. A constant integer function has `any`
as its input value type, while its unconstrained input-computation row remains a
free parameter. Both function values can be assigned any outer computation row.

The source inference checks and instance theorems then connect the actual
computed results to these independently proved families. No graph, constraint
list, row assignment, or guessed value solution is supplied to inference.
-/

namespace Yulang.SourceInferenceExamples

open Inference

universe u

variable {Row : Type u}

abbrev model (algebra : RowFlowSchemes.Algebra Row) := SourcePrincipalInference.model algebra
abbrev Value (Row : Type u) := RegularInferenceModel.Ty Row

def identity : Expr := .lam (.var 0)
def constantInt : Expr := .lam (.lit .int)

def identityType (value : Value Row) (row : Row) : Value Row :=
  .arrow (.node value) row (.node value) row

def constantIntType (algebra : RowFlowSchemes.Algebra Row) (inputRow : Row) : Value Row :=
  .arrow (.node .top) inputRow (.node (.base .int)) algebra.empty

/-- This describes every original typing, including arbitrary regular value
types and arbitrary input rows. The result row of the function value is free. -/
theorem identity_typing_iff (algebra : RowFlowSchemes.Algebra Row)
    (target : Comp (model algebra)) :
    Typing (model algebra) [] identity target ↔
      ∃ value : Value Row, ∃ row : Row,
        RegularInferenceModel.Subtype algebra.le (identityType value row) target.1 := by
  constructor
  · intro typed
    obtain ⟨input, output, body, outer⟩ :=
      (Typing.lam_iff (model algebra) [] (.var 0) target).mp typed
    have below : Comp.le (model algebra) input output := by
      simpa [Typing.var_iff, BindingLookup] using body
    refine ⟨input.1, input.2, RegularInferenceModel.subtype_trans ?_ outer.1⟩
    exact RegularInferenceModel.arrow_subtype
      (RegularInferenceModel.subtype_refl algebra.le input.1) (algebra.refl input.2)
      below.1 below.2
  · rintro ⟨value, row, below⟩
    apply Typing.lam (m := model algebra) (a := (value, row)) (b := (value, row))
    · exact .var rfl (.mono
        ⟨RegularInferenceModel.subtype_refl algebra.le value, algebra.refl row⟩)
    · exact ⟨below, algebra.empty_le target.2⟩

/-- The input value parameter occurs only negatively and is exactly eliminated
by `any`. The input row is retained, since no purity constraint is imposed on it. -/
theorem constant_int_typing_iff (algebra : RowFlowSchemes.Algebra Row)
    (target : Comp (model algebra)) :
    Typing (model algebra) [] constantInt target ↔
      ∃ inputRow : Row,
        RegularInferenceModel.Subtype algebra.le (constantIntType algebra inputRow) target.1 := by
  constructor
  · intro typed
    obtain ⟨input, output, body, outer⟩ :=
      (Typing.lam_iff (model algebra) [] (.lit .int) target).mp typed
    have below : Comp.le (model algebra)
        (Comp.pure (model algebra) ((model algebra).base .int)) output :=
      (Typing.lit_iff (model algebra) [.mono input] .int output).mp body
    refine ⟨input.2, RegularInferenceModel.subtype_trans ?_ outer.1⟩
    exact RegularInferenceModel.arrow_subtype
      (RegularInferenceModel.subtype_top algebra.le input.1) (algebra.refl input.2)
      below.1 below.2
  · rintro ⟨inputRow, below⟩
    apply Typing.lam (m := model algebra)
      (a := ((model algebra).top, inputRow))
      (b := ((model algebra).base .int, algebra.empty))
    · exact .lit ⟨RegularInferenceModel.subtype_refl algebra.le _, algebra.refl _⟩
    · exact ⟨below, algebra.empty_le target.2⟩

theorem identity_at_arbitrary_parameters (algebra : RowFlowSchemes.Algebra Row)
    (value : Value Row) (inputRow outerRow : Row) :
    Typing (model algebra) [] identity (identityType value inputRow, outerRow) :=
  (identity_typing_iff algebra _).mpr
    ⟨value, inputRow, RegularInferenceModel.subtype_refl algebra.le _⟩

theorem constant_int_at_arbitrary_input_row (algebra : RowFlowSchemes.Algebra Row)
    (inputRow outerRow : Row) :
    Typing (model algebra) [] constantInt (constantIntType algebra inputRow, outerRow) :=
  (constant_int_typing_iff algebra _).mpr
    ⟨inputRow, RegularInferenceModel.subtype_refl algebra.le _⟩

/-! ## Executed source inference and complete instance descriptions -/

theorem identity_inferred :
    (SourcePrincipalInference.infer identity).status = .inferred := by decide +kernel

theorem constant_int_inferred :
    (SourcePrincipalInference.infer constantInt).status = .inferred := by decide +kernel

private theorem supported_of_inferred (expression : Expr)
    (success : (SourcePrincipalInference.infer expression).status = .inferred) :
    SourcePrincipalInference.supported expression = true := by
  cases checked : SourcePrincipalInference.supported expression with
  | false =>
      have failed := (SourcePrincipalInference.infer_unsupported_iff expression).mpr checked
      rw [success] at failed
      cases failed
  | true => rfl

theorem identity_supported : SourcePrincipalInference.supported identity = true :=
  supported_of_inferred identity identity_inferred

theorem constant_int_supported : SourcePrincipalInference.supported constantInt = true :=
  supported_of_inferred constantInt constant_int_inferred

/-- The actual computed regular scheme preserves identity's shared value and
row parameters. Antisymmetry is required only by the joint source-solver bridge,
not by the independent typing characterization above. -/
theorem infer_identity_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (target : Comp (model algebra)) :
    (SourcePrincipalInference.infer identity).Instance algebra target ↔
      ∃ value : Value Row, ∃ row : Row,
        RegularInferenceModel.Subtype algebra.le (identityType value row) target.1 :=
  (SourcePrincipalInference.infer_instances_exact algebra rowAntisymm identity identity_supported target).trans
    (identity_typing_iff algebra target)

/-- The computed scheme has exactly the same instances as `any ! row → int ! ∅`
with a free input row. It does not default that row to empty. -/
theorem infer_constant_int_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (target : Comp (model algebra)) :
    (SourcePrincipalInference.infer constantInt).Instance algebra target ↔
      ∃ inputRow : Row,
        RegularInferenceModel.Subtype algebra.le (constantIntType algebra inputRow) target.1 :=
  (SourcePrincipalInference.infer_instances_exact algebra rowAntisymm constantInt
    constant_int_supported target).trans (constant_int_typing_iff algebra target)

end Yulang.SourceInferenceExamples
