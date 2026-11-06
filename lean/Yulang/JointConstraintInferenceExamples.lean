import Yulang.JointConstraintInference

/-!
# Executed joint value and row inference

The same finite symbolic computation supports every row interpretation.
Boolean observations here check that live row parameters remain free, that
shared arrow rows stay shared, and that negative arrow positions propagate
their row obligations in the correct direction.
-/

namespace Yulang.JointConstraintInferenceExamples

open Inference JointConstraintInference

abbrev rows := RowFlowSchemes.Examples.boolAlgebra

theorem row_antisymm {left right : Bool} : rows.le left right → rows.le right left → left = right := by
  cases left <;> cases right <;> simp [rows, RowFlowSchemes.Examples.boolAlgebra]

def observedRows (result : Result n) (parameter : Fin n → Bool) : Option (List Bool) :=
  match result with
  | .inferred scheme => some ((List.finRange n).map (scheme.rows rows parameter))
  | _ => none

def sharedArrowRows : ConstraintProblems.Problem 2 :=
  ⟨[(.arrow (.base .int) (.var 0) (.base .int) (.var 0), .var 1)], []⟩

theorem shared_arrow_rows_infer : (infer sharedArrowRows).status = .inferred := by decide +kernel

theorem live_row_parameter_is_not_defaulted :
    observedRows (infer sharedArrowRows) (fun index => index == 0) = some [true, false] := by decide +kernel

theorem shared_arrow_annotations_stay_nonempty :
    (match infer sharedArrowRows with
      | .inferred scheme => some ((List.finRange scheme.size).any fun node =>
          match NestedRowRequirements.instantiateGraph rows
              (scheme.rows rows (fun index => index == 0)) scheme.graph node with
          | .arrow _ inputRow _ outputRow => inputRow && outputRow
          | _ => false)
      | _ => none) = some true := by decide +kernel

def contravariantRows : ConstraintProblems.Problem 2 :=
  ⟨[(.arrow (.base .int) (.var 0) (.base .int) .empty,
      .arrow (.base .int) (.var 1) (.base .int) .empty)],
    [(.var 0, .empty)]⟩

theorem negative_arrow_row_obligation_is_propagated :
    observedRows (infer contravariantRows) (fun _ => true) = some [false, false] := by decide +kernel

def pureCycle : ConstraintProblems.Problem 3 :=
  ⟨[], [(.var 0, .var 1), (.var 1, .var 0), (.var 1, .empty)]⟩

theorem unrelated_row_remains_free :
    observedRows (infer pureCycle) (fun _ => true) = some [false, false, true] := by decide +kernel

def selfApplication : ConstraintProblems.Problem 3 :=
  ⟨[(.var 0, .arrow (.var 0) (.var 1) (.var 2) (.var 1))], [(.var 0, .empty)]⟩

theorem self_application_infers_jointly : (infer selfApplication).status = .inferred := by decide +kernel

theorem self_application_rows_are_live :
    observedRows (infer selfApplication) (fun _ => true) = some [false, true, true] := by decide +kernel

theorem self_application_all_instances (output : Fin 3) (expected : Comp (model rows)) :
    selfApplication.Instance (model rows) output expected ↔
      (infer selfApplication).Instance rows output expected :=
  infer_instances_exact rows row_antisymm selfApplication (by decide +kernel) output expected

theorem self_application_every_parameter_solves (scheme : Scheme 3)
    (returned : infer selfApplication = .inferred scheme) (rowParameter : Fin 3 → Bool)
    (valueParameter : Fin scheme.size → Value Bool) :
    selfApplication.Holds (model rows) (scheme.values rows rowParameter valueParameter)
      (scheme.rows rows rowParameter) :=
  infer_inferred_sound rows row_antisymm selfApplication scheme returned rowParameter valueParameter

def recursiveArrowEquation : ConstraintProblems.Problem 2 :=
  ⟨[(.var 0, .arrow (.var 0) (.var 1) (.var 1) (.var 1)),
    (.arrow (.var 0) (.var 1) (.var 1) (.var 1), .var 0)], []⟩

theorem recursive_arrow_equation_infers_jointly :
    (infer recursiveArrowEquation).status = .inferred := by decide +kernel

theorem recursive_arrow_equation_has_a_joint_model :
    ∃ values rowValues, recursiveArrowEquation.Holds (model rows) values rowValues :=
  ((infer_inferred_iff rows row_antisymm recursiveArrowEquation).mp recursive_arrow_equation_infers_jointly).2

/-- The value contradiction is independent of the unsupported row form, so
the entry can soundly reject before inspecting that row form. -/
def shapeConflict : ConstraintProblems.Problem 1 :=
  ⟨[(.base .int, .base .str)], [(.var 0, .join (.var 0) .empty)]⟩

theorem shape_conflict_rejected : (infer shapeConflict).status = .rejected := by decide +kernel

theorem shape_conflict_has_no_joint_model :
    ¬ ∃ values rowValues, shapeConflict.Holds (model rows) values rowValues :=
  ((infer_rejected_iff rows row_antisymm shapeConflict).mp shape_conflict_rejected).2

def rightJoin : ConstraintProblems.Problem 1 := ⟨[], [(.var 0, .join (.var 0) .empty)]⟩

theorem unhandled_row_join_is_unsupported : (infer rightJoin).status = .unsupported := by decide +kernel

theorem unsupported_row_join_has_a_model :
    rightJoin.Holds (model rows) (fun _ => .bottom) (fun _ => false) := by
  refine ⟨TypeConstraintGraph.holds_nil _ _ _, ?_⟩
  exact (rowHolds_iff rows (fun _ => false) rightJoin.rows).mpr
    (RowFlowSchemes.empty_assignment_models rows rightJoin.rows)

end Yulang.JointConstraintInferenceExamples
