import Yulang.RigidRecordValueInference

/-!
# Actual data inference and a widened non-rigid tail instance

The nested example keeps an internal tail strictly wider than its finite
record literal. Its free-parameter instance is established explicitly, by
congruence and lattice retraction, without arbitrary-tail covariance.
-/

namespace Yulang.RigidRecordValueInferenceExamples

open Inference RigidRecordValueInference
open StructuralBase (Ty)
open RigidSemanticRecords (Subtype Equivalent)

universe u

variable {Row : Type u}

def singleton : Expr := .record 0 (.lit .int) .emptyRecord
def nested : Expr := .record 0 (.lit .int) (.record 1 (.lit .int) .emptyRecord)
def repeated : Expr := .record 0 (.lit .int) (.record 0 (.lit .str) .emptyRecord)

def innerPlan : Plan := .record 1 (.lit .int) .emptyRecord
def nestedPlan : Plan := .record 0 (.lit .int) innerPlan

theorem nested_inferred : infer nested = .inferred nestedPlan := by decide +kernel
theorem nested_has_four_parameters : nestedPlan.parameterCount = 4 := by decide +kernel

def yType : Ty Row := .record 1 (.base .int) .emptyRecord
def zType : Ty Row := .record 2 (.base .str) .emptyRecord
def widerTail : Ty Row := .union yType zType
def widerResult : Ty Row := .record 0 (.base .int) widerTail

theorem wider_tail_not_spine : ¬ StructuralBase.IsRecord (widerTail : Ty Row) := by
  intro impossible
  cases impossible

theorem wider_tail_below_empty (leRow : Row → Row → Prop) :
    Subtype leRow widerTail .emptyRecord :=
  .unionElim (RigidSemanticRecords.record_width 1 _ (.refl _))
    (RigidSemanticRecords.record_width 2 _ (.refl _))

def innerParameters : innerPlan.Parameters (Ty Row) :=
  ⟨PUnit.unit, PUnit.unit, .base .int, .emptyRecord⟩

def nestedParameters : nestedPlan.Parameters (Ty Row) :=
  ⟨PUnit.unit, innerParameters, .base .int, widerTail⟩

theorem inner_parameters_retract (leRow : Row → Row → Prop) :
    Equivalent leRow (innerPlan.evaluate innerParameters) yType :=
  RigidSemanticRecords.record_congr 1 (widen_retract (.refl _))
    (clamp_retract (.refl _) (.refl _))

/-- This is a concrete unconstrained parameter tuple for the actual returned
plan. Its result has the widened union tail, not a forced proper spine. -/
theorem nested_parameters_retract (leRow : Row → Row → Prop) :
    Equivalent leRow (nestedPlan.evaluate nestedParameters) widerResult :=
  RigidSemanticRecords.record_congr 0 (widen_retract (.refl _))
    (clamp_retract (.trans (inner_parameters_retract leRow).1 (.unionLeft _ _))
      (wider_tail_below_empty leRow))

theorem nested_widened_instance (algebra : RowFlowSchemes.Algebra Row) :
    (infer nested).Instance algebra (widerResult, algebra.empty) := by
  rw [nested_inferred]
  exact ⟨nestedParameters, (nested_parameters_retract algebra.le).1, algebra.refl _⟩

theorem nested_widened_typing (algebra : RowFlowSchemes.Algebra Row) :
    Typing (model algebra) [] nested (widerResult, algebra.empty) :=
  (infer_instances_exact algebra nested ⟨trivial, trivial, trivial⟩ _).mp
    (nested_widened_instance algebra)

theorem scalar_tail_rejected : infer (.record 0 (.lit .int) (.lit .str)) = .rejected :=
  by decide +kernel

theorem scalar_tail_has_no_typing (algebra : RowFlowSchemes.Algebra Row) :
    ¬ ∃ target, Typing (model algebra) [] (.record 0 (.lit .int) (.lit .str)) target :=
  (infer_rejected_iff algebra (.record 0 (.lit .int) (.lit .str)) ⟨trivial, trivial⟩).mp scalar_tail_rejected

def cases : List (String × Expr × Status) :=
  [ ("literal", .lit .int, .inferred),
    ("empty record", .emptyRecord, .inferred),
    ("record literal", singleton, .inferred),
    ("nested record", nested, .inferred),
    ("first field wins", repeated, .inferred),
    ("records inside pair and variant", .pair singleton (.variant 3 nested), .inferred),
    ("scalar record tail", .record 0 (.lit .int) (.lit .str), .rejected),
    ("pair record tail", .record 0 (.lit .int) (.pair .emptyRecord .emptyRecord), .rejected),
    ("variant record tail", .record 0 (.lit .int) (.variant 1 .emptyRecord), .rejected),
    ("rejected nested tail", .record 0 (.lit .int) (.record 1 (.lit .int) (.lit .str)), .rejected),
    ("function outside data entry", .lam (.var 0), .unsupported),
    ("variable outside data entry", .var 0, .unsupported) ]

theorem computed_cases : cases.all (fun (_, expression, expected) =>
    decide ((infer expression).status = expected)) = true := by decide +kernel

end Yulang.RigidRecordValueInferenceExamples
