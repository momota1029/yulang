import Yulang.RigidRecordValueInference
import Yulang.RigidRecordQuotientInference
import Yulang.RigidRecordSourceBoundary

/-!
# Actual data inference with unrestricted semantic type parameters

The source algorithm and its finite plan are unchanged. Parameters range over
the decision-39 quotient itself, not over assignments constrained by a graph.
Surjectivity of the quotient map on each finite parameter product and exact
constructor transport preserve every source instance and every rejection.

The supported grammar remains `RigidRecordValueInference.Data`; this is not
the all-core regular-type inference theorem.
-/

namespace Yulang.RigidRecordValueQuotient

open Inference
open RigidRecordValueInference (Plan Result Data infer)

universe u

variable {Row : Type u}

abbrev model (algebra : RowFlowSchemes.Algebra Row) : Model :=
  RigidRecordQuotientInference.model algebra

/-- A constructor map reflecting both orders and covering all value types
preserves the exact free-parameter instance family of every finite plan. -/
theorem plan_instances_transport (map : ModelMap source target)
    (valueReflect : ∀ {a b}, target.subTy (map.value a) (map.value b) → source.subTy a b)
    (rowReflect : ∀ {a b}, target.subRow (map.row a) (map.row b) → source.subRow a b)
    (onto : ∀ value : target.Ty, ∃ original : source.Ty, map.value original = value)
    (plan : Plan) (result : Comp source) :
    plan.InstanceWith target (map.comp result) ↔ plan.InstanceWith source result := by
  constructor
  · rintro ⟨parameter, below⟩
    obtain ⟨original, rfl⟩ := plan.mapParameters_surjective map.value onto parameter
    refine ⟨original, valueReflect ?_, rowReflect ?_⟩
    · rw [plan.evalWith_map map]
      exact below.1
    · rw [map.empty]
      exact below.2
  · rintro ⟨parameter, below⟩
    refine ⟨plan.mapParameters map.value parameter, ?_, ?_⟩
    · rw [← plan.evalWith_map map]
      exact map.subtype below.1
    · rw [← map.empty]
      exact map.subrow below.2

theorem value_surjective (leRow : Row → Row → Prop)
    (value : RigidRecordQuotient.QTy leRow) :
    ∃ original : StructuralBase.Ty Row, RigidRecordQuotient.mk original = value := by
  refine Quotient.inductionOn value ?_
  exact fun original => ⟨original, rfl⟩

theorem plan_instances_exact (algebra : RowFlowSchemes.Algebra Row) (plan : Plan)
    (result : Comp (RigidRecordValueInference.model algebra)) :
    plan.InstanceWith (model algebra) (RigidRecordQuotient.mk result.1, result.2) ↔
      plan.Instance algebra result :=
  (plan_instances_transport
    (RigidRecordQuotientInference.quotientMap algebra.empty algebra.join algebra.le algebra.refl)
    (fun proof => proof) (fun proof => proof) (value_surjective algebra.le) plan result).trans
      (plan.instanceWith_model algebra result)

theorem result_instances_exact (algebra : RowFlowSchemes.Algebra Row) (result : Result)
    (target : Comp (RigidRecordValueInference.model algebra)) :
    result.InstanceWith (model algebra) (RigidRecordQuotient.mk target.1, target.2) ↔
      result.Instance algebra target := by
  cases result with
  | inferred plan => exact plan_instances_exact algebra plan target
  | _ => rfl

/-- Every quotient target and every unrestricted quotient parameter tuple
is covered. The premise is only the syntactic data grammar and row algebra. -/
theorem infer_instances_exact (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (data : Data expression) (target : Comp (model algebra)) :
    (infer expression).InstanceWith (model algebra) target ↔
      Typing (model algebra) [] expression target := by
  rcases target with ⟨value, row⟩
  refine Quotient.inductionOn value ?_
  intro representative
  exact (result_instances_exact algebra (infer expression) (representative, row)).trans
    ((RigidRecordValueInference.infer_instances_exact algebra expression data (representative, row)).trans
      (RigidRecordQuotientInference.closed_typing_exact algebra.empty algebra.join
        algebra.le algebra.refl expression (representative, row)).symm)

theorem infer_principal_formula_exact (algebra : RowFlowSchemes.Algebra Row)
    (expression : Expr) (data : Data expression) (target : Comp (model algebra)) :
    (infer expression).InstanceWith (model algebra) target ↔
      (principal ([] : SchemeEnv Empty) expression).Holds (model algebra) (extend Empty.elim target) :=
  (infer_instances_exact algebra expression data target).trans
    (principal_exact (model algebra) expression [] [] Empty.elim
      (EnvRel.nil (model algebra) Empty.elim) target).symm

/-- The caller supplies only the actually returned plan and an arbitrary
finite tuple of quotient types. No graph model or parameter side condition
is needed to obtain a typing of the original expression. -/
theorem infer_plan_sound (algebra : RowFlowSchemes.Algebra Row)
    (expression : Expr) (plan : Plan) (returned : infer expression = .inferred plan)
    (parameter : plan.Parameters (model algebra).Ty) :
    Typing (model algebra) [] expression
      (plan.evalWith (model algebra) parameter, algebra.empty) := by
  have data : Data expression := by
    rw [← (RigidRecordValueInference.infer_plan_correct expression plan returned).2]
    exact plan.expression_data
  apply (infer_instances_exact algebra expression data _).mp
  rw [returned]
  exact ⟨parameter, RigidRecordQuotient.le_refl _, algebra.refl _⟩

theorem typing_exists_exact (algebra : RowFlowSchemes.Algebra Row) (expression : Expr) :
    (∃ target, Typing (model algebra) [] expression target) ↔
      ∃ original, Typing (RigidRecordValueInference.model algebra) [] expression original := by
  constructor
  · rintro ⟨target, typed⟩
    obtain ⟨original, same⟩ := RigidRecordQuotientInference.computation_surjective
      algebra.empty algebra.join algebra.le algebra.refl target
    refine ⟨original, ?_⟩
    apply (RigidRecordQuotientInference.closed_typing_exact algebra.empty algebra.join
      algebra.le algebra.refl expression original).mp
    rw [← same] at typed
    exact typed
  · rintro ⟨original, typed⟩
    exact ⟨(RigidRecordQuotient.mk original.1, original.2),
      (RigidRecordQuotientInference.closed_typing_exact algebra.empty algebra.join
        algebra.le algebra.refl expression original).mpr typed⟩

theorem infer_rejected_iff (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (data : Data expression) :
    infer expression = .rejected ↔ ¬ ∃ target, Typing (model algebra) [] expression target := by
  rw [typing_exists_exact]
  exact RigidRecordValueInference.infer_rejected_iff algebra expression data

theorem boundary_data : Data RigidRecordSourceBoundary.expression :=
  ⟨trivial, ⟨trivial, ⟨trivial, trivial⟩⟩⟩

/-- The actual computed quotient scheme retains both opaque alternatives
of the same closed expression. They are not collapsed to a rigid spine. -/
theorem inferred_boundary_has_both_instances (algebra : RowFlowSchemes.Algebra Row) :
    (infer RigidRecordSourceBoundary.expression).InstanceWith (model algebra)
        (RigidRecordQuotient.mk RigidRecordSourceBoundary.nested, algebra.empty) ∧
      (infer RigidRecordSourceBoundary.expression).InstanceWith (model algebra)
        (RigidRecordQuotient.mk RigidRecordSourceBoundary.flat, algebra.empty) := by
  constructor
  · apply (result_instances_exact algebra (infer RigidRecordSourceBoundary.expression)
      (RigidRecordSourceBoundary.nested, algebra.empty)).mpr
    exact (RigidRecordValueInference.infer_instances_exact algebra _ boundary_data _).mpr
      (RigidRecordSourceBoundary.typed_nested algebra)
  · apply (result_instances_exact algebra (infer RigidRecordSourceBoundary.expression)
      (RigidRecordSourceBoundary.flat, algebra.empty)).mpr
    exact (RigidRecordValueInference.infer_instances_exact algebra _ boundary_data _).mpr
      (RigidRecordSourceBoundary.typed_flat algebra)

theorem boundary_quotient_types_distinct (leRow : Row → Row → Prop) :
    RigidRecordQuotient.mk (leRow := leRow) RigidRecordSourceBoundary.nested ≠
      RigidRecordQuotient.mk RigidRecordSourceBoundary.flat := by
  intro same
  exact (RigidRecordSourceBoundary.result_types_incomparable leRow).1
    ((RigidRecordQuotient.mk_eq_mk_iff _ _).mp same).1

end Yulang.RigidRecordValueQuotient
