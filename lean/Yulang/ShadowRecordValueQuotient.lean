import Yulang.ShadowRecordValueInference
import Yulang.ShadowRecordExamples
import Yulang.RigidRecordValueQuotient

/-!
# Principal data inference on the latest semantic quotient

The same executable plan now ranges over all semantic quotient types of
decision 40. Parameter tuples remain entirely free. The source AST, algorithm
and original declarative typing rules are unchanged.
-/

namespace Yulang.ShadowRecordValueQuotient

open Inference
open RigidRecordValueInference (Plan Result Data infer)

universe u
variable {Row : Type u}

abbrev model (algebra : RowFlowSchemes.Algebra Row) : Model :=
  ShadowRecordQuotientInference.model algebra

theorem value_surjective (leRow : Row → Row → Prop)
    (value : ShadowRecordQuotient.QTy leRow) :
    ∃ original : StructuralBase.Ty Row, ShadowRecordQuotient.mk original = value := by
  refine Quotient.inductionOn value ?_
  exact fun original => ⟨original, rfl⟩

theorem plan_instances_exact (algebra : RowFlowSchemes.Algebra Row) (plan : Plan)
    (target : Comp (ShadowRecordValueInference.model algebra)) :
    plan.InstanceWith (model algebra) (ShadowRecordQuotient.mk target.1, target.2) ↔
      plan.InstanceWith (ShadowRecordValueInference.model algebra) target :=
  RigidRecordValueQuotient.plan_instances_transport
    (ShadowRecordQuotientInference.quotientMap algebra.empty algebra.join algebra.le algebra.refl)
    (fun proof => proof) (fun proof => proof) (value_surjective algebra.le) plan target

theorem result_instances_exact (algebra : RowFlowSchemes.Algebra Row) (result : Result)
    (target : Comp (ShadowRecordValueInference.model algebra)) :
    result.InstanceWith (model algebra) (ShadowRecordQuotient.mk target.1, target.2) ↔
      result.InstanceWith (ShadowRecordValueInference.model algebra) target := by
  cases result with
  | inferred plan => exact plan_instances_exact algebra plan target
  | _ => rfl

theorem infer_instances_exact (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (data : Data expression) (target : Comp (model algebra)) :
    (infer expression).InstanceWith (model algebra) target ↔
      Typing (model algebra) [] expression target := by
  rcases target with ⟨value, row⟩
  refine Quotient.inductionOn value ?_
  intro representative
  exact (result_instances_exact algebra (infer expression) (representative, row)).trans
    ((ShadowRecordValueInference.infer_instances_exact algebra expression data (representative, row)).trans
      (ShadowRecordQuotientInference.closed_typing_exact algebra.empty algebra.join
        algebra.le algebra.refl expression (representative, row)).symm)

theorem infer_principal_formula_exact (algebra : RowFlowSchemes.Algebra Row)
    (expression : Expr) (data : Data expression) (target : Comp (model algebra)) :
    (infer expression).InstanceWith (model algebra) target ↔
      (principal ([] : SchemeEnv Empty) expression).Holds (model algebra) (extend Empty.elim target) :=
  (infer_instances_exact algebra expression data target).trans
    (principal_exact (model algebra) expression [] [] Empty.elim
      (EnvRel.nil (model algebra) Empty.elim) target).symm

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
  exact ⟨parameter, ShadowRecordQuotient.le_refl _, algebra.refl _⟩

theorem typing_exists_exact (algebra : RowFlowSchemes.Algebra Row) (expression : Expr) :
    (∃ target, Typing (model algebra) [] expression target) ↔
      ∃ original, Typing (ShadowRecordValueInference.model algebra) [] expression original := by
  constructor
  · rintro ⟨target, typed⟩
    obtain ⟨original, same⟩ := ShadowRecordQuotientInference.computation_surjective
      algebra.empty algebra.join algebra.le algebra.refl target
    refine ⟨original, ?_⟩
    apply (ShadowRecordQuotientInference.closed_typing_exact algebra.empty algebra.join
      algebra.le algebra.refl expression original).mp
    rw [← same] at typed
    exact typed
  · rintro ⟨original, typed⟩
    exact ⟨(ShadowRecordQuotient.mk original.1, original.2),
      (ShadowRecordQuotientInference.closed_typing_exact algebra.empty algebra.join
        algebra.le algebra.refl expression original).mpr typed⟩

theorem infer_rejected_iff (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (data : Data expression) :
    infer expression = .rejected ↔ ¬ ∃ target, Typing (model algebra) [] expression target := by
  rw [typing_exists_exact]
  exact ShadowRecordValueInference.infer_rejected_iff algebra expression data

/-- Both formerly separated alternatives are still inferred, and are equal. -/
theorem inferred_boundary_instances_equal (algebra : RowFlowSchemes.Algebra Row) :
    (infer RigidRecordSourceBoundary.expression).InstanceWith (model algebra)
        (ShadowRecordQuotient.mk RigidRecordSourceBoundary.nested, algebra.empty) ∧
      (infer RigidRecordSourceBoundary.expression).InstanceWith (model algebra)
        (ShadowRecordQuotient.mk RigidRecordSourceBoundary.flat, algebra.empty) ∧
      ShadowRecordQuotient.mk (leRow := algebra.le) RigidRecordSourceBoundary.nested =
        ShadowRecordQuotient.mk RigidRecordSourceBoundary.flat :=
  ⟨(infer_instances_exact algebra _ RigidRecordValueQuotient.boundary_data _).mpr
      (ShadowRecordExamples.source_has_equal_instances algebra).1,
    (infer_instances_exact algebra _ RigidRecordValueQuotient.boundary_data _).mpr
      (ShadowRecordExamples.source_has_equal_instances algebra).2.1,
    ShadowRecordExamples.boundary_quotient_equal algebra.le⟩

end Yulang.ShadowRecordValueQuotient
