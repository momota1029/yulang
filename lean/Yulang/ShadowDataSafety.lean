import Yulang.SourceDataSafety
import Yulang.ShadowRecordValueQuotient

/-!
# The latest record inference result describes the actual source evaluation

The decision-40 subtype relation preserves the independently defined masked
finite-data meaning. That meaning descends to the semantic quotient, with no
choice of canonical representative and no additional source restriction.

The first-order operational theorem applies to the original `Typing` in the
latest raw model and quotient. The executable data inference bridge quantifies
over every free quotient parameter and every widened scheme instance. A
single actual evaluation result satisfies them all.

This is a sound interpretation, not a characterization of subtyping by set
inclusion. Its source restriction is explicit: data/let/accessor syntax here;
full higher-order, effectful or recursive source evaluation is not claimed.
-/

namespace Yulang.ShadowDataSafety

open Inference
open StructuralBase (Ty)
open SourceDataRuntime
open DataTypeSemantics

universe u
variable {Row : Type u}

theorem subtype_preserves {leRow : Row → Row → Prop} :
    Preserves (ShadowSemanticRecords.Subtype leRow) := by
  intro source target below
  induction below with
  | refl => exact fun _ _ valid => valid
  | trans _ _ first last => exact fun mask value valid => last mask value (first mask value valid)
  | bottom => exact fun _ _ impossible => False.elim impossible
  | top => exact fun _ _ _ => trivial
  | unionLeft => exact fun _ _ valid => Or.inl valid
  | unionRight => exact fun _ _ valid => Or.inr valid
  | unionElim _ _ first last =>
      exact fun mask value valid => valid.elim (first mask value) (last mask value)
  | interLeft => exact fun _ _ valid => valid.1
  | interRight => exact fun _ _ valid => valid.2
  | interIntro _ _ first last =>
      exact fun mask value valid => ⟨first mask value valid, last mask value valid⟩
  | pair _ _ first last =>
      intro mask value valid
      cases value with
      | pair a b => exact ⟨first visible a valid.1, last visible b valid.2⟩
      | base | record | variant => exact False.elim valid
  | variant _ payload =>
      intro mask value valid
      cases value with
      | variant label body => exact ⟨valid.1, payload visible body valid.2⟩
      | base | pair | record => exact False.elim valid
  | arrow => exact fun _ _ impossible => False.elim impossible
  | record sourceShape targetShape available _ payloads =>
      intro mask value valid
      obtain ⟨fields, rfl⟩ := record_shape sourceShape mask value valid
      apply (rigid_record_iff targetShape mask fields).mpr
      intro label expected found unmasked
      obtain ⟨actual, actualFound⟩ := available label expected found
      obtain ⟨item, itemFound, itemValid⟩ :=
        (rigid_record_iff sourceShape mask fields).mp valid label actual actualFound unmasked
      exact ⟨item, itemFound, payloads label actual expected actualFound found visible item itemValid⟩
  | recordCongr _ _ _ _ headForward _ tailForward _ =>
      intro mask value valid
      cases value with
      | record fields =>
          refine ⟨?_, tailForward _ _ valid.2⟩
          intro unmasked
          obtain ⟨item, found, good⟩ := valid.1 unmasked
          exact ⟨item, found, headForward visible item good⟩
      | base | pair | variant => exact False.elim valid
  | recordTail _ _ tail =>
      intro mask value valid
      cases value with
      | record fields => exact ⟨valid.1, tail _ _ valid.2⟩
      | base | pair | variant => exact False.elim valid
  | shadowErase label head hidden tail =>
      exact fun mask value valid => (record_shadow label head hidden tail mask value).mp valid
  | shadowInsert label head hidden tail =>
      exact fun mask value valid => (record_shadow label head hidden tail mask value).mpr valid

/-- Semantic types have well-defined data meanings independently of their
representatives. This is not executable canonicalization. -/
def QuotientHolds {leRow : Row → Row → Prop}
    (type : ShadowRecordQuotient.QTy leRow) (mask : Mask) (value : Value) : Prop :=
  Quotient.lift (s := ShadowRecordQuotient.typeSetoid leRow) (fun raw => Holds raw mask value)
    (fun _ _ same => propext ⟨subtype_preserves same.1 mask value,
      subtype_preserves same.2 mask value⟩) type

@[simp] theorem quotientHolds_mk {leRow : Row → Row → Prop}
    (type : Ty Row) (mask : Mask) (value : Value) :
    QuotientHolds (ShadowRecordQuotient.mk (leRow := leRow) type) mask value ↔
      Holds type mask value := Iff.rfl

/-- The original, independent typing judgement ensures actual evaluation
success, including nonrecursive lets and real field lookup. -/
theorem typing_evaluates (algebra : RowFlowSchemes.Algebra Row)
    (expression : Expr) (supported : Supported expression)
    (target : Comp (ShadowRecordValueInference.model algebra))
    (typed : Typing (ShadowRecordValueInference.model algebra) [] expression target) :
    ∃ value, eval [] expression = .ok value ∧ Holds target.1 visible value :=
  SourceDataSafety.closed_typing_evaluates algebra (ShadowSemanticRecords.Subtype algebra.le)
    subtype_preserves expression supported target typed

theorem quotient_typing_evaluates (algebra : RowFlowSchemes.Algebra Row)
    (expression : Expr) (supported : Supported expression)
    (target : Comp (ShadowRecordValueQuotient.model algebra))
    (typed : Typing (ShadowRecordValueQuotient.model algebra) [] expression target) :
    ∃ value, eval [] expression = .ok value ∧ QuotientHolds target.1 visible value := by
  rcases target with ⟨type, row⟩
  revert typed
  refine Quotient.inductionOn type ?_
  intro representative typed
  exact typing_evaluates algebra expression supported (representative, row)
    ((ShadowRecordQuotientInference.closed_typing_exact algebra.empty algebra.join
      algebra.le algebra.refl expression (representative, row)).mp typed)

/-- Every solved principal formula in this source fragment has the same
operational guarantee; there is no shape-resolved intermediate AST premise. -/
theorem principal_evaluates (algebra : RowFlowSchemes.Algebra Row)
    (expression : Expr) (supported : Supported expression)
    (target : Comp (ShadowRecordValueQuotient.model algebra))
    (solved : (principal ([] : SchemeEnv Empty) expression).Holds
      (ShadowRecordValueQuotient.model algebra) (extend Empty.elim target)) :
    ∃ value, eval [] expression = .ok value ∧ QuotientHolds target.1 visible value :=
  quotient_typing_evaluates algebra expression supported target
    ((principal_exact (ShadowRecordValueQuotient.model algebra) expression [] [] Empty.elim
      (EnvRel.nil _ _) target).mp solved)

/-- Actual inference success supplies the source's runtime value, and all
unconstrained quotient parameter tuples validate that very same value. -/
theorem inferred_evaluates (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (plan : RigidRecordValueInference.Plan)
    (inferred : RigidRecordValueInference.infer expression = .inferred plan) :
    ∃ value, eval [] expression = .ok value ∧
      ∀ parameter : plan.Parameters (ShadowRecordValueQuotient.model algebra).Ty,
        QuotientHolds (plan.evalWith (ShadowRecordValueQuotient.model algebra) parameter)
          visible value := by
  have supported : Supported expression := by
    rw [← (RigidRecordValueInference.infer_plan_correct expression plan inferred).2]
    exact SourceDataSafety.data_supported plan.expression plan.expression_data
  have typed parameter := ShadowRecordValueQuotient.infer_plan_sound algebra expression plan inferred parameter
  obtain ⟨value, evaluated, _⟩ := quotient_typing_evaluates algebra expression supported _
    (typed (plan.defaultParameters (ShadowRecordQuotient.mk .bottom)))
  refine ⟨value, evaluated, ?_⟩
  intro parameter
  obtain ⟨other, otherEvaluated, otherValid⟩ :=
    quotient_typing_evaluates algebra expression supported _ (typed parameter)
  have equal : value = other := Except.ok.inj (evaluated.symm.trans otherEvaluated)
  simpa [equal] using otherValid

/-- The entire inferred family, including final subsumption, preserves its
runtime meaning. New shadow-equivalent instances are included. -/
theorem instance_evaluates (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (plan : RigidRecordValueInference.Plan)
    (inferred : RigidRecordValueInference.infer expression = .inferred plan)
    (target : Comp (ShadowRecordValueQuotient.model algebra))
    (instanceTyped : plan.InstanceWith (ShadowRecordValueQuotient.model algebra) target) :
    ∃ value, eval [] expression = .ok value ∧ QuotientHolds target.1 visible value := by
  have data : RigidRecordValueInference.Data expression := by
    rw [← (RigidRecordValueInference.infer_plan_correct expression plan inferred).2]
    exact plan.expression_data
  apply quotient_typing_evaluates algebra expression (SourceDataSafety.data_supported expression data) target
  apply (ShadowRecordValueQuotient.infer_instances_exact algebra expression data target).mp
  simpa [inferred, RigidRecordValueInference.Result.InstanceWith] using instanceTyped

/-- Inference success excludes each of the evaluator's actual error results. -/
theorem inferred_no_error (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (plan : RigidRecordValueInference.Plan)
    (inferred : RigidRecordValueInference.infer expression = .inferred plan) (error : Error) :
    eval [] expression ≠ .error error := by
  obtain ⟨value, evaluated, _⟩ := inferred_evaluates algebra expression plan inferred
  rw [evaluated]
  intro impossible
  cases impossible

end Yulang.ShadowDataSafety
