import Yulang.ShadowRecordQuotientInference
import Yulang.RigidRecordValueInference

/-!
# The existing data inference algorithm is exact after decision 40

The algorithm, source grammar, parameter tuples and generated plans are reused
unchanged. We prove soundness and completeness for the new independent subtype
relation, including all typings newly made available by hidden-field equality.
No graph model, admissible parameter tuple or assumed solver success occurs in
the principal-instance theorem.
-/

namespace Yulang.ShadowRecordValueInference

open Inference
open StructuralBase (Ty IsRecord)
open ShadowSemanticRecords (Subtype Equivalent)
open RigidRecordValueInference (Plan Result Data infer infer_plan_correct infer_unsupported_iff)

universe u
variable {Row : Type u}

abbrev model (algebra : RowFlowSchemes.Algebra Row) : Model :=
  ShadowSemanticRecords.model Row algebra.empty algebra.join algebra.le

/-- This observation separates non-record outer constructors from records.
It is not an operational interpretation or a substitute for type safety. -/
private def nonrecord : Ty Row → Prop
  | .bottom => False
  | .top => True
  | .union a b => nonrecord a ∨ nonrecord b
  | .inter a b => nonrecord a ∧ nonrecord b
  | .emptyRecord | .record _ _ _ => False
  | _ => True

private theorem nonrecord_proper {type : Ty Row} (shape : IsRecord type) :
    ¬ nonrecord type := by
  cases shape <;> exact id

private theorem nonrecord_mono {leRow : Row → Row → Prop} {a b : Ty Row}
    (below : Subtype leRow a b) : nonrecord a → nonrecord b := by
  induction below with
  | refl => exact id
  | trans _ _ first last => exact fun h => last (first h)
  | bottom => exact False.elim
  | top => exact fun _ => trivial
  | unionLeft => exact Or.inl
  | unionRight => exact Or.inr
  | unionElim _ _ first last => exact fun h => h.elim first last
  | interLeft => exact And.left
  | interRight => exact And.right
  | interIntro _ _ first last => exact fun h => ⟨first h, last h⟩
  | pair | variant | arrow => exact fun _ => trivial
  | record shape _ _ _ _ => exact fun h => False.elim (nonrecord_proper shape h)
  | recordCongr | recordTail | shadowErase | shadowInsert => exact False.elim

theorem nonrecord_plan_not_below_empty {leRow : Row → Row → Prop}
    (plan : Plan) (shape : plan.recordShape = false)
    (parameter : plan.Parameters (Ty Row)) :
    ¬ Subtype leRow (plan.evaluate parameter) .emptyRecord := by
  intro below
  have observed := nonrecord_mono below
  cases plan with
  | emptyRecord | record => cases shape
  | lit | pair | variant => exact observed trivial

theorem evalWith_model (algebra : RowFlowSchemes.Algebra Row) (plan : Plan)
    (parameter : plan.Parameters (Ty Row)) :
    plan.evalWith (model algebra) parameter = plan.evaluate parameter := by
  induction plan with
  | lit base | emptyRecord => rfl
  | pair left right ihl ihr =>
      change Ty.pair (left.evalWith (model algebra) parameter.1)
        (right.evalWith (model algebra) parameter.2) = _
      rw [ihl, ihr]
      rfl
  | variant label payload ih =>
      change Ty.variant label (payload.evalWith (model algebra) parameter) = _
      exact congrArg (Ty.variant label) (ih parameter)
  | record label head tail ihh iht =>
      change Ty.record label
        (.union (head.evalWith (model algebra) parameter.1) parameter.2.2.1)
        (.inter (.union (tail.evalWith (model algebra) parameter.2.1) parameter.2.2.2) .emptyRecord) = _
      rw [ihh, iht]
      rfl

/-- Soundness applies to every free parameter tuple of the existing plan. -/
theorem plan_sound (algebra : RowFlowSchemes.Algebra Row) (plan : Plan)
    (good : plan.Good) (parameter : plan.Parameters (Ty Row)) :
    Typing (model algebra) [] plan.expression (plan.evaluate parameter, algebra.empty) :=
  ShadowRecordInference.rigid_closed_typing_preserved algebra.empty algebra.join algebra.le
    plan.expression _ (plan.sound algebra good parameter)

private theorem typing_upper (algebra : RowFlowSchemes.Algebra Row)
    {expression : Expr} {source target : Comp (model algebra)}
    (typed : Typing (model algebra) [] expression source)
    (below : Comp.le (model algebra) source target) :
    Typing (model algebra) [] expression target :=
  ConstraintProblems.typing_subsumption (model algebra) Subtype.trans algebra.refl
    (fun first last => algebra.trans first last) typed below

theorem widen_retract {leRow : Row → Row → Prop} {lower target : Ty Row}
    (above : Subtype leRow lower target) : Equivalent leRow (.union lower target) target :=
  ⟨.unionElim above (.refl _), .unionRight _ _⟩

theorem clamp_retract {leRow : Row → Row → Prop} {lower target : Ty Row}
    (above : Subtype leRow lower target) (admissible : Subtype leRow target .emptyRecord) :
    Equivalent leRow (.inter (.union lower target) .emptyRecord) target :=
  ⟨.trans (.interLeft _ _) (.unionElim above (.refl _)),
    .interIntro (.unionRight _ _) admissible⟩

/-- Completeness includes new source instances, not just preservation of old
ones. The recovered parameters are unrestricted values of the new type model. -/
theorem plan_complete (algebra : RowFlowSchemes.Algebra Row) (plan : Plan)
    (good : plan.Good) (target : Comp (model algebra))
    (typed : Typing (model algebra) [] plan.expression target) :
    ∃ parameter : plan.Parameters (Ty Row),
      Comp.le (model algebra) (plan.evaluate parameter, algebra.empty) target := by
  induction plan generalizing target with
  | lit base =>
      cases typed with
      | lit bounded => exact ⟨PUnit.unit, bounded⟩
  | emptyRecord =>
      cases typed with
      | emptyRecord bounded => exact ⟨PUnit.unit, bounded⟩
  | pair left right ihl ihr =>
      cases typed with
      | pair leftTyped rightTyped bounded =>
          obtain ⟨leftParameter, leftBelow⟩ := ihl good.1 _ leftTyped
          obtain ⟨rightParameter, rightBelow⟩ := ihr good.2 _ rightTyped
          exact ⟨⟨leftParameter, rightParameter⟩,
            .trans (.pair leftBelow.1 rightBelow.1) bounded.1, algebra.empty_le _⟩
  | variant label payload ih =>
      cases typed with
      | variant payloadTyped bounded =>
          obtain ⟨parameter, below⟩ := ih good _ payloadTyped
          exact ⟨parameter, .trans (.variant below.1) bounded.1, algebra.empty_le _⟩
  | record label head tail ihh iht =>
      cases typed with
      | record headTyped tailTyped admissible bounded =>
          rename_i actualHead actualTail
          obtain ⟨headParameter, headBelow⟩ := ihh good.1 _ headTyped
          obtain ⟨tailParameter, tailBelow⟩ := iht good.2.1 _ tailTyped
          refine ⟨⟨headParameter, tailParameter, actualHead.1, actualTail.1⟩, ?_, algebra.empty_le _⟩
          exact .trans (ShadowSemanticRecords.record_congr label
            (widen_retract headBelow.1) (clamp_retract tailBelow.1 admissible)).1 bounded.1

theorem plan_instances_exact (algebra : RowFlowSchemes.Algebra Row) (plan : Plan)
    (good : plan.Good) (target : Comp (model algebra)) :
    plan.InstanceWith (model algebra) target ↔ Typing (model algebra) [] plan.expression target := by
  constructor
  · rintro ⟨parameter, below⟩
    change Comp.le (model algebra)
      (plan.evalWith (model algebra) (show plan.Parameters (Ty Row) from parameter), algebra.empty) target at below
    rw [evalWith_model algebra plan parameter] at below
    exact typing_upper algebra (plan_sound algebra plan good parameter) below
  · intro typed
    obtain ⟨parameter, below⟩ := plan_complete algebra plan good target typed
    exact ⟨parameter, by rwa [evalWith_model]⟩

/-- Typability throughout the supported grammar forces actual solver success. -/
theorem infer_complete (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (data : Data expression) (target : Comp (model algebra))
    (typed : Typing (model algebra) [] expression target) :
    ∃ plan, infer expression = .inferred plan := by
  induction expression generalizing target with
  | lit base => exact ⟨.lit base, rfl⟩
  | emptyRecord => exact ⟨.emptyRecord, rfl⟩
  | pair left right ihl ihr =>
      cases typed with
      | pair leftTyped rightTyped _ =>
          obtain ⟨first, l⟩ := ihl data.1 _ leftTyped
          obtain ⟨last, r⟩ := ihr data.2 _ rightTyped
          exact ⟨.pair first last, by simp [infer, l, r]⟩
  | variant label payload ih =>
      cases typed with
      | variant payloadTyped _ =>
          obtain ⟨body, p⟩ := ih data _ payloadTyped
          exact ⟨.variant label body, by simp [infer, p]⟩
  | record label head tail ihh iht =>
      cases typed with
      | record headTyped tailTyped admissible _ =>
          obtain ⟨first, h⟩ := ihh data.1 _ headTyped
          obtain ⟨last, t⟩ := iht data.2 _ tailTyped
          obtain ⟨tailGood, tailExpression⟩ := infer_plan_correct tail last t
          obtain ⟨parameter, below⟩ := plan_complete algebra last tailGood _
            (by simpa [tailExpression] using tailTyped)
          have shape : last.recordShape = true := by
            cases shaped : last.recordShape with
            | true => rfl
            | false => exact False.elim (nonrecord_plan_not_below_empty last shaped parameter
                (.trans below.1 admissible))
          exact ⟨.record label first last, by simp [infer, h, t, shape]⟩
  | _ => cases data

theorem infer_instances_exact (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (data : Data expression) (target : Comp (model algebra)) :
    (infer expression).InstanceWith (model algebra) target ↔
      Typing (model algebra) [] expression target := by
  cases returned : infer expression with
  | unsupported => exact False.elim ((infer_unsupported_iff expression).mp returned data)
  | rejected =>
      constructor
      · intro impossible; cases impossible
      · intro typed
        obtain ⟨plan, accepted⟩ := infer_complete algebra expression data target typed
        rw [returned] at accepted
        cases accepted
  | inferred plan =>
      obtain ⟨good, same⟩ := infer_plan_correct expression plan returned
      exact (plan_instances_exact algebra plan good target).trans (by rw [same])

theorem infer_principal_formula_exact (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (data : Data expression) (target : Comp (model algebra)) :
    (infer expression).InstanceWith (model algebra) target ↔
      (principal ([] : SchemeEnv Empty) expression).Holds (model algebra)
        (extend Empty.elim target) :=
  (infer_instances_exact algebra expression data target).trans
    (principal_exact (model algebra) expression [] [] Empty.elim
      (EnvRel.nil (model algebra) Empty.elim) target).symm

theorem infer_rejected_iff (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (data : Data expression) :
    infer expression = .rejected ↔ ¬ ∃ target, Typing (model algebra) [] expression target := by
  constructor
  · intro rejected ⟨target, typed⟩
    obtain ⟨plan, accepted⟩ := infer_complete algebra expression data target typed
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases returned : infer expression with
    | unsupported => exact False.elim ((infer_unsupported_iff expression).mp returned data)
    | rejected => rfl
    | inferred plan =>
        obtain ⟨good, same⟩ := infer_plan_correct expression plan returned
        exact False.elim (absent ⟨(plan.evaluate (plan.defaultParameters .bottom), algebra.empty),
          by simpa [same] using plan_sound algebra plan good (plan.defaultParameters .bottom)⟩)

end Yulang.ShadowRecordValueInference
