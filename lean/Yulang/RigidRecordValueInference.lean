import Yulang.RigidRecordDemands
import Yulang.ConstraintProblems
import Yulang.InferenceModelMap

/-!
# Unconstrained parameter schemes for closed data expressions

This entry consumes the original `Inference.Expr`. Its supported fragment is
the recursive data syntax: literals, empty records, pairs, variants and record
extension. A non-record data tail is rejected, not silently normalized.

Every record retains two unconstrained value parameters. If the child schemes
evaluate to `H` and `R`, their actual construction slots are `H | alpha` and
`(R | beta) & {}`. The latter clamp uses only the already known fact that the
tail expression is a record. All choices of the finite parameter tuple work;
there are no residual constraints or assumed solver successes in a plan.

The two-sided retraction uses record congruence, not covariance toward an
arbitrary demanded tail. This is necessary to retain widened non-rigid tail
instances of nested literals under decision 39. Functions, variables, lets,
field selection, effects and recursive source expressions are outside this
entry; this module does not remove the `RecordFree` restriction of the existing
`SourcePrincipalInference` entry.
-/

namespace Yulang.RigidRecordValueInference

open Inference
open StructuralBase (Ty)
open RigidSemanticRecords (Subtype Equivalent)

universe u

variable {Row : Type u}

abbrev model (algebra : RowFlowSchemes.Algebra Row) : Model :=
  RigidSemanticRecords.model Row algebra.empty algebra.join algebra.le

inductive Plan where
  | lit : Base → Plan
  | emptyRecord : Plan
  | pair : Plan → Plan → Plan
  | variant : Nat → Plan → Plan
  | record : Nat → Plan → Plan → Plan
  deriving Repr, DecidableEq

def Plan.expression : Plan → Expr
  | .lit base => .lit base
  | .emptyRecord => .emptyRecord
  | .pair left right => .pair left.expression right.expression
  | .variant label payload => .variant label payload.expression
  | .record label head tail => .record label head.expression tail.expression

def Plan.recordShape : Plan → Bool
  | .emptyRecord | .record _ _ _ => true
  | _ => false

def Plan.Good : Plan → Prop
  | .lit _ | .emptyRecord => True
  | .pair left right => left.Good ∧ right.Good
  | .variant _ payload => payload.Good
  | .record _ head tail => head.Good ∧ tail.Good ∧ tail.recordShape = true

/-- A finite product of arbitrary value types, with no admissibility predicate. -/
def Plan.Parameters (Value : Type u) : Plan → Type u
  | .lit _ | .emptyRecord => PUnit
  | .pair left right => left.Parameters Value × right.Parameters Value
  | .variant _ payload => payload.Parameters Value
  | .record _ head tail => head.Parameters Value × tail.Parameters Value × Value × Value

def Plan.parameterCount : Plan → Nat
  | .lit _ | .emptyRecord => 0
  | .pair left right => left.parameterCount + right.parameterCount
  | .variant _ payload => payload.parameterCount
  | .record _ head tail => head.parameterCount + tail.parameterCount + 2

def Plan.defaultParameters (value : Value) : (plan : Plan) → plan.Parameters Value
  | .lit _ | .emptyRecord => PUnit.unit
  | .pair left right => ⟨left.defaultParameters value, right.defaultParameters value⟩
  | .variant _ payload => payload.defaultParameters value
  | .record _ head tail => ⟨head.defaultParameters value, tail.defaultParameters value, value, value⟩

def Plan.evaluate : (plan : Plan) → plan.Parameters (Ty Row) → Ty Row
  | .lit base, _ => .base base
  | .emptyRecord, _ => .emptyRecord
  | .pair left right, parameter => .pair (left.evaluate parameter.1) (right.evaluate parameter.2)
  | .variant label payload, parameter => .variant label (payload.evaluate parameter)
  | .record label head tail, parameter =>
      .record label (.union (head.evaluate parameter.1) parameter.2.2.1)
        (.inter (.union (tail.evaluate parameter.2.1) parameter.2.2.2) .emptyRecord)

/-- The same finite scheme can be evaluated directly on a semantic quotient
or another constructor-preserving inference model. -/
def Plan.evalWith (m : Model) : (plan : Plan) → plan.Parameters m.Ty → m.Ty
  | .lit base, _ => m.base base
  | .emptyRecord, _ => m.emptyRecord
  | .pair left right, parameter => m.pair (left.evalWith m parameter.1) (right.evalWith m parameter.2)
  | .variant label payload, parameter => m.variant label (payload.evalWith m parameter)
  | .record label head tail, parameter =>
      m.record label (m.union (head.evalWith m parameter.1) parameter.2.2.1)
        (m.inter (m.union (tail.evalWith m parameter.2.1) parameter.2.2.2) m.emptyRecord)

def Plan.mapParameters (map : Source → Target) :
    (plan : Plan) → plan.Parameters Source → plan.Parameters Target
  | .lit _, _ | .emptyRecord, _ => PUnit.unit
  | .pair left right, parameter =>
      ⟨left.mapParameters map parameter.1, right.mapParameters map parameter.2⟩
  | .variant _ payload, parameter => payload.mapParameters map parameter
  | .record _ head tail, parameter =>
      ⟨head.mapParameters map parameter.1, tail.mapParameters map parameter.2.1,
        map parameter.2.2.1, map parameter.2.2.2⟩

/-- All finite tuples of quotient parameters have representatives. No
admissibility condition is imposed on either tuple. -/
theorem Plan.mapParameters_surjective (map : Source → Target)
    (surjective : ∀ target, ∃ source, map source = target)
    (plan : Plan) (parameter : plan.Parameters Target) :
    ∃ original : plan.Parameters Source, plan.mapParameters map original = parameter := by
  induction plan with
  | lit base | emptyRecord => cases parameter; exact ⟨PUnit.unit, rfl⟩
  | pair left right ihl ihr =>
      obtain ⟨first, last⟩ := parameter
      obtain ⟨leftSource, leftEqual⟩ := ihl first
      obtain ⟨rightSource, rightEqual⟩ := ihr last
      exact ⟨⟨leftSource, rightSource⟩, by simp only [mapParameters, leftEqual, rightEqual]; rfl⟩
  | variant label payload ih => exact ih parameter
  | record label head tail ihh iht =>
      obtain ⟨headParameter, tailParameter, headUpper, tailUpper⟩ := parameter
      obtain ⟨headSource, headEqual⟩ := ihh headParameter
      obtain ⟨tailSource, tailEqual⟩ := iht tailParameter
      obtain ⟨headValue, headValueEqual⟩ := surjective headUpper
      obtain ⟨tailValue, tailValueEqual⟩ := surjective tailUpper
      exact ⟨⟨headSource, tailSource, headValue, tailValue⟩,
        by simp only [mapParameters, headEqual, tailEqual, headValueEqual, tailValueEqual]; rfl⟩

theorem Plan.evalWith_map (map : ModelMap source target) (plan : Plan)
    (parameter : plan.Parameters source.Ty) :
    map.value (plan.evalWith source parameter) =
      plan.evalWith target (plan.mapParameters map.value parameter) := by
  induction plan with
  | lit base => exact map.base base
  | emptyRecord => exact map.emptyRecord
  | pair left right ihl ihr =>
      simp only [evalWith, mapParameters, map.pair, ihl, ihr]
  | variant label payload ih =>
      change map.value (source.variant label (payload.evalWith source parameter)) =
        target.variant label (payload.evalWith target (payload.mapParameters map.value parameter))
      rw [map.variant, ih parameter]
  | record label head tail ihh iht =>
      simp only [evalWith, mapParameters, map.record, map.union, map.inter, map.emptyRecord, ihh, iht]

theorem Plan.evalWith_model (algebra : RowFlowSchemes.Algebra Row) (plan : Plan)
    (parameter : plan.Parameters (Ty Row)) :
    plan.evalWith (model algebra) parameter = plan.evaluate parameter := by
  induction plan with
  | lit base | emptyRecord => rfl
  | pair left right ihl ihr =>
      change Ty.pair (left.evalWith (model algebra) parameter.1)
        (right.evalWith (model algebra) parameter.2) =
          Ty.pair (left.evaluate parameter.1) (right.evaluate parameter.2)
      rw [ihl parameter.1, ihr parameter.2]
  | variant label payload ih =>
      change Ty.variant label (payload.evalWith (model algebra) parameter) =
        Ty.variant label (payload.evaluate parameter)
      rw [ih parameter]
  | record label head tail ihh iht =>
      change Ty.record label (.union (head.evalWith (model algebra) parameter.1) parameter.2.2.1)
        (.inter (.union (tail.evalWith (model algebra) parameter.2.1) parameter.2.2.2) .emptyRecord) = _
      rw [ihh parameter.1, iht parameter.2.1]
      rfl

def Plan.InstanceWith (m : Model) (plan : Plan) (target : Comp m) : Prop :=
  ∃ parameter : plan.Parameters m.Ty, Comp.le m (plan.evalWith m parameter, m.empty) target

def Plan.Instance (algebra : RowFlowSchemes.Algebra Row) (plan : Plan) (target : Comp (model algebra)) : Prop :=
  ∃ parameter : plan.Parameters (Ty Row),
    Comp.le (model algebra) (plan.evaluate parameter, algebra.empty) target

theorem Plan.instanceWith_model (algebra : RowFlowSchemes.Algebra Row) (plan : Plan)
    (target : Comp (model algebra)) :
    plan.InstanceWith (model algebra) target ↔ plan.Instance algebra target := by
  unfold InstanceWith Instance
  apply exists_congr
  intro parameter
  rw [Plan.evalWith_model algebra plan parameter]
  rfl

private theorem typing_upper (algebra : RowFlowSchemes.Algebra Row)
    {expression : Expr} {source target : Comp (model algebra)}
    (typed : Typing (model algebra) [] expression source)
    (below : Comp.le (model algebra) source target) :
    Typing (model algebra) [] expression target :=
  ConstraintProblems.typing_subsumption (model algebra) Subtype.trans algebra.refl
    (fun first last => algebra.trans first last) typed below

/-- The record clamp is above its lower bound whenever that lower bound is
itself an admissible tail. The free parameter is otherwise unrestricted. -/
theorem clamp_lower {leRow : Row → Row → Prop} {lower : Ty Row}
    (admissible : Subtype leRow lower .emptyRecord) (parameter : Ty Row) :
    Subtype leRow lower (.inter (.union lower parameter) .emptyRecord) :=
  .interIntro (.unionLeft _ _) admissible

/-- Every solution of the interval is recovered up to the semantic equality
needed by the record constructor. -/
theorem clamp_retract {leRow : Row → Row → Prop} {lower target : Ty Row}
    (above : Subtype leRow lower target) (admissible : Subtype leRow target .emptyRecord) :
    Equivalent leRow (.inter (.union lower target) .emptyRecord) target :=
  ⟨.trans (.interLeft _ _) (.unionElim above (.refl _)),
    .interIntro (.unionRight _ _) admissible⟩

theorem widen_retract {leRow : Row → Row → Prop} {lower target : Ty Row}
    (above : Subtype leRow lower target) : Equivalent leRow (.union lower target) target :=
  ⟨.unionElim above (.refl _), .unionRight _ _⟩

theorem Plan.record_below_empty {leRow : Row → Row → Prop} (plan : Plan)
    (shape : plan.recordShape = true) (parameter : plan.Parameters (Ty Row)) :
    Subtype leRow (plan.evaluate parameter) .emptyRecord := by
  cases plan with
  | emptyRecord => exact .refl _
  | record label head tail => exact RigidSemanticRecords.record_width label _ (.interRight _ _)
  | _ => cases shape

theorem Plan.nonrecord_not_below_empty {leRow : Row → Row → Prop} (plan : Plan)
    (shape : plan.recordShape = false) (parameter : plan.Parameters (Ty Row)) :
    ¬ Subtype leRow (plan.evaluate parameter) .emptyRecord := by
  intro below
  have fits := (RigidRecordDemands.subtype_iff_fits _ (.empty : StructuralBase.IsRecord (Ty.emptyRecord : Ty Row))).mp below
  cases plan with
  | emptyRecord | record => cases shape
  | lit | pair | variant => exact fits

/-- Every unconstrained parameter tuple constructs an original pure typing. -/
theorem Plan.sound (algebra : RowFlowSchemes.Algebra Row) (plan : Plan) (good : plan.Good)
    (parameter : plan.Parameters (Ty Row)) :
    Typing (model algebra) [] plan.expression (plan.evaluate parameter, algebra.empty) := by
  induction plan with
  | lit base => exact .lit ⟨.refl _, algebra.refl _⟩
  | emptyRecord => exact .emptyRecord ⟨.refl _, algebra.refl _⟩
  | pair left right ihl ihr =>
      exact .pair (ihl good.1 parameter.1) (ihr good.2 parameter.2)
        ⟨.refl _, (algebra.join_le_iff _ _ _).mpr ⟨algebra.refl _, algebra.refl _⟩⟩
  | variant label payload ih =>
      exact .variant (ih good parameter) ⟨.refl _, algebra.refl _⟩
  | record label head tail ihh iht =>
      have typedHead := typing_upper algebra (ihh good.1 parameter.1)
        (target := (.union (head.evaluate parameter.1) parameter.2.2.1, algebra.empty))
        ⟨.unionLeft _ _, algebra.refl _⟩
      have typedTail := typing_upper algebra (iht good.2.1 parameter.2.1)
        (target := (.inter (.union (tail.evaluate parameter.2.1) parameter.2.2.2) .emptyRecord, algebra.empty))
        ⟨clamp_lower (tail.record_below_empty good.2.2 parameter.2.1) _, algebra.refl _⟩
      exact .record typedHead typedTail (.interRight _ _)
        ⟨.refl _, (algebra.join_le_iff _ _ _).mpr ⟨algebra.refl _, algebra.refl _⟩⟩

/-- Every original instance supplies an unconstrained parameter tuple. The
record case retracts both intermediate slots rather than minimizing them. -/
theorem Plan.complete (algebra : RowFlowSchemes.Algebra Row) (plan : Plan) (good : plan.Good)
    (target : Comp (model algebra)) (typed : Typing (model algebra) [] plan.expression target) :
    plan.Instance algebra target := by
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
          exact .trans (RigidSemanticRecords.record_congr label
            (widen_retract headBelow.1) (clamp_retract tailBelow.1 admissible)).1 bounded.1

theorem Plan.instances_exact (algebra : RowFlowSchemes.Algebra Row) (plan : Plan)
    (good : plan.Good) (target : Comp (model algebra)) :
    plan.Instance algebra target ↔ Typing (model algebra) [] plan.expression target := by
  constructor
  · rintro ⟨parameter, below⟩
    exact typing_upper algebra (plan.sound algebra good parameter) below
  · exact plan.complete algebra good target

/-! ## Actual inference from the original source syntax -/

/-- Data syntax includes invalid record tails; such inputs are rejected. -/
def Data : Expr → Prop
  | .lit _ | .emptyRecord => True
  | .pair left right | .record _ left right => Data left ∧ Data right
  | .variant _ payload => Data payload
  | _ => False

theorem Plan.expression_data (plan : Plan) : Data plan.expression := by
  induction plan <;> simp_all [expression, Data]

inductive Result where
  | unsupported
  | rejected
  | inferred : Plan → Result
  deriving Repr, DecidableEq

inductive Status where
  | unsupported | rejected | inferred
  deriving Repr, DecidableEq

def Result.status : Result → Status
  | .unsupported => .unsupported
  | .rejected => .rejected
  | .inferred _ => .inferred

def Result.Instance (algebra : RowFlowSchemes.Algebra Row) (target : Comp (model algebra)) : Result → Prop
  | .inferred plan => plan.Instance algebra target
  | _ => False

def Result.InstanceWith (m : Model) (target : Comp m) : Result → Prop
  | .inferred plan => plan.InstanceWith m target
  | _ => False

theorem Result.instanceWith_model (algebra : RowFlowSchemes.Algebra Row)
    (target : Comp (model algebra)) (result : Result) :
    result.InstanceWith (model algebra) target ↔ result.Instance algebra target := by
  cases result with
  | inferred plan => exact plan.instanceWith_model algebra target
  | _ => rfl

/-- No type assignment, successful constraint solve, or semantic test is an
input. Each accepted record keeps its two free widening parameters. -/
def infer : Expr → Result
  | .lit base => .inferred (.lit base)
  | .emptyRecord => .inferred .emptyRecord
  | .pair left right =>
      match infer left, infer right with
      | .unsupported, _ | _, .unsupported => .unsupported
      | .rejected, _ | _, .rejected => .rejected
      | .inferred first, .inferred last => .inferred (.pair first last)
  | .variant label payload =>
      match infer payload with
      | .unsupported => .unsupported
      | .rejected => .rejected
      | .inferred body => .inferred (.variant label body)
  | .record label head tail =>
      match infer head, infer tail with
      | .unsupported, _ | _, .unsupported => .unsupported
      | .rejected, _ | _, .rejected => .rejected
      | .inferred first, .inferred last =>
          if last.recordShape then .inferred (.record label first last) else .rejected
  | _ => .unsupported

theorem infer_unsupported_iff (expression : Expr) : infer expression = .unsupported ↔ ¬ Data expression := by
  induction expression with
  | pair left right ihl ihr =>
      cases l : infer left <;> cases r : infer right <;>
        simp_all [infer, Data]
  | variant label payload ih =>
      cases result : infer payload <;> simp_all [infer, Data]
  | record label head tail ihh iht =>
      cases h : infer head <;> cases t : infer tail <;> simp_all [infer, Data]
      split <;> simp_all
  | _ => simp [infer, Data]

theorem infer_plan_correct (expression : Expr) (plan : Plan) (returned : infer expression = .inferred plan) :
    plan.Good ∧ plan.expression = expression := by
  induction expression generalizing plan with
  | lit base =>
      have same : Plan.lit base = plan := Result.inferred.inj returned
      subst plan
      exact ⟨trivial, rfl⟩
  | emptyRecord =>
      have same : Plan.emptyRecord = plan := Result.inferred.inj returned
      subst plan
      exact ⟨trivial, rfl⟩
  | pair left right ihl ihr =>
      cases l : infer left <;> cases r : infer right <;> simp_all [infer]
      rename_i first last
      obtain ⟨leftGood, leftExpression⟩ := ihl
      obtain ⟨rightGood, rightExpression⟩ := ihr
      try subst plan
      exact ⟨⟨leftGood, rightGood⟩, by simp [Plan.expression, leftExpression, rightExpression]⟩
  | variant label payload ih =>
      cases p : infer payload <;> simp_all [infer]
      rename_i body
      obtain ⟨good, same⟩ := ih
      try subst plan
      exact ⟨good, by simp [Plan.expression, same]⟩
  | record label head tail ihh iht =>
      cases h : infer head <;> cases t : infer tail <;> simp_all [infer]
      rename_i first last
      split at returned
      · rename_i shape
        obtain ⟨headGood, headExpression⟩ := ihh
        obtain ⟨tailGood, tailExpression⟩ := iht
        have same : Plan.record label first last = plan := Result.inferred.inj returned
        subst plan
        exact ⟨⟨headGood, tailGood, shape⟩, by simp [Plan.expression, headExpression, tailExpression]⟩
      · cases returned
  | _ => cases returned

/-- Every typing in the whole supported data grammar makes the actual
inference function succeed. In particular there is no semantic tail check
supplied by the caller. -/
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
          have tailInstance := last.complete algebra tailGood _ (by simpa [tailExpression] using tailTyped)
          obtain ⟨parameter, below⟩ := tailInstance
          have shape : last.recordShape = true := by
            cases shaped : last.recordShape with
            | true => rfl
            | false => exact False.elim (last.nonrecord_not_below_empty shaped parameter
                (.trans below.1 admissible))
          exact ⟨.record label first last, by simp [infer, h, t, shape]⟩
  | _ => cases data

/-- Complete principal instance family for every data expression, including
arbitrarily nested record construction and malformed data tails. -/
theorem infer_instances_exact (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (data : Data expression) (target : Comp (model algebra)) :
    (infer expression).Instance algebra target ↔ Typing (model algebra) [] expression target := by
  cases returned : infer expression with
  | unsupported => exact False.elim ((infer_unsupported_iff expression).mp returned data)
  | rejected =>
      constructor
      · intro impossible
        cases impossible
      · intro typed
        obtain ⟨plan, accepted⟩ := infer_complete algebra expression data target typed
        rw [returned] at accepted
        cases accepted
  | inferred plan =>
      obtain ⟨good, same⟩ := infer_plan_correct expression plan returned
      exact (plan.instances_exact algebra good target).trans (by rw [same])

theorem infer_principal_formula_exact (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (data : Data expression) (target : Comp (model algebra)) :
    (infer expression).Instance algebra target ↔
      (principal ([] : SchemeEnv Empty) expression).Holds (model algebra) (extend Empty.elim target) :=
  (infer_instances_exact algebra expression data target).trans
    (principal_exact (model algebra) expression [] [] Empty.elim
      (EnvRel.nil (model algebra) Empty.elim) target).symm

/-- Rejection is a proof of non-typability for this entire source fragment,
and every non-typable supported data expression is actually rejected. -/
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
          by simpa [same] using plan.sound algebra good (plan.defaultParameters .bottom)⟩)

end Yulang.RigidRecordValueInference
