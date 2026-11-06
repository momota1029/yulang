import Yulang.DataTypeSemantics
import Yulang.RigidRecordValueInference

/-!
# Original-source data typing prevents runtime failures

The evaluator and its error cases are defined independently in
`SourceDataRuntime`. This theorem covers its entire first-order source
fragment, including variables, both declarative let routes, record construction
and selection, pairs and projections, and variants. The runtime has no shape
indices. A typed selection must actually find the requested field.

For a polymorphic let, the right-hand side is evaluated once. Each possible
typing of its captured scheme is interpreted using the induction hypothesis;
determinism identifies that result with the single stored value. The source
typing rules and their quantifiers are unchanged.

The generic theorem requires semantic preservation of the subtype relation,
not evaluation safety as an assumption. `DataTypeSemantics` proves that
preservation for concrete record relations. The final bridge starts from the
actual existing data inference result and validates all its free parameters.
Functions, applications, effects, conditionals and recursive source programs
are not part of this first-order runtime theorem.
-/

namespace Yulang.SourceDataSafety

open Inference
open StructuralBase (Ty)
open SourceDataRuntime
open DataTypeSemantics

universe u v

@[local simp] private theorem bind_ok (value : α) (next : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= next) = next value := rfl

@[local simp] private theorem map_ok (value : α) (map : α → β) :
    map <$> (Except.ok value : Except ε α) = Except.ok (map value) := rfl

@[local simp] private theorem pure_ok (value : α) :
    (pure value : Except ε α) = Except.ok value := rfl

/-- Runtime environments satisfy every instance of their lexical bindings. -/
def Environment (m : Model) (meaning : m.Ty → Value → Prop)
    (bindings : List (Binding m)) (runtime : List Value) : Prop :=
  ∀ (index : Nat) binding type, bindings[index]? = some binding → BindingTyping m binding type →
    ∃ value, runtime[index]? = some value ∧ meaning type.1 value

theorem Environment.nil (m : Model) (meaning : m.Ty → Value → Prop) :
    Environment m meaning [] [] := by
  intro index binding type found
  simp at found

theorem Environment.cons {m : Model} {meaning : m.Ty → Value → Prop}
    {bindings : List (Binding m)} {runtime : List Value}
    (environment : Environment m meaning bindings runtime)
    (binding : Binding m) (value : Value)
    (valid : ∀ type, BindingTyping m binding type → meaning type.1 value) :
    Environment m meaning (binding :: bindings) (value :: runtime) := by
  intro index selected type found typed
  cases index with
  | zero =>
      have same : binding = selected := Option.some.inj found
      subst selected
      exact ⟨value, rfl, valid type typed⟩
  | succ index =>
      exact environment index selected type found typed

/-- The structural constructors and row algebra stay fixed while the value
preorder is supplied independently of the evaluator. -/
def model (algebra : RowFlowSchemes.Algebra Row)
    (relation : Ty Row → Ty Row → Prop) : Model :=
  { StructuralBase.model Row algebra.empty algebra.join algebra.le with subTy := relation }

/-- Every independently typed supported original expression evaluates to a
value of its declared value type. No evaluator success is an input. -/
theorem typing_evaluates (algebra : RowFlowSchemes.Algebra Row)
    (relation : Ty Row → Ty Row → Prop) (preserves : Preserves relation)
    (expression : Expr) (supported : Supported expression)
    (bindings : List (Binding (model algebra relation))) (runtime : List Value)
    (environment : Environment (model algebra relation)
      (fun type value => Holds type visible value) bindings runtime)
    (target : Comp (model algebra relation))
    (typed : Typing (model algebra relation) bindings expression target) :
    ∃ value, eval runtime expression = .ok value ∧ Holds target.1 visible value := by
  induction expression generalizing bindings runtime target with
  | recordDefault => cases typed
  | var index =>
      cases typed with
      | var found bindingTyped =>
          obtain ⟨value, valueFound, valid⟩ := environment index _ target found bindingTyped
          exact ⟨value, by simp [eval, valueFound], valid⟩
  | lit base =>
      cases typed with
      | lit below =>
          exact ⟨.base base, rfl, preserves below.1 visible (.base base) rfl⟩
  | emptyRecord =>
      cases typed with
      | emptyRecord below =>
          exact ⟨.record [], rfl, preserves below.1 visible (.record []) trivial⟩
  | pair left right ihl ihr =>
      cases typed with
      | pair leftTyped rightTyped below =>
          obtain ⟨first, firstEvaluated, firstValid⟩ :=
            ihl supported.1 bindings runtime environment _ leftTyped
          obtain ⟨last, lastEvaluated, lastValid⟩ :=
            ihr supported.2 bindings runtime environment _ rightTyped
          exact ⟨.pair first last, by simp [eval, firstEvaluated, lastEvaluated],
            preserves below.1 visible (.pair first last) ⟨firstValid, lastValid⟩⟩
  | fst expression ih =>
      cases typed with
      | fst pairTyped below =>
          obtain ⟨value, evaluated, valid⟩ := ih supported bindings runtime environment _ pairTyped
          cases value with
          | pair first last =>
              exact ⟨first, by simp [eval, evaluated], preserves below.1 visible first valid.1⟩
          | base | record | variant => exact False.elim valid
  | snd expression ih =>
      cases typed with
      | snd pairTyped below =>
          obtain ⟨value, evaluated, valid⟩ := ih supported bindings runtime environment _ pairTyped
          cases value with
          | pair first last =>
              exact ⟨last, by simp [eval, evaluated], preserves below.1 visible last valid.2⟩
          | base | record | variant => exact False.elim valid
  | variant label expression ih =>
      cases typed with
      | variant payloadTyped below =>
          obtain ⟨value, evaluated, valid⟩ := ih supported bindings runtime environment _ payloadTyped
          exact ⟨.variant label value, by simp [eval, evaluated],
            preserves below.1 visible (.variant label value) ⟨rfl, valid⟩⟩
  | record label head tail ihh iht =>
      cases typed with
      | record headTyped tailTyped admissible below =>
          obtain ⟨first, firstEvaluated, firstValid⟩ :=
            ihh supported.1 bindings runtime environment _ headTyped
          obtain ⟨last, lastEvaluated, lastValid⟩ :=
            iht supported.2 bindings runtime environment _ tailTyped
          have shape : Holds (.emptyRecord : Ty Row) visible last :=
            preserves admissible visible last lastValid
          cases last with
          | record fields =>
              exact ⟨.record (Fields.insert label first fields),
                by simp [eval, firstEvaluated, lastEvaluated],
                preserves below.1 visible _ (record_intro label _ _ first fields firstValid lastValid)⟩
          | base | pair | variant => exact False.elim shape
  | field label expression ih =>
      cases typed with
      | field recordTyped below =>
          obtain ⟨value, evaluated, valid⟩ := ih supported bindings runtime environment _ recordTyped
          cases value with
          | record fields =>
              obtain ⟨item, found, good⟩ := valid.1 (fun impossible => impossible)
              exact ⟨item, by simp [eval, evaluated, found], preserves below.1 visible item good⟩
          | base | pair | variant => exact False.elim valid
  | letE expression body ihv ihb =>
      cases typed with
      | letComputed valueTyped bodyTyped below =>
          rename_i valueType bodyType
          obtain ⟨value, evaluated, valid⟩ :=
            ihv supported.1 bindings runtime environment _ valueTyped
          have extended := environment.cons (.mono (Comp.pure (model algebra relation) valueType.1)) value (fun type instanceTyped => by
            cases instanceTyped with
            | mono sub => exact preserves sub.1 visible value valid)
          obtain ⟨result, bodyEvaluated, resultValid⟩ :=
            ihb supported.2 _ _ extended _ bodyTyped
          exact ⟨result, by simp [eval, evaluated, bodyEvaluated],
            preserves below.1 visible result resultValid⟩
      | letValue _ valueTyped bodyTyped =>
          obtain ⟨value, evaluated, _⟩ :=
            ihv supported.1 bindings runtime environment _ valueTyped
          have extended := environment.cons (.poly expression bindings) value (fun type instanceTyped => by
            cases instanceTyped with
            | poly otherTyped _ =>
                obtain ⟨otherValue, otherEvaluated, otherValid⟩ :=
                  ihv supported.1 bindings runtime environment _ otherTyped
                have same : value = otherValue := Except.ok.inj (evaluated.symm.trans otherEvaluated)
                simpa [same, Comp.pure] using otherValid)
          obtain ⟨result, bodyEvaluated, resultValid⟩ :=
            ihb supported.2 _ _ extended _ bodyTyped
          exact ⟨result, by simp [eval, evaluated, bodyEvaluated], resultValid⟩
  | lam | app | branch => cases supported

theorem closed_typing_evaluates (algebra : RowFlowSchemes.Algebra Row)
    (relation : Ty Row → Ty Row → Prop) (preserves : Preserves relation)
    (expression : Expr) (supported : Supported expression)
    (target : Comp (model algebra relation))
    (typed : Typing (model algebra relation) [] expression target) :
    ∃ value, eval [] expression = .ok value ∧ Holds target.1 visible value :=
  typing_evaluates algebra relation preserves expression supported [] []
    (Environment.nil _ _) target typed

theorem closed_typing_no_error (algebra : RowFlowSchemes.Algebra Row)
    (relation : Ty Row → Ty Row → Prop) (preserves : Preserves relation)
    (expression : Expr) (supported : Supported expression)
    (target : Comp (model algebra relation))
    (typed : Typing (model algebra relation) [] expression target) (error : Error) :
    eval [] expression ≠ .error error := by
  obtain ⟨value, evaluated, _⟩ :=
    closed_typing_evaluates algebra relation preserves expression supported target typed
  rw [evaluated]
  intro impossible
  cases impossible

theorem data_supported (expression : Expr) (data : RigidRecordValueInference.Data expression) :
    Supported expression := by
  induction expression <;> simp_all [RigidRecordValueInference.Data, Supported]

/-- The existing inference algorithm needs no runtime witness, and every one
of the inferred plan's free parameter tuples describes the same actual value. -/
theorem inferred_evaluates (algebra : RowFlowSchemes.Algebra Row) (expression : Expr)
    (plan : RigidRecordValueInference.Plan)
    (inferred : RigidRecordValueInference.infer expression = .inferred plan) :
    ∃ value, eval [] expression = .ok value ∧
      ∀ parameter : plan.Parameters (Ty Row), Holds (plan.evaluate parameter) visible value := by
  obtain ⟨good, same⟩ := RigidRecordValueInference.infer_plan_correct expression plan inferred
  have supported := data_supported plan.expression plan.expression_data
  have typed parameter := plan.sound algebra good parameter
  obtain ⟨value, evaluated, _⟩ := closed_typing_evaluates algebra
    (RigidSemanticRecords.Subtype algebra.le) rigid_subtype_preserves
    plan.expression supported _ (typed (plan.defaultParameters .bottom))
  refine ⟨value, by simpa [same] using evaluated, ?_⟩
  intro parameter
  obtain ⟨other, otherEvaluated, otherValid⟩ := closed_typing_evaluates algebra
    (RigidSemanticRecords.Subtype algebra.le) rigid_subtype_preserves
    plan.expression supported _ (typed parameter)
  have equal : value = other := Except.ok.inj (evaluated.symm.trans otherEvaluated)
  simpa [equal] using otherValid

end Yulang.SourceDataSafety
