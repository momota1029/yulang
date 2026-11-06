import Yulang.CaseEvaluation

/-!
# Concrete data leaves for the ordered case evaluator

This finite, first-order syntax evaluates values, resolved named variables,
products, records and their projections, variants, resolved nominal
construction, finite lists and computed lets. Every syntax visit is logged.
Record constructors evaluate both operands
in written order; only pattern defaults are lazy.

The independent judgement is a value-safety judgement using `CaseValues.Ty`
predicates. Its semantic widening is not asserted to be the language's nominal
subtyping or a source annotation checker. There is no type inference, recursion,
function application, effect handler, cast, or nested case in this leaf syntax.
The main theorem discharges the case evaluator's default/guard/body contracts
from syntax derivations. Guards convert actual Boolean values; they are not
supplied by an arbitrary Boolean oracle.

Bindings prepend a resolved scope to an explicitly supplied outer lexical
environment. The source pass that chooses a default's lexical environment,
resolves names or rejects duplicate binders remains outside this module.
Nominal type and constructor identities are supplied by an earlier pass;
declaration validation, constructor defaults and cast insertion are not chosen
by this resolved constructor. Its payload expression is evaluated strictly.
-/

namespace Yulang.CaseDataTerms

open CaseValues LiteralValues EvaluationTrace

inductive Expr (F : Type) where
  | value : Value F → Expr F
  | var : Nat → Expr F
  | pair : Expr F → Expr F → Expr F
  | fst : Expr F → Expr F
  | snd : Expr F → Expr F
  | emptyRecord
  | record : Nat → Expr F → Expr F → Expr F
  | recordDefault : Nat → Expr F → Expr F → Expr F
  | field : Nat → Expr F → Expr F
  | variant : Nat → Expr F → Expr F
  | nominal : Nat → Nat → Expr F → Expr F
  | nil
  | cons : Expr F → Expr F → Expr F
  | letE : Nat → Expr F → Expr F → Expr F
  deriving Repr

inductive Error where
  | unboundVariable : Nat → Error
  | expectedPair
  | expectedRecord
  | missingField : Nat → Error
  | expectedList
  | expectedBool
  deriving DecidableEq, Repr

abbrev Result (F : Type) := Logged (CaseEvaluation.Event (Expr F)) Error (Value F)

def pure (value : Value F) : Result F := Logged.ofResult (.ok value)
def fail (error : Error) : Result F := Logged.ofResult (.error error)

/-- Runtime record insertion removes every hidden duplicate payload. -/
def insert (name : Nat) (value : Value F) (fields : Bindings F) : Bindings F :=
  (name, value) :: fields.filter (fun field => field.1 != name)

def insertDefault (name : Nat) (value : Value F) (fields : Bindings F) : Bindings F :=
  if (lookup name fields).isSome then fields else fields ++ [(name, value)]

def eval (environment : Bindings F) (expression : Expr F) : Result F :=
  Logged.prepend [.source expression] <|
    match expression with
    | .value value => pure value
    | .var name => match lookup name environment with
      | some value => pure value
      | none => fail (.unboundVariable name)
    | .pair left right => (eval environment left).bind fun first =>
        (eval environment right).bind fun last => pure (.pair first last)
    | .fst pair => (eval environment pair).bind fun value => match value with
      | .pair first _ => pure first
      | _ => fail .expectedPair
    | .snd pair => (eval environment pair).bind fun value => match value with
      | .pair _ last => pure last
      | _ => fail .expectedPair
    | .emptyRecord => pure (.record [])
    | .record name head tail => (eval environment head).bind fun first =>
        (eval environment tail).bind fun rest => match rest with
          | .record fields => pure (.record (insert name first fields))
          | _ => fail .expectedRecord
    | .recordDefault name source fallback => (eval environment source).bind fun base =>
        (eval environment fallback).bind fun value => match base with
          | .record fields => pure (.record (insertDefault name value fields))
          | _ => fail .expectedRecord
    | .field name record => (eval environment record).bind fun value => match value with
      | .record fields => match lookup name fields with
        | some item => pure item
        | none => fail (.missingField name)
      | _ => fail .expectedRecord
    | .variant tag payload => (eval environment payload).bind fun value => pure (.variant tag value)
    | .nominal typeId ctorId payload => (eval environment payload).bind fun value =>
        pure (.nominal typeId ctorId value)
    | .nil => pure (.list [])
    | .cons head tail => (eval environment head).bind fun first =>
        (eval environment tail).bind fun rest => match rest with
          | .list values => pure (.list (first :: values))
          | _ => fail .expectedList
    | .letE name value body => (eval environment value).bind fun result =>
        eval ((name, result) :: environment) body

def lookupType (name : Nat) : List (Nat × Ty F) → Option (Ty F)
  | [] => none
  | (label, type) :: rest => if name = label then some type else lookupType name rest

theorem lookup_typed (environment : Bindings F) (types : List (Nat × Ty F))
    (valid : BindingsHold types environment) (name : Nat) (type : Ty F)
    (found : lookupType name types = some type) :
    ∃ value, lookup name environment = some value ∧ type value := by
  induction valid with
  | nil => cases found
  | @cons headType types values label value headValid tailValid ih =>
      by_cases same : name = label
      · subst label
        have equal : headType = type := by simpa [lookupType] using found
        subst type
        exact ⟨value, by simp [lookup], headValid⟩
      · have tailFound : lookupType name types = some type := by
          simpa [lookupType, same] using found
        obtain ⟨value, present, valueValid⟩ := ih tailFound
        exact ⟨value, by simpa [lookup, same] using present, valueValid⟩

/-- Constructor images retain all constraints of the two inferred operands. -/
def recordType (name : Nat) (head tail : Ty F) : Ty F := fun result =>
  ∃ value fields, head value ∧ tail (.record fields) ∧
    result = .record (insert name value fields)

def defaultType (name : Nat) (source fallback : Ty F) : Ty F := fun result =>
  ∃ fields value, source (.record fields) ∧ fallback value ∧
    result = .record (insertDefault name value fields)

def consType (head tail : Ty F) : Ty F := fun result =>
  ∃ value values, head value ∧ tail (.list values) ∧ result = .list (value :: values)

inductive Typing : List (Nat × Ty F) → Expr F → Ty F → Prop where
  | value : Typing types (.value value) (Ty.exact value)
  | var : lookupType name types = some type → Typing types (.var name) type
  | pair : Typing types left a → Typing types right b → Typing types (.pair left right) (Ty.pair a b)
  | fst : Typing types pair (Ty.pair a b) → Typing types (.fst pair) a
  | snd : Typing types pair (Ty.pair a b) → Typing types (.snd pair) b
  | emptyRecord : Typing types .emptyRecord (Ty.exact (.record []))
  | record : Typing types head headType → Typing types tail tailType → Ty.Le tailType Ty.records →
      Typing types (.record name head tail) (recordType name headType tailType)
  | recordDefault : Typing types source sourceType → Typing types fallback fallbackType →
      Ty.Le sourceType Ty.records →
      Typing types (.recordDefault name source fallback) (defaultType name sourceType fallbackType)
  | field : Typing types source input → Ty.Le input (Ty.required name payload) →
      Typing types (.field name source) payload
  | variant : Typing types payload type → Typing types (.variant tag payload) (Ty.variant tag type)
  | nominal : Typing types payload type →
      Typing types (.nominal typeId ctorId payload) (Ty.nominal typeId ctorId type)
  | nil : Typing types .nil (Ty.exact (.list []))
  | cons : Typing types head headType → Typing types tail tailType → Ty.Le tailType (Ty.list Ty.any) →
      Typing types (.cons head tail) (consType headType tailType)
  | letE : Typing types value input → Typing ((name, input) :: types) body output →
      Typing types (.letE name value body) output
  | widen : Typing types expression input → Ty.Le input output → Typing types expression output

@[local simp] private theorem except_bind_ok (value : A) (next : A → Except R B) :
    (Except.ok value).bind next = next value := rfl

/-- Total evaluation follows from ordinary syntax typing and a valid initial
environment. No successful execution or bound for an expression is assumed. -/
theorem typing_evaluates {F : Type} {types : List (Nat × Ty F)}
    {expression : Expr F} {type : Ty F} (typed : Typing types expression type) :
    ∀ environment : Bindings F, BindingsHold types environment →
      ∃ value, (eval environment expression).result = .ok value ∧ type value := by
  induction typed with
  | value => intro environment valid; exact ⟨_, rfl, rfl⟩
  | var found =>
      intro environment valid
      obtain ⟨value, present, valueValid⟩ := lookup_typed environment _ valid _ _ found
      exact ⟨value, by simp [eval, present, pure, Logged.ofResult], valueValid⟩
  | pair left right leftIH rightIH =>
      intro environment valid
      obtain ⟨first, firstEval, firstValid⟩ := leftIH environment valid
      obtain ⟨last, lastEval, lastValid⟩ := rightIH environment valid
      refine ⟨.pair first last, ?_, firstValid, lastValid⟩
      simp [eval, Logged.bind_result, firstEval, lastEval, pure, Logged.ofResult]
  | fst pair pairIH =>
      intro environment valid
      obtain ⟨value, evaluated, valueValid⟩ := pairIH environment valid
      cases value with
      | pair first last =>
          exact ⟨first, by simp [eval, Logged.bind_result, evaluated, pure, Logged.ofResult], valueValid.1⟩
      | literal | record | variant | nominal | list => cases valueValid
  | snd pair pairIH =>
      intro environment valid
      obtain ⟨value, evaluated, valueValid⟩ := pairIH environment valid
      cases value with
      | pair first last =>
          exact ⟨last, by simp [eval, Logged.bind_result, evaluated, pure, Logged.ofResult], valueValid.2⟩
      | literal | record | variant | nominal | list => cases valueValid
  | emptyRecord => intro environment valid; exact ⟨_, rfl, rfl⟩
  | record head tail isRecord headIH tailIH =>
      intro environment valid
      obtain ⟨first, firstEval, firstValid⟩ := headIH environment valid
      obtain ⟨rest, restEval, restValid⟩ := tailIH environment valid
      have shape := isRecord rest restValid
      cases rest with
      | record fields =>
          refine ⟨_, ?_, first, fields, firstValid, restValid, rfl⟩
          simp [eval, Logged.bind_result, firstEval, restEval, pure, Logged.ofResult]
      | literal | pair | variant | nominal | list => cases shape
  | recordDefault source fallback isRecord sourceIH fallbackIH =>
      intro environment valid
      obtain ⟨base, baseEval, baseValid⟩ := sourceIH environment valid
      obtain ⟨value, valueEval, valueValid⟩ := fallbackIH environment valid
      have shape := isRecord base baseValid
      cases base with
      | record fields =>
          refine ⟨_, ?_, fields, value, baseValid, valueValid, rfl⟩
          simp [eval, Logged.bind_result, baseEval, valueEval, pure, Logged.ofResult]
      | literal | pair | variant | nominal | list => cases shape
  | field source required sourceIH =>
      intro environment valid
      obtain ⟨value, evaluated, valueValid⟩ := sourceIH environment valid
      have field := required value valueValid
      cases value with
      | record fields =>
          obtain ⟨item, present, itemValid⟩ := field
          exact ⟨item, by simp [eval, Logged.bind_result, evaluated, present, pure, Logged.ofResult], itemValid⟩
      | literal | pair | variant | nominal | list => cases field
  | variant payload payloadIH =>
      intro environment valid
      obtain ⟨value, evaluated, valueValid⟩ := payloadIH environment valid
      exact ⟨.variant _ value, by simp [eval, Logged.bind_result, evaluated, pure, Logged.ofResult], rfl, valueValid⟩
  | nominal payload payloadIH =>
      intro environment valid
      obtain ⟨value, evaluated, valueValid⟩ := payloadIH environment valid
      exact ⟨.nominal _ _ value,
        by simp [eval, Logged.bind_result, evaluated, pure, Logged.ofResult], rfl, rfl, valueValid⟩
  | nil => intro environment valid; exact ⟨_, rfl, rfl⟩
  | cons head tail isList headIH tailIH =>
      intro environment valid
      obtain ⟨first, firstEval, firstValid⟩ := headIH environment valid
      obtain ⟨rest, restEval, restValid⟩ := tailIH environment valid
      have shape := isList rest restValid
      cases rest with
      | list values =>
          refine ⟨_, ?_, first, values, firstValid, restValid, rfl⟩
          simp [eval, Logged.bind_result, firstEval, restEval, pure, Logged.ofResult]
      | literal | pair | record | variant | nominal => cases shape
  | letE value body valueIH bodyIH =>
      intro environment valid
      obtain ⟨first, firstEval, firstValid⟩ := valueIH environment valid
      obtain ⟨last, lastEval, lastValid⟩ := bodyIH _ (.cons firstValid valid)
      exact ⟨last, by simp [eval, Logged.bind_result, firstEval, lastEval], lastValid⟩
  | widen source below sourceIH =>
      intro environment valid
      obtain ⟨value, evaluated, valueValid⟩ := sourceIH environment valid
      exact ⟨value, evaluated, below value valueValid⟩

/-! ## Concrete case-leaf interfaces -/

def DefaultTyped (outerTypes : List (Nat × Ty F)) (expression : Expr F) (type : Ty F) : Prop :=
  Typing outerTypes expression type

def GuardTyped (outerTypes : List (Nat × Ty F)) (expression : Expr F)
    (bindingTypes : List (Nat × Ty F)) : Prop :=
  Typing (bindingTypes ++ outerTypes) expression (Ty.literal .bool)

def BodyTyped (outerTypes : List (Nat × Ty F)) (expression : Expr F)
    (bindingTypes : List (Nat × Ty F)) (type : Ty F) : Prop :=
  Typing (bindingTypes ++ outerTypes) expression type

def defaultEval (outer : Bindings F) (expression : Expr F) : Result F := eval outer expression

def bodyEval (outer : Bindings F) (expression : Expr F) (bindings : Bindings F) : Result F :=
  eval (bindings ++ outer) expression

def guardEval (outer : Bindings F) (expression : Expr F) (bindings : Bindings F) :
    Logged (CaseEvaluation.Event (Expr F)) Error Bool :=
  (eval (bindings ++ outer) expression).bind fun value =>
    match value with
    | .literal (.bool result) => Logged.ofResult (.ok result)
    | _ => Logged.ofResult (.error .expectedBool)

theorem default_sound (outer : Bindings F) (types : List (Nat × Ty F))
    (valid : BindingsHold types outer) :
    CasePatterns.DefaultSound (DefaultTyped types) (defaultEval outer) := by
  intro expression type typed
  exact typing_evaluates typed outer valid

theorem body_sound (outer : Bindings F) (types : List (Nat × Ty F))
    (valid : BindingsHold types outer) :
    CaseEvaluation.BodySound (BodyTyped types) (bodyEval outer) := by
  intro expression bindingTypes target typed bindings bindingsValid
  exact typing_evaluates typed _ (bindingsValid.append valid)

theorem guard_sound (outer : Bindings F) (types : List (Nat × Ty F))
    (valid : BindingsHold types outer) :
    CaseEvaluation.GuardSound (GuardTyped types) (guardEval outer) := by
  intro expression bindingTypes typed bindings bindingsValid
  obtain ⟨value, evaluated, valueValid⟩ := typing_evaluates typed _ (bindingsValid.append valid)
  cases value with
  | literal literal =>
      cases literal with
      | bool result =>
          exact ⟨result, by simp [guardEval, Logged.bind_result, evaluated, Logged.ofResult]⟩
      | int | float | str | unit => cases valueValid
  | pair | record | variant | nominal | list => cases valueValid

end Yulang.CaseDataTerms
