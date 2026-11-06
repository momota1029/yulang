import Yulang.SourceDataRuntime
import Yulang.EvaluationTrace

/-!
# Independent evaluation-order rules for the original data core

The judgments below use `Inference.Expr` and the actual runtime values/errors.
They are inductive rules for entering expressions, sequencing their children,
and applying value operations. They do not refer to either executable evaluator.
Failures retain exactly the observations made before the failure.

`run` is a separate executable evaluator recording expression-entry visits.
Its result agrees with `SourceDataRuntime.eval`, including strict fallback
evaluation for spread-first records. Functions, application and conditionals
are explicitly unsupported here; their argument or branch order is not claimed.
-/

namespace Yulang.SourceDataOrder

open Inference SourceDataRuntime
open EvaluationTrace (Logged)

abbrev Trace := List Expr
abbrev Observation := Logged Expr Error Value

inductive Unary where
  | fst
  | snd
  | field : Nat → Unary
  | variant : Nat → Unary

def Unary.expr : Unary → Expr → Expr
  | .fst, argument => .fst argument
  | .snd, argument => .snd argument
  | .field label, argument => .field label argument
  | .variant label, argument => .variant label argument

/-- A value operation performs no recursive expression evaluation. -/
def Unary.apply : Unary → Value → Result
  | .fst, .pair first _ => .ok first
  | .fst, _ => .error .expectedPair
  | .snd, .pair _ last => .ok last
  | .snd, _ => .error .expectedPair
  | .field label, .record fields =>
      match Fields.lookup label fields with
      | some value => .ok value
      | none => .error (.missingField label)
  | .field _, _ => .error .expectedRecord
  | .variant label, value => .ok (.variant label value)

inductive Binary where
  | pair
  | record : Nat → Binary
  | recordDefault : Nat → Binary

def Binary.expr : Binary → Expr → Expr → Expr
  | .pair, first, last => .pair first last
  | .record label, first, last => .record label first last
  | .recordDefault label, first, last => .recordDefault label first last

/-- Storage selection occurs after both expressions have been evaluated.
For a default, the first value is the base and the last is the fallback. -/
def Binary.apply : Binary → Value → Value → Result
  | .pair, first, last => .ok (.pair first last)
  | .record label, first, .record fields => .ok (.record (Fields.insert label first fields))
  | .record _, _, _ => .error .expectedRecord
  | .recordDefault label, .record fields, last =>
      .ok (.record (Fields.insertDefault label last fields))
  | .recordDefault _, _, _ => .error .expectedRecord

inductive Unsupported : Expr → Prop where
  | lam (body : Expr) : Unsupported (.lam body)
  | app (function argument : Expr) : Unsupported (.app function argument)
  | branch (condition yes no : Expr) : Unsupported (.branch condition yes no)

/-- Independent big-step rules with explicit order and error propagation.
Every recorded expression is entered before any of its children. -/
inductive Evaluates : List Value → Expr → Trace → Result → Prop where
  | bound (found : environment[index]? = some value) :
      Evaluates environment (.var index) [.var index] (.ok value)
  | unbound (missing : environment[index]? = none) :
      Evaluates environment (.var index) [.var index] (.error (.unboundVariable index))
  | literal (base : Base) : Evaluates environment (.lit base) [.lit base] (.ok (.base base))
  | empty : Evaluates environment .emptyRecord [.emptyRecord] (.ok (.record []))
  | unsupported (outside : Unsupported expression) :
      Evaluates environment expression [expression] (.error .unsupported)
  | unaryError (operation : Unary) (argument : Evaluates environment expression trace (.error error)) :
      Evaluates environment (operation.expr expression) (operation.expr expression :: trace) (.error error)
  | unaryValue (operation : Unary) (argument : Evaluates environment expression trace (.ok value)) :
      Evaluates environment (operation.expr expression) (operation.expr expression :: trace)
        (operation.apply value)
  | binaryFirstError (operation : Binary) (last : Expr)
      (first : Evaluates environment expression trace (.error error)) :
      Evaluates environment (operation.expr expression last)
        (operation.expr expression last :: trace) (.error error)
  | binaryLastError (operation : Binary)
      (first : Evaluates environment firstExpr firstTrace (.ok firstValue))
      (last : Evaluates environment lastExpr lastTrace (.error error)) :
      Evaluates environment (operation.expr firstExpr lastExpr)
        (operation.expr firstExpr lastExpr :: (firstTrace ++ lastTrace)) (.error error)
  | binaryValues (operation : Binary)
      (first : Evaluates environment firstExpr firstTrace (.ok firstValue))
      (last : Evaluates environment lastExpr lastTrace (.ok lastValue)) :
      Evaluates environment (operation.expr firstExpr lastExpr)
        (operation.expr firstExpr lastExpr :: (firstTrace ++ lastTrace))
        (operation.apply firstValue lastValue)
  | letError (body : Expr) (definition : Evaluates environment expression trace (.error error)) :
      Evaluates environment (.letE expression body) (.letE expression body :: trace) (.error error)
  | letValue (definition : Evaluates environment expression definitionTrace (.ok value))
      (body : Evaluates (value :: environment) bodyExpr bodyTrace result) :
      Evaluates environment (.letE expression bodyExpr)
        (.letE expression bodyExpr :: (definitionTrace ++ bodyTrace)) result

def run (environment : List Value) (expression : Expr) : Observation :=
  Logged.prepend [expression] <|
    match expression with
    | .var index => Logged.ofResult <|
        match environment[index]? with
        | some value => .ok value
        | none => .error (.unboundVariable index)
    | .lit base => Logged.ofResult (.ok (.base base))
    | .emptyRecord => Logged.ofResult (.ok (.record []))
    | .letE definition body =>
        (run environment definition).bind fun value => run (value :: environment) body
    | .pair first last =>
        Logged.sequence (run environment first) (fun _ => run environment last) Binary.pair.apply
    | .record label first last =>
        Logged.sequence (run environment first) (fun _ => run environment last) (Binary.record label).apply
    | .recordDefault label first last =>
        Logged.sequence (run environment first) (fun _ => run environment last)
          (Binary.recordDefault label).apply
    | .fst argument => (run environment argument).bind fun value => Logged.ofResult (Unary.fst.apply value)
    | .snd argument => (run environment argument).bind fun value => Logged.ofResult (Unary.snd.apply value)
    | .field label argument =>
        (run environment argument).bind fun value => Logged.ofResult ((Unary.field label).apply value)
    | .variant label argument =>
        (run environment argument).bind fun value => Logged.ofResult ((Unary.variant label).apply value)
    | _ => Logged.ofResult (.error .unsupported)

theorem run_unary (environment : List Value) (operation : Unary) (argument : Expr) :
    run environment (operation.expr argument) = Logged.prepend [operation.expr argument]
      ((run environment argument).bind fun value => Logged.ofResult (operation.apply value)) := by
  cases operation <;> rfl

theorem run_binary (environment : List Value) (operation : Binary) (first last : Expr) :
    run environment (operation.expr first last) = Logged.prepend [operation.expr first last]
      (Logged.sequence (run environment first) (fun _ => run environment last) operation.apply) := by
  cases operation <;> rfl

theorem run_let (environment : List Value) (definition body : Expr) :
    run environment (.letE definition body) = Logged.prepend [.letE definition body]
      ((run environment definition).bind fun value => run (value :: environment) body) := rfl

/-- Every independent derivation is reproduced by the traced executable. -/
theorem Evaluates.executable (evaluation : Evaluates environment expression trace result) :
    run environment expression = ⟨trace, result⟩ := by
  induction evaluation with
  | bound found => simp [run, found, Logged.ofResult, Logged.prepend]
  | unbound missing => simp [run, missing, Logged.ofResult, Logged.prepend]
  | literal | empty => rfl
  | unsupported outside => cases outside <;> rfl
  | unaryError operation _ ih => rw [run_unary, ih]; rfl
  | unaryValue operation _ ih =>
      rw [run_unary, ih]
      simp [Logged.bind, Logged.ofResult, Logged.prepend]
  | binaryFirstError operation _ _ ih => rw [run_binary, ih]; rfl
  | binaryLastError operation _ _ first last =>
      rw [run_binary, first, last, Logged.sequence_second_error]
      rfl
  | binaryValues operation _ _ first last =>
      rw [run_binary, first, last, Logged.sequence_values]
      rfl
  | letError _ _ ih => rw [run_let, ih]; rfl
  | letValue _ _ definition body =>
      rw [run_let, definition]
      simp only [Logged.bind_ok, body, Logged.prepend, List.singleton_append]

private theorem unary_run_spec (operation : Unary) (environment : List Value) (argument : Expr)
    (evaluated : Evaluates environment argument (run environment argument).trace (run environment argument).result) :
    Evaluates environment (operation.expr argument) (run environment (operation.expr argument)).trace
      (run environment (operation.expr argument)).result := by
  cases actual : run environment argument with
  | mk trace result =>
      rw [actual] at evaluated
      cases result with
      | error error =>
          simpa [run_unary, actual, Logged.bind, Logged.prepend] using
            Evaluates.unaryError operation evaluated
      | ok value =>
          simpa [run_unary, actual, Logged.bind, Logged.ofResult, Logged.prepend] using
            Evaluates.unaryValue operation evaluated

private theorem binary_run_spec (operation : Binary) (environment : List Value) (firstExpr lastExpr : Expr)
    (first : Evaluates environment firstExpr (run environment firstExpr).trace (run environment firstExpr).result)
    (last : Evaluates environment lastExpr (run environment lastExpr).trace (run environment lastExpr).result) :
    Evaluates environment (operation.expr firstExpr lastExpr)
      (run environment (operation.expr firstExpr lastExpr)).trace
      (run environment (operation.expr firstExpr lastExpr)).result := by
  cases actualFirst : run environment firstExpr with
  | mk firstTrace firstResult =>
      rw [actualFirst] at first
      cases firstResult with
      | error error =>
          simpa [run_binary, actualFirst, Logged.prepend] using
            Evaluates.binaryFirstError operation lastExpr first
      | ok firstValue =>
          cases actualLast : run environment lastExpr with
          | mk lastTrace lastResult =>
              rw [actualLast] at last
              cases lastResult with
              | error error =>
                  simpa [run_binary, actualFirst, actualLast, Logged.prepend] using
                    Evaluates.binaryLastError operation first last
              | ok lastValue =>
                  simpa [run_binary, actualFirst, actualLast, Logged.prepend] using
                    Evaluates.binaryValues operation first last

/-- The traced evaluator always produces an independent derivation, including
unbound variables, shape failures and unsupported syntax. -/
theorem run_spec (environment : List Value) (expression : Expr) :
    Evaluates environment expression (run environment expression).trace (run environment expression).result := by
  induction expression generalizing environment with
  | var index =>
      cases found : environment[index]? with
      | none => simpa [run, found, Logged.ofResult, Logged.prepend] using Evaluates.unbound found
      | some value => simpa [run, found, Logged.ofResult, Logged.prepend] using Evaluates.bound found
  | lit base => exact .literal base
  | emptyRecord => exact .empty
  | fst argument ih => exact unary_run_spec .fst environment argument (ih environment)
  | snd argument ih => exact unary_run_spec .snd environment argument (ih environment)
  | field label argument ih => exact unary_run_spec (.field label) environment argument (ih environment)
  | variant label argument ih => exact unary_run_spec (.variant label) environment argument (ih environment)
  | pair first last ihf ihl => exact binary_run_spec .pair environment first last (ihf environment) (ihl environment)
  | record label first last ihf ihl =>
      exact binary_run_spec (.record label) environment first last (ihf environment) (ihl environment)
  | recordDefault label first last ihf ihl =>
      exact binary_run_spec (.recordDefault label) environment first last (ihf environment) (ihl environment)
  | lam body => exact .unsupported (.lam body)
  | app function argument => exact .unsupported (.app function argument)
  | branch condition yes no => exact .unsupported (.branch condition yes no)
  | letE definition body ihd ihb =>
      have first := ihd environment
      cases actual : run environment definition with
      | mk definitionTrace result =>
          rw [actual] at first
          cases result with
          | error error =>
              simpa [run_let, actual, Logged.prepend] using Evaluates.letError body first
          | ok value =>
              have last := ihb (value :: environment)
              cases bodyActual : run (value :: environment) body with
              | mk bodyTrace bodyResult =>
                  rw [bodyActual] at last
                  simpa [run_let, actual, bodyActual, Logged.prepend] using Evaluates.letValue first last

theorem evaluates_iff_run (environment : List Value) (expression : Expr) (trace : Trace) (result : Result) :
    Evaluates environment expression trace result ↔ run environment expression = ⟨trace, result⟩ := by
  constructor
  · exact Evaluates.executable
  · intro actual
    simpa only [actual] using run_spec environment expression

theorem Evaluates.deterministic (first : Evaluates environment expression firstTrace firstResult)
    (last : Evaluates environment expression lastTrace lastResult) :
    firstTrace = lastTrace ∧ firstResult = lastResult :=
  Logged.mk.inj (first.executable.symm.trans last.executable)

/-! ## Agreement with the actual untraced runtime -/

@[simp] private theorem except_bind_ok {α β : Type} (value : α) (next : α → Except Error β) :
    ((.ok value : Except Error α) >>= next) = next value := rfl

@[simp] private theorem except_bind_error {α β : Type} (error : Error) (next : α → Except Error β) :
    ((.error error : Except Error α) >>= next) = .error error := rfl

/-- The independent rules describe the actual runtime result, including all
errors. Record shape checks occur only after both child evaluations succeed. -/
theorem Evaluates.runtime_result (evaluation : Evaluates environment expression trace result) :
    SourceDataRuntime.eval environment expression = result := by
  induction evaluation with
  | bound found => simp [SourceDataRuntime.eval, found]
  | unbound missing => simp [SourceDataRuntime.eval, missing]
  | literal | empty => rfl
  | unsupported outside => cases outside <;> rfl
  | unaryError operation _ ih =>
      cases operation <;> simp only [Unary.expr, SourceDataRuntime.eval, ih, except_bind_error]
  | @unaryValue _ _ _ value operation _ ih =>
      cases operation <;> cases value <;>
        simp only [Unary.expr, SourceDataRuntime.eval, ih, except_bind_ok, Unary.apply] <;> rfl
  | binaryFirstError operation _ _ ih =>
      cases operation <;> simp only [Binary.expr, SourceDataRuntime.eval, ih, except_bind_error]
  | binaryLastError operation _ _ first last =>
      cases operation <;> simp only [Binary.expr, SourceDataRuntime.eval, first, last,
        except_bind_ok, except_bind_error]
  | @binaryValues _ _ _ firstValue _ _ lastValue operation _ _ first last =>
      cases operation <;> cases firstValue <;> cases lastValue <;>
        simp only [Binary.expr, SourceDataRuntime.eval, first, last, except_bind_ok, Binary.apply] <;> rfl
  | letError _ _ ih => simp only [SourceDataRuntime.eval, ih, except_bind_error]
  | letValue _ _ definition body => simp only [SourceDataRuntime.eval, definition, except_bind_ok, body]

theorem run_result (environment : List Value) (expression : Expr) :
    (run environment expression).result = SourceDataRuntime.eval environment expression :=
  (run_spec environment expression).runtime_result.symm

theorem runtime_iff_evaluates (environment : List Value) (expression : Expr) (result : Result) :
    SourceDataRuntime.eval environment expression = result ↔
      ∃ trace, Evaluates environment expression trace result := by
  constructor
  · intro actual
    refine ⟨(run environment expression).trace, ?_⟩
    simpa only [run_result, actual] using run_spec environment expression
  · rintro ⟨_, evaluation⟩
    exact evaluation.runtime_result

/-! ## An independent written-order schedule and the failure-prefix theorem -/

/-- The structural schedule for this data evaluator. Unsupported expressions
are single visits; no traversal of their function bodies or arguments is claimed. -/
def writtenOrder (expression : Expr) : Trace :=
  expression :: match expression with
    | .letE first last | .pair first last | .record _ first last | .recordDefault _ first last =>
        writtenOrder first ++ writtenOrder last
    | .fst argument | .snd argument | .field _ argument | .variant _ argument => writtenOrder argument
    | _ => []

@[simp] theorem writtenOrder_unary (operation : Unary) (argument : Expr) :
    writtenOrder (operation.expr argument) = operation.expr argument :: writtenOrder argument := by
  cases operation <;> rfl

@[simp] theorem writtenOrder_binary (operation : Binary) (first last : Expr) :
    writtenOrder (operation.expr first last) =
      operation.expr first last :: (writtenOrder first ++ writtenOrder last) := by
  cases operation <;> rfl

/-- Successful evaluation enters every strict subexpression in written order,
including unused let definitions, hidden fields and discarded fallbacks. -/
theorem Evaluates.successful_order (evaluation : Evaluates environment expression trace result) :
    ∀ value, result = .ok value → trace = writtenOrder expression := by
  induction evaluation with
  | bound | literal | empty => intro _ _; rfl
  | unbound | unsupported | unaryError | binaryFirstError | binaryLastError | letError =>
      intro _ impossible
      cases impossible
  | unaryValue operation _ ih =>
      intro _ _
      rw [writtenOrder_unary, ih _ rfl]
  | binaryValues operation _ _ first last =>
      intro _ _
      rw [writtenOrder_binary, first _ rfl, last _ rfl]
  | letValue _ _ definition body =>
      intro value returned
      rw [writtenOrder, definition _ rfl, body value returned]

/-- A failed evaluation can stop partway through the structural schedule,
but cannot skip an earlier expression and then visit a later one. -/
theorem Evaluates.prefix (evaluation : Evaluates environment expression trace result) :
    ∃ remaining, trace ++ remaining = writtenOrder expression := by
  induction evaluation with
  | bound | unbound | literal | empty => exact ⟨[], rfl⟩
  | unsupported outside => cases outside <;> exact ⟨[], rfl⟩
  | unaryError operation _ ih =>
      obtain ⟨remaining, suffix⟩ := ih
      exact ⟨remaining, by simp only [List.cons_append, writtenOrder_unary, suffix]⟩
  | unaryValue operation argument _ =>
      exact ⟨[], by simp only [List.append_nil, writtenOrder_unary, argument.successful_order _ rfl]⟩
  | binaryFirstError operation last _ ih =>
      obtain ⟨remaining, suffix⟩ := ih
      exact ⟨remaining ++ writtenOrder last, by
        simp only [List.cons_append, ← List.append_assoc, writtenOrder_binary, suffix]⟩
  | binaryLastError operation first _ _ ih =>
      obtain ⟨remaining, suffix⟩ := ih
      exact ⟨remaining, by
        simp only [List.cons_append, List.append_assoc, writtenOrder_binary,
          first.successful_order _ rfl, suffix]⟩
  | binaryValues operation first last _ _ =>
      exact ⟨[], by simp only [List.append_nil, writtenOrder_binary,
        first.successful_order _ rfl, last.successful_order _ rfl]⟩
  | letError body _ ih =>
      obtain ⟨remaining, suffix⟩ := ih
      exact ⟨remaining ++ writtenOrder body, by
        simp only [List.cons_append, ← List.append_assoc, writtenOrder, suffix]⟩
  | letValue definition _ _ ih =>
      obtain ⟨remaining, suffix⟩ := ih
      exact ⟨remaining, by simp only [List.cons_append, List.append_assoc, writtenOrder,
        definition.successful_order _ rfl, suffix]⟩

theorem run_trace_prefix (environment : List Value) (expression : Expr) :
    ∃ remaining, (run environment expression).trace ++ remaining = writtenOrder expression :=
  (run_spec environment expression).prefix

theorem successful_run_trace (environment : List Value) (expression : Expr) (value : Value)
    (success : SourceDataRuntime.eval environment expression = .ok value) :
    (run environment expression).trace = writtenOrder expression :=
  (run_spec environment expression).successful_order value ((run_result environment expression).trans success)

end Yulang.SourceDataOrder
