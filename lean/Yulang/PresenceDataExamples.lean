import Yulang.PresenceDataSafety

/-!
# Presence-aware inference and runtime regressions

These examples exercise the real original AST and both actual entry points.
The string and integer literals denote their existing abstract base tags.
-/

namespace Yulang.PresenceDataExamples

open Inference (Expr)
open SourceDataRuntime (Value eval)
open PresenceDataTypes
open PresenceDataShapes (Shape ShapeFields)
open PresenceDataInference (Typing infer Result)

def supplied : Expr := .record 0 (.lit .str) (.record 1 (.lit .bool) .emptyRecord)
def knownPresent : Expr := .recordDefault 0 supplied (.lit .int)
def knownAbsent : Expr := .recordDefault 0 (.record 1 (.lit .bool) .emptyRecord) (.lit .int)

def computedBase : Expr :=
  .letE supplied (.field 0 (.recordDefault 0 (.var 0) (.lit .int)))

def invalidBase : Expr := .recordDefault 0 (.lit .bool) (.lit .int)
def hiddenInvalidFallback : Expr := .recordDefault 0 supplied (.field 2 .emptyRecord)
def hiddenUnsupportedFallback : Expr := .recordDefault 0 supplied (.lam (.var 0))

theorem present_inferred : infer knownPresent =
    .solved (.record (.cons 0 (.base .str) (.cons 1 (.base .bool) .nil))) := rfl

theorem absent_inferred : infer knownAbsent =
    .solved (.record (.cons 1 (.base .bool) (.cons 0 (.base .int) .nil))) := rfl

theorem computed_inferred : infer computedBase = .solved (.base .str) := rfl

theorem invalid_base_rejected : infer invalidBase = .rejected := rfl
theorem hidden_invalid_rejected : infer hiddenInvalidFallback = .rejected := rfl
theorem hidden_unsupported : infer hiddenUnsupportedFallback = .unsupported := rfl

/-- A hidden default is still evaluated; a missing-field failure is not
silently skipped just because the base already supplies the field. -/
theorem hidden_fallback_evaluated :
    eval [] hiddenInvalidFallback = .error (.missingField 2) := rfl

theorem hidden_invalid_untypable : ¬ ∃ type, Typing [] hiddenInvalidFallback type :=
  ((PresenceDataInference.infer_rejected_iff hiddenInvalidFallback).mp hidden_invalid_rejected).2

theorem present_runtime : eval [] knownPresent =
    .ok (.record [(0, .base .str), (1, .base .bool)]) :=
  PresenceDataSafety.inferred_evaluates knownPresent _ present_inferred

theorem absent_runtime : eval [] knownAbsent =
    .ok (.record [(1, .base .bool), (0, .base .int)]) :=
  PresenceDataSafety.inferred_evaluates knownAbsent _ absent_inferred

theorem computed_runtime : eval [] computedBase = .ok (.base .str) :=
  PresenceDataSafety.inferred_evaluates computedBase _ computed_inferred

/-- The optional input includes records whose existing field is a string.
Consequently the unknown-base operator cannot promise only the integer default. -/
theorem unknown_base_not_int_only :
    ¬ Typing [optional 0 (base .str), base .int] (PresenceDataSafety.defaultOperator 0)
      (required 0 (base .int)) := by
  intro typed
  have bounded := (PresenceDataSafety.optional_operator_principal 0 (base .str) (base .int) _).mp typed
  have sourceValid : optional 0 (base .str) (.record [(0, .base .str)]) :=
    required_optional 0 (base .str) _ ⟨trivial, .base .str, rfl, rfl⟩
  have wrong := bounded (.record [(0, .base .str)])
    ⟨[(0, .base .str)], .base .int, sourceValid, rfl, rfl⟩
  simp [required, records, lookup, SourceDataRuntime.Fields.lookup, base, exact] at wrong

def checks : List (String × Bool) := [
  ("present field keeps its original type and other fields", match infer knownPresent with
    | .solved (.record (.cons 0 (.base .str) (.cons 1 (.base .bool) .nil))) => true
    | _ => false),
  ("absent field receives the fallback type", match infer knownAbsent with
    | .solved (.record (.cons 1 (.base .bool) (.cons 0 (.base .int) .nil))) => true
    | _ => false),
  ("let, variable and field selection share the inferred base", match infer computedBase with
    | .solved (.base .str) => true
    | _ => false),
  ("scalar spread base is rejected", match infer invalidBase with
    | .rejected => true
    | _ => false),
  ("hidden failing default is rejected", match infer hiddenInvalidFallback with
    | .rejected => true
    | _ => false),
  ("unsupported hidden default is reported separately", match infer hiddenUnsupportedFallback with
    | .unsupported => true
    | _ => false),
  ("actual runtime evaluates the hidden default", match eval [] hiddenInvalidFallback with
    | .error (.missingField 2) => true
    | _ => false),
  ("actual runtime preserves the existing field", match eval [] computedBase with
    | .ok (.base .str) => true
    | _ => false)
  ]

theorem checks_correct : checks.all Prod.snd = true := by decide +kernel

end Yulang.PresenceDataExamples
