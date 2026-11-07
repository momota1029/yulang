import Yulang.CommonPatternAlignedMatcher
import Yulang.ScopedCaseEvaluation

/-!
# Ordered case evaluation with canonical source or interfaces

This preserves the original first-match, false-guard, lazy-default and failure
behavior. The equality theorem includes all visits, errors, and final values.
It is an operational bridge, not yet the Common case-typing generation iff.
-/

namespace Yulang.CommonAlignedCaseEvaluation

open CaseValues EvaluationTrace
open CasePatterns (Pattern Observation success miss)
open CaseEvaluation (Event Arm)
open CommonPatternAlignedObservations
open CommonPatternBindingAlignment (LookupEq)

def testArm (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F))
    (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (index : Nat) (arm : Arm F D G B) (value : Value F) :
    Observation F (Event E) R :=
  (CommonPatternAlignedMatcher.run floatCheck defaultEval environment arm.pattern value).bind fun matched =>
    match matched with
    | none => miss
    | some bindings => match arm.guard with
      | none => success bindings
      | some guard => Logged.prepend [.guard index] <|
          (guardEval guard bindings).bind fun accepted =>
            if accepted then success bindings else miss

def runArms (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F))
    (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
    (value : Value F) (index : Nat) : List (Arm F D G B) → Logged (Event E) R (Option (Value F))
  | [] => Logged.ofResult (.ok none)
  | arm :: rest => Logged.prepend [.arm index] <|
      (testArm floatCheck defaultEval environment guardEval index arm value).bind fun selected =>
        match selected with
        | none => runArms floatCheck defaultEval environment guardEval bodyEval value (index + 1) rest
        | some bindings => Logged.prepend [.body index] <|
            (bodyEval arm.body bindings).bind fun result => Logged.ofResult (.ok (some result))

def eval (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F))
    (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
    (scrutinee : Logged (Event E) R (Value F)) (arms : List (Arm F D G B)) :
    Logged (Event E) R (Option (Value F)) :=
  Logged.prepend [.scrutinee] <| scrutinee.bind fun value =>
    runArms floatCheck defaultEval environment guardEval bodyEval value 0 arms

def NamedInvariant (evaluate : Code → Bindings F → Logged E R A) : Prop :=
  ∀ code first last, LookupEq first last → evaluate code first = evaluate code last

theorem testArm_equivalent (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F))
    (defaults : CommonPatternAlignedMatcher.DefaultInvariant defaultEval)
    (first last : Bindings F) (same : LookupEq first last)
    (guardEval : G → Bindings F → Logged (Event E) R Bool) (guards : NamedInvariant guardEval)
    (index : Nat) (arm : Arm F D G B) (valid : PatternBindingChecks.NamesValid arm.pattern) (value : Value F) :
    Equivalent (testArm floatCheck defaultEval first guardEval index arm value)
      (ScopedCaseEvaluation.testArm floatCheck defaultEval last guardEval index arm value) := by
  apply logged_bind (CommonPatternAlignedMatcher.run_equivalent floatCheck defaultEval defaults arm.pattern valid
    first last same value)
  intro a b related
  cases related with
  | miss => exact equivalent_miss
  | hit sameBindings =>
      cases selected : arm.guard with
      | none => exact equivalent_success sameBindings
      | some code =>
          apply logged_prepend
          apply logged_bind (relation := Eq)
            (by rw [guards code _ _ sameBindings]; exact logged_equal _)
          intro a b equal
          subst b
          cases a with
          | false => exact equivalent_miss
          | true => exact equivalent_success sameBindings

/-- Any finite source-valid arm list and arbitrary starting index. Earlier
arms, failed guards, default errors, all-arm failure and selected bodies keep
exactly the original observation. No successful arm or coverage is assumed. -/
theorem runArms_eq (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F))
    (defaults : CommonPatternAlignedMatcher.DefaultInvariant defaultEval)
    (first last : Bindings F) (same : LookupEq first last)
    (guardEval : G → Bindings F → Logged (Event E) R Bool) (guards : NamedInvariant guardEval)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F)) (bodies : NamedInvariant bodyEval)
    (value : Value F) (index : Nat) (arms : List (Arm F D G B))
    (valid : ∀ arm ∈ arms, PatternBindingChecks.NamesValid arm.pattern) :
    runArms floatCheck defaultEval first guardEval bodyEval value index arms =
      ScopedCaseEvaluation.runArms floatCheck defaultEval last guardEval bodyEval value index arms := by
  induction arms generalizing index with
  | nil => rfl
  | cons arm rest ih =>
      apply logged_eq_of_rel
      apply logged_prepend
      apply logged_bind (testArm_equivalent floatCheck defaultEval defaults first last same guardEval guards
        index arm (valid arm List.mem_cons_self) value)
      intro a b related
      cases related with
      | miss =>
          rw [ih (index + 1) (fun arm member => valid arm (List.mem_cons_of_mem _ member))]
          exact logged_equal _
      | hit sameBindings =>
          apply logged_prepend
          apply logged_bind (relation := Eq)
            (by rw [bodies arm.body _ _ sameBindings]; exact logged_equal _)
          intro a b equal
          subst b
          exact logged_equal _

theorem eval_eq (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F))
    (defaults : CommonPatternAlignedMatcher.DefaultInvariant defaultEval)
    (first last : Bindings F) (same : LookupEq first last)
    (guardEval : G → Bindings F → Logged (Event E) R Bool) (guards : NamedInvariant guardEval)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F)) (bodies : NamedInvariant bodyEval)
    (scrutinee : Logged (Event E) R (Value F)) (arms : List (Arm F D G B))
    (valid : ∀ arm ∈ arms, PatternBindingChecks.NamesValid arm.pattern) :
    eval floatCheck defaultEval first guardEval bodyEval scrutinee arms =
      ScopedCaseEvaluation.eval floatCheck defaultEval last guardEval bodyEval scrutinee arms := by
  simp only [eval, ScopedCaseEvaluation.eval,
    runArms_eq floatCheck defaultEval defaults first last same guardEval guards bodyEval bodies _ _ arms valid]

theorem data_body_invariant (outer : Bindings F) : NamedInvariant (CaseDataTerms.bodyEval outer) :=
  fun code first last same => CommonPatternBindingAlignment.data_eval_lookup_eq code
    (first ++ outer) (last ++ outer) (same.append outer)

theorem data_guard_invariant (outer : Bindings F) : NamedInvariant (CaseDataTerms.guardEval outer) := by
  intro code first last same
  unfold CaseDataTerms.guardEval
  rw [CommonPatternBindingAlignment.data_eval_lookup_eq code _ _ (same.append outer)]

/-- The concrete data-default/guard/body evaluator discharges every name
invariance premise. Every finite valid source arm list and every scrutinee
observation retain the original complete ordered-case observation. -/
theorem data_evaluation_eq (floatCheck : F → F → Bool) (outer : Bindings F)
    (scrutinee : CaseDataTerms.Result F)
    (arms : List (Arm F (CaseDataTerms.Expr F) (CaseDataTerms.Expr F) (CaseDataTerms.Expr F)))
    (valid : ∀ arm ∈ arms, PatternBindingChecks.NamesValid arm.pattern) :
    eval floatCheck CaseDataTerms.defaultEval outer (CaseDataTerms.guardEval outer) (CaseDataTerms.bodyEval outer)
      scrutinee arms =
    ScopedCaseEvaluation.eval floatCheck CaseDataTerms.defaultEval outer
      (CaseDataTerms.guardEval outer) (CaseDataTerms.bodyEval outer) scrutinee arms :=
  eval_eq floatCheck CaseDataTerms.defaultEval CommonPatternAlignedMatcher.data_defaults_invariant
    outer outer (fun _ => rfl) _ (data_guard_invariant outer) _ (data_body_invariant outer) scrutinee arms valid

end Yulang.CommonAlignedCaseEvaluation
