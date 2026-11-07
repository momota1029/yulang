import Yulang.ScopedCaseEvaluation

/-! Exact operational paths of the actual source-ordered case evaluator.
The judgments retain complete traces and original error identities. They
use actual pattern/default and guard/body observations and never require
every callback to succeed. No Common typing/coverage claim is inferred. -/

namespace Yulang.CommonCaseOrderedPaths

open CaseValues EvaluationTrace
open CaseEvaluation (Arm Event)

variable (floatCheck : F → F → Bool)
  (defaultEval : Bindings F → D → Logged (Event E) R (Value F))
  (environment : Bindings F) (guardEval : G → Bindings F → Logged (Event E) R Bool)
  (bodyEval : B → Bindings F → Logged (Event E) R (Value F))

inductive TestPath (index : Nat) (arm : Arm F D G B) (value : Value F) :
    List (Event E) → Except R (Option (Bindings F)) → Prop where
  | error (failed : (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result = .error error) :
      TestPath index arm value (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).trace
        (.error error)
  | miss (missed : (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result = .ok none) :
      TestPath index arm value (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).trace
        (.ok none)
  | unguarded (matched : (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result =
        .ok (some bindings)) (absent : arm.guard = none) :
      TestPath index arm value (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).trace
        (.ok (some bindings))
  | guarded (matched : (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result =
        .ok (some bindings)) (present : arm.guard = some code) :
      TestPath index arm value
        ((ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).trace ++
          .guard index :: (guardEval code bindings).trace)
        ((guardEval code bindings).result.map (fun accepted => if accepted then some bindings else none))

theorem TestPath.observation
    (path : TestPath floatCheck defaultEval environment guardEval index arm value events result) :
    ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value = ⟨events, result⟩ := by
  cases path with
  | error failed => simp [ScopedCaseEvaluation.testArm, Logged.bind, failed]
  | miss missed => simp [ScopedCaseEvaluation.testArm, Logged.bind, missed, CasePatterns.miss, Logged.ofResult]
  | unguarded matched absent =>
      simp [ScopedCaseEvaluation.testArm, Logged.bind, matched, absent, CasePatterns.success, Logged.ofResult]
  | guarded matched present =>
      simp only [ScopedCaseEvaluation.testArm, Logged.bind, matched, present, Logged.prepend]
      cases observed : (guardEval _ _).result with
      | error => simp [Except.map]
      | ok accepted =>
          cases accepted <;> simp [Except.map, CasePatterns.success, CasePatterns.miss, Logged.ofResult]

theorem testPath_actual (index : Nat) (arm : Arm F D G B) (value : Value F) :
    TestPath floatCheck defaultEval environment guardEval index arm value
      (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value).trace
      (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value).result := by
  cases matched : (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result with
  | error error =>
      have path : TestPath floatCheck defaultEval environment guardEval index arm value _ _ := .error matched
      rw [path.observation]
      exact path
  | ok option =>
      cases option with
      | none =>
          have path : TestPath floatCheck defaultEval environment guardEval index arm value _ _ := .miss matched
          rw [path.observation]
          exact path
      | some bindings =>
          cases guard : arm.guard with
          | none =>
              have path : TestPath floatCheck defaultEval environment guardEval index arm value _ _ := .unguarded matched guard
              rw [path.observation]
              exact path
          | some code =>
              have path : TestPath floatCheck defaultEval environment guardEval index arm value _ _ := .guarded matched guard
              rw [path.observation]
              exact path

inductive RunPath (value : Value F) : Nat → List (Arm F D G B) → List (Event E) → Except R (Option (Value F)) → Prop where
  | nil : RunPath value index [] [] (.ok none)
  | error (tested : TestPath floatCheck defaultEval environment guardEval index arm value events (.error error)) :
      RunPath value index (arm :: rest) (.arm index :: events) (.error error)
  | miss (tested : TestPath floatCheck defaultEval environment guardEval index arm value events (.ok none))
      (later : RunPath value (index + 1) rest more result) :
      RunPath value index (arm :: rest) (.arm index :: (events ++ more)) result
  | selected (tested : TestPath floatCheck defaultEval environment guardEval index arm value events (.ok (some bindings))) :
      RunPath value index (arm :: rest) (.arm index :: (events ++ .body index :: (bodyEval arm.body bindings).trace))
        ((bodyEval arm.body bindings).result.map some)

theorem RunPath.observation
    (path : RunPath floatCheck defaultEval environment guardEval bodyEval value index arms events result) :
    ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value index arms =
      ⟨events, result⟩ := by
  induction path with
  | nil => rfl
  | error tested => rw [ScopedCaseEvaluation.runArms, tested.observation]; rfl
  | miss tested later ih =>
      rw [ScopedCaseEvaluation.runArms, tested.observation]
      simp only [Logged.bind_ok, Logged.prepend, ih, List.singleton_append]
  | selected tested =>
      rw [ScopedCaseEvaluation.runArms, tested.observation]
      simp only [Logged.bind_ok]
      cases observed : (bodyEval _ _).result <;>
        simp [Logged.bind, observed, Logged.prepend, Logged.ofResult, Except.map]

theorem runPath_actual (value : Value F) (index : Nat) (arms : List (Arm F D G B)) :
    RunPath floatCheck defaultEval environment guardEval bodyEval value index arms
      (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value index arms).trace
      (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value index arms).result := by
  induction arms generalizing index with
  | nil => exact .nil
  | cons arm rest ih =>
      have tested := testPath_actual floatCheck defaultEval environment guardEval index arm value
      cases observed : (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value).result with
      | error error =>
          rw [observed] at tested
          have path : RunPath floatCheck defaultEval environment guardEval bodyEval value index (arm :: rest) _ _ :=
            .error tested
          rw [path.observation]
          exact path
      | ok option =>
          rw [observed] at tested
          cases option with
          | none =>
              have path : RunPath floatCheck defaultEval environment guardEval bodyEval value index (arm :: rest) _ _ :=
                .miss tested (ih (index + 1))
              rw [path.observation]
              exact path
          | some bindings =>
              have path : RunPath floatCheck defaultEval environment guardEval bodyEval value index (arm :: rest) _ _ :=
                .selected tested
              rw [path.observation]
              exact path

/-- All finite arms, arbitrary callbacks, incoming environment/subject/index,
and arbitrary requested trace/result. The path stops at the first error or
selected body, and later arms do not occur in it. -/
theorem runArms_exact (value : Value F) (index : Nat) (arms : List (Arm F D G B))
    (events : List (Event E)) (result : Except R (Option (Value F))) :
    ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value index arms =
        ⟨events, result⟩ ↔
      RunPath floatCheck defaultEval environment guardEval bodyEval value index arms events result := by
  constructor
  · intro equal
    have actual := runPath_actual floatCheck defaultEval environment guardEval bodyEval value index arms
    rw [equal] at actual
    exact actual
  · intro path; exact path.observation

inductive AllMiss (value : Value F) : Nat → List (Arm F D G B) → Prop where
  | nil : AllMiss value index []
  | cons (tested : TestPath floatCheck defaultEval environment guardEval index arm value events (.ok none))
      (later : AllMiss value (index + 1) rest) : AllMiss value index (arm :: rest)

theorem RunPath.allMiss
    (path : RunPath floatCheck defaultEval environment guardEval bodyEval value index arms events result)
    (unmatched : result = .ok none) : AllMiss floatCheck defaultEval environment guardEval value index arms := by
  induction path with
  | nil => exact .nil
  | error => cases unmatched
  | miss tested later ih => exact .cons tested (ih unmatched)
  | selected tested =>
      rename_i chosenIndex arm trace bindings rest
      cases observed : (bodyEval arm.body bindings).result <;> simp [observed, Except.map] at unmatched

theorem AllMiss.path (misses : AllMiss floatCheck defaultEval environment guardEval value index arms) :
    ∃ events, RunPath floatCheck defaultEval environment guardEval bodyEval value index arms events (.ok none) := by
  induction misses with
  | nil => exact ⟨[], .nil⟩
  | cons tested later ih =>
      obtain ⟨events, path⟩ := ih
      exact ⟨_, .miss tested path⟩

/-- Failure to select is equivalent to every tested arm missing in written
order. A default/guard/body error cannot be mistaken for an unmatched case. -/
theorem runArms_unmatched_exact (value : Value F) (index : Nat) (arms : List (Arm F D G B)) :
    (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value index arms).result = .ok none ↔
      AllMiss floatCheck defaultEval environment guardEval value index arms := by
  constructor
  · intro unmatched
    exact RunPath.allMiss floatCheck defaultEval environment guardEval bodyEval
      (runPath_actual floatCheck defaultEval environment guardEval bodyEval value index arms) unmatched
  · intro misses
    obtain ⟨events, path⟩ := AllMiss.path floatCheck defaultEval environment guardEval bodyEval misses
    rw [path.observation]

inductive EvalPath (scrutinee : Logged (Event E) R (Value F)) (arms : List (Arm F D G B)) :
    List (Event E) → Except R (Option (Value F)) → Prop where
  | error (failed : scrutinee.result = .error error) :
      EvalPath scrutinee arms (.scrutinee :: scrutinee.trace) (.error error)
  | value (evaluated : scrutinee.result = .ok value)
      (path : RunPath floatCheck defaultEval environment guardEval bodyEval value 0 arms events result) :
      EvalPath scrutinee arms (.scrutinee :: (scrutinee.trace ++ events)) result

theorem EvalPath.observation
    (path : EvalPath floatCheck defaultEval environment guardEval bodyEval scrutinee arms events result) :
    ScopedCaseEvaluation.eval floatCheck defaultEval environment guardEval bodyEval scrutinee arms = ⟨events, result⟩ := by
  cases path with
  | error failed => simp [ScopedCaseEvaluation.eval, Logged.bind, failed, Logged.prepend]
  | value evaluated run =>
      simp [ScopedCaseEvaluation.eval, Logged.bind, evaluated, run.observation, Logged.prepend]

theorem evalPath_actual (scrutinee : Logged (Event E) R (Value F)) (arms : List (Arm F D G B)) :
    EvalPath floatCheck defaultEval environment guardEval bodyEval scrutinee arms
      (ScopedCaseEvaluation.eval floatCheck defaultEval environment guardEval bodyEval scrutinee arms).trace
      (ScopedCaseEvaluation.eval floatCheck defaultEval environment guardEval bodyEval scrutinee arms).result := by
  cases observed : scrutinee.result with
  | error error =>
      have path : EvalPath floatCheck defaultEval environment guardEval bodyEval scrutinee arms _ _ := .error observed
      rw [path.observation]
      exact path
  | ok value =>
      have path : EvalPath floatCheck defaultEval environment guardEval bodyEval scrutinee arms _ _ :=
        .value observed (runPath_actual floatCheck defaultEval environment guardEval bodyEval value 0 arms)
      rw [path.observation]
      exact path

/-- The subject is evaluated once, before any arm. All callback errors and
all observations before the first stopping point are retained literally. -/
theorem eval_exact (scrutinee : Logged (Event E) R (Value F)) (arms : List (Arm F D G B))
    (events : List (Event E)) (result : Except R (Option (Value F))) :
    ScopedCaseEvaluation.eval floatCheck defaultEval environment guardEval bodyEval scrutinee arms = ⟨events, result⟩ ↔
      EvalPath floatCheck defaultEval environment guardEval bodyEval scrutinee arms events result := by
  constructor
  · intro equal
    have actual := evalPath_actual floatCheck defaultEval environment guardEval bodyEval scrutinee arms
    rw [equal] at actual
    exact actual
  · intro path; exact path.observation

end Yulang.CommonCaseOrderedPaths
