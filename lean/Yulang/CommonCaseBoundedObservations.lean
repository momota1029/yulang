import Yulang.CommonPatternObservationBounds
import Yulang.CommonPatternSourceCasePartial

/-! Arbitrary ordered arms compose partial value safety and declared error /
trace bounds. Leaf contracts are explicit and allow errors. Coverage and the
translation of unmatched results into a source failure effect remain separate. -/

namespace Yulang.CommonCaseBoundedObservations

open Core.CommonData (Value)
open CommonPatternEnvironment (NamedTypes)
open CommonPatternTyping (valueAt bindingTypes)
open CommonPatternPartialSafety (PartialHolds)
open CommonPatternSourceCasePartial (PartialResult)
open CommonPatternObservationBounds
open CommonCaseEffectPaths (observationRow eventRow traceRow resultRow)
open CaseValues (Bindings BindingsHold)
open CaseEvaluation (Arm Event)
open EvaluationTrace (Logged)

theorem marker_observation (source : E → Common.Row) (failure : R → Common.Row)
    (marker : Event E) (empty : eventRow source marker = Common.rowEmpty)
    (observed : Logged (Event E) R A) :
    observationRow source failure (observed.prepend [marker]) = observationRow source failure observed := by
  funext occurrence
  simp [Logged.prepend, observationRow, traceRow, empty, Common.rowJoin, Common.rowEmpty]

inductive ArmTyping (DefaultTyped : NamedTypes → D → Common.Ty → Prop)
    (GuardTyped : G → NamedTypes → Prop) (BodyTyped : B → NamedTypes → Common.Ty → Prop)
    (types : NamedTypes) (arm : Arm Empty D G B) (input target : Common.Ty) : Prop where
  | arm {bindings : NamedTypes} :
      CommonAlignedPatternTyping.Typing DefaultTyped types arm.pattern input bindings →
      (∀ code, arm.guard = some code → GuardTyped code bindings) →
      BodyTyped arm.body bindings target → ArmTyping DefaultTyped GuardTyped BodyTyped types arm input target

def GuardObservationSound (source : E → Common.Row) (failure : R → Common.Row) (cap : Common.Row)
    (GuardTyped : G → NamedTypes → Prop) (evaluate : G → Bindings Empty → Logged (Event E) R Bool) : Prop :=
  ∀ code types, GuardTyped code types → ∀ actual, BindingsHold (bindingTypes types) actual →
    Common.rowLe (observationRow source failure (evaluate code actual)) cap

def BodyObservationSound (source : E → Common.Row) (failure : R → Common.Row) (cap : Common.Row)
    (BodyTyped : B → NamedTypes → Common.Ty → Prop)
    (evaluate : B → Bindings Empty → Logged (Event E) R Value) : Prop :=
  ∀ code types target, BodyTyped code types target → ∀ actual, BindingsHold (bindingTypes types) actual →
    (∀ value, (evaluate code actual).result = .ok value → valueAt target value) ∧
      Common.rowLe (observationRow source failure (evaluate code actual)) cap

theorem testArm_partial (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged (Event E) R Value)
    (defaults : CommonPatternPartialSafety.DefaultPartialSound DefaultTyped defaultEval)
    (environment : Bindings Empty) (valid : BindingsHold (bindingTypes types) environment)
    (guardEval : G → Bindings Empty → Logged (Event E) R Bool) (index : Nat) (arm : Arm Empty D G B)
    (typed : CommonAlignedPatternTyping.Typing DefaultTyped types arm.pattern input bindings)
    (value : Value) (within : valueAt input value) :
    PartialHolds bindings
      (CommonAlignedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value).result := by
  have safe := CommonAlignedPatternPartialSafety.typing_matches_partial floatCheck defaultEval defaults
    typed.2 typed.1 environment valid value within
  simp only [CommonAlignedCaseEvaluation.testArm, Logged.bind_result]
  cases observed : (CommonPatternAlignedMatcher.run floatCheck defaultEval environment arm.pattern value).result with
  | error => trivial
  | ok option =>
      rw [observed] at safe
      cases option with
      | none => trivial
      | some matched =>
          cases guard : arm.guard with
          | none => exact safe
          | some code =>
              simp only [Except.bind, Logged.prepend_result, Logged.bind_result]
              cases returned : (guardEval code matched).result with
              | error => trivial
              | ok accepted => cases accepted <;> first | trivial | exact safe

theorem testArm_bound (source : E → Common.Row) (failure : R → Common.Row) (cap : Common.Row)
    (floatCheck : Empty → Empty → Bool) (defaultEval : Bindings Empty → D → Logged (Event E) R Value)
    (defaults : DefaultObservationSound source failure cap DefaultTyped defaultEval)
    (environment : Bindings Empty) (valid : BindingsHold (bindingTypes types) environment)
    (guardEval : G → Bindings Empty → Logged (Event E) R Bool)
    (guards : GuardObservationSound source failure cap GuardTyped guardEval)
    (index : Nat) (arm : Arm Empty D G B)
    (typed : CommonAlignedPatternTyping.Typing DefaultTyped types arm.pattern input bindings)
    (guardTyped : ∀ code, arm.guard = some code → GuardTyped code bindings)
    (value : Value) (within : valueAt input value) :
    Common.rowLe (observationRow source failure
      (CommonAlignedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value)) cap := by
  have safe := CommonAlignedPatternPartialSafety.typing_matches_partial floatCheck defaultEval defaults.1
    typed.2 typed.1 environment valid value within
  apply bind_bound source failure _ _ cap
    (typing_observation_bound source failure cap floatCheck defaultEval defaults typed.2 typed.1 environment valid value within)
  intro option observed
  cases option with
  | none => exact pure_bound source failure none cap
  | some matched =>
      have matching : BindingsHold (bindingTypes bindings) matched := by simpa only [observed, PartialHolds] using safe
      cases guard : arm.guard with
      | none => exact pure_bound source failure (some matched) cap
      | some code =>
          rw [marker_observation source failure (.guard index) rfl]
          apply bind_bound source failure _ _ cap (guards code bindings (guardTyped code guard) matched matching)
          intro accepted returned
          cases accepted <;> exact pure_bound source failure _ cap

theorem runArms_partial_and_bound (source : E → Common.Row) (failure : R → Common.Row) (cap : Common.Row)
    (floatCheck : Empty → Empty → Bool) (defaultEval : Bindings Empty → D → Logged (Event E) R Value)
    (defaults : DefaultObservationSound source failure cap DefaultTyped defaultEval)
    (environment : Bindings Empty) (valid : BindingsHold (bindingTypes types) environment)
    (guardEval : G → Bindings Empty → Logged (Event E) R Bool)
    (guards : GuardObservationSound source failure cap GuardTyped guardEval)
    (bodyEval : B → Bindings Empty → Logged (Event E) R Value)
    (bodies : BodyObservationSound source failure cap BodyTyped bodyEval)
    (arms : List (Arm Empty D G B))
    (typed : ∀ arm ∈ arms, ArmTyping DefaultTyped GuardTyped BodyTyped types arm input target)
    (value : Value) (within : valueAt input value) (index : Nat) :
    PartialResult target (CommonAlignedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value index arms).result ∧
      Common.rowLe (observationRow source failure
        (CommonAlignedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value index arms)) cap := by
  induction arms generalizing index with
  | nil => exact ⟨True.intro, pure_bound source failure none cap⟩
  | cons arm rest ih =>
      cases typed arm List.mem_cons_self with
      | arm patternTyped guardTyped bodyTyped =>
          rename_i bindings
          have safe := testArm_partial floatCheck defaultEval defaults.1 environment valid guardEval index arm patternTyped value within
          have later := ih (fun arm member => typed arm (List.mem_cons_of_mem _ member)) (index + 1)
          constructor
          · simp only [CommonAlignedCaseEvaluation.runArms, Logged.prepend_result, Logged.bind_result]
            cases observed : (CommonAlignedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value).result with
            | error => trivial
            | ok option =>
                rw [observed] at safe
                cases option with
                | none => exact later.1
                | some matched =>
                    have bodySafe := (bodies arm.body _ target bodyTyped matched safe).1
                    simp only [Except.bind, Logged.prepend_result, Logged.bind_result]
                    cases returned : (bodyEval arm.body matched).result with
                    | error => trivial
                    | ok output => exact bodySafe output returned
          · simp only [CommonAlignedCaseEvaluation.runArms]
            rw [marker_observation source failure (.arm index) rfl]
            apply bind_bound source failure _ _ cap
              (testArm_bound source failure cap floatCheck defaultEval defaults environment valid guardEval guards index arm
                patternTyped guardTyped value within)
            intro option observed
            cases option with
            | none => exact later.2
            | some matched =>
                have matching : BindingsHold (bindingTypes bindings) matched := by simpa only [observed, PartialHolds] using safe
                rw [marker_observation source failure (.body index) rfl]
                apply bind_bound source failure _ _ cap (bodies arm.body _ target bodyTyped matched matching).2
                intro result returned
                exact pure_bound source failure (some result) cap

theorem actual_runArms_partial_and_bound (source : E → Common.Row) (failure : R → Common.Row) (cap : Common.Row)
    (floatCheck : Empty → Empty → Bool) (defaultEval : Bindings Empty → D → Logged (Event E) R Value)
    (defaults : DefaultObservationSound source failure cap DefaultTyped defaultEval)
    (defaultNames : CommonPatternAlignedMatcher.DefaultInvariant defaultEval)
    (environment : Bindings Empty) (valid : BindingsHold (bindingTypes types) environment)
    (guardEval : G → Bindings Empty → Logged (Event E) R Bool)
    (guards : GuardObservationSound source failure cap GuardTyped guardEval)
    (guardNames : CommonAlignedCaseEvaluation.NamedInvariant guardEval)
    (bodyEval : B → Bindings Empty → Logged (Event E) R Value)
    (bodies : BodyObservationSound source failure cap BodyTyped bodyEval)
    (bodyNames : CommonAlignedCaseEvaluation.NamedInvariant bodyEval)
    (arms : List (Arm Empty D G B))
    (typed : ∀ arm ∈ arms, ArmTyping DefaultTyped GuardTyped BodyTyped types arm input target)
    (value : Value) (within : valueAt input value) (index : Nat) :
    PartialResult target (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value index arms).result ∧
      Common.rowLe (observationRow source failure
        (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value index arms)) cap := by
  have sourceValid : ∀ arm ∈ arms, PatternBindingChecks.NamesValid arm.pattern := by
    intro arm member
    cases typed arm member with | arm patternTyped guardTyped bodyTyped => exact patternTyped.1
  rw [← CommonAlignedCaseEvaluation.runArms_eq floatCheck defaultEval defaultNames environment environment
    (fun _ => rfl) guardEval guardNames bodyEval bodyNames value index arms sourceValid]
  exact runArms_partial_and_bound source failure cap floatCheck defaultEval defaults environment valid guardEval guards bodyEval bodies
    arms typed value within index

/-- The subject is observed once, before the ordered arms. A subject error
retains its trace/error row and invokes no arm. All contracts remain partial. -/
theorem eval_partial_and_bound (source : E → Common.Row) (failure : R → Common.Row) (cap : Common.Row)
    (floatCheck : Empty → Empty → Bool) (defaultEval : Bindings Empty → D → Logged (Event E) R Value)
    (defaults : DefaultObservationSound source failure cap DefaultTyped defaultEval)
    (environment : Bindings Empty) (valid : BindingsHold (bindingTypes types) environment)
    (guardEval : G → Bindings Empty → Logged (Event E) R Bool)
    (guards : GuardObservationSound source failure cap GuardTyped guardEval)
    (bodyEval : B → Bindings Empty → Logged (Event E) R Value)
    (bodies : BodyObservationSound source failure cap BodyTyped bodyEval)
    (arms : List (Arm Empty D G B))
    (typed : ∀ arm ∈ arms, ArmTyping DefaultTyped GuardTyped BodyTyped types arm input target)
    (subject : Logged (Event E) R Value)
    (subjectTyped : ∀ value, subject.result = .ok value → valueAt input value)
    (subjectBound : Common.rowLe (observationRow source failure subject) cap) :
    PartialResult target (CommonAlignedCaseEvaluation.eval floatCheck defaultEval environment guardEval bodyEval subject arms).result ∧
      Common.rowLe (observationRow source failure
        (CommonAlignedCaseEvaluation.eval floatCheck defaultEval environment guardEval bodyEval subject arms)) cap := by
  have run (value : Value) (evaluated : subject.result = .ok value) :=
    runArms_partial_and_bound source failure cap floatCheck defaultEval defaults environment valid guardEval guards bodyEval bodies
      arms typed value (subjectTyped value evaluated) 0
  constructor
  · simp only [CommonAlignedCaseEvaluation.eval, Logged.prepend_result, Logged.bind_result]
    cases evaluated : subject.result with
    | error => trivial
    | ok value => exact (run value evaluated).1
  · simp only [CommonAlignedCaseEvaluation.eval]
    rw [marker_observation source failure .scrutinee rfl]
    exact bind_bound source failure _ _ cap subjectBound (fun value evaluated => (run value evaluated).2)

end Yulang.CommonCaseBoundedObservations
