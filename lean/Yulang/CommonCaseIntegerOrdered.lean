import Yulang.CommonCaseIntegerCoverage
import Yulang.CommonPatternConcreteCaseTotal

/-! Exact finite integer coverage reaches actual first-match execution.
Earlier guards or errors are not treated as coverage witnesses. Successful
progress below uses the separately proved concrete data error exclusion. -/

namespace Yulang.CommonCaseIntegerOrdered

open CaseValues EvaluationTrace
open CaseEvaluation (Arm Event ResultHolds)
open CommonCaseOrderedPaths (AllMiss)

theorem allMiss_no_unguarded_match (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F)) (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (misses : AllMiss floatCheck defaultEval environment guardEval value index arms) :
    ∀ arm ∈ arms, arm.guard = none → ∀ bindings,
      (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result ≠ .ok (some bindings) := by
  induction misses with
  | nil => intro arm member; cases member
  | cons tested later ih =>
      intro arm member unguarded bindings matched
      rcases List.mem_cons.mp member with same | tail
      · subst arm
        have testResult := congrArg Logged.result tested.observation
        simp [ScopedCaseEvaluation.testArm, Logged.bind_result, matched, unguarded,
          CasePatterns.success, Logged.ofResult, Except.bind] at testResult
      · exact ih arm tail unguarded bindings matched

theorem covered_not_unmatched (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F)) (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
    (arms : List (Arm F D G B)) (coverage : CommonCaseIntegerCoverage.checkInteger arms = true)
    (integer : Int) (index : Nat) :
    (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval
      (.literal (.int integer)) index arms).result ≠ .ok none := by
  intro unmatched
  have misses := (CommonCaseOrderedPaths.runArms_unmatched_exact floatCheck defaultEval environment guardEval bodyEval
    (.literal (.int integer)) index arms).mp unmatched
  obtain ⟨arm, member, unguarded, bindings, matched⟩ :=
    (CommonCaseIntegerCoverage.checkInteger_matches_exact floatCheck defaultEval environment arms).mp coverage integer
  exact allMiss_no_unguarded_match floatCheck defaultEval environment guardEval misses arm member unguarded bindings matched

open Core
open PresenceGeneration (Comp)
open CommonPatternDataSafety (EnvironmentHolds)
open CommonPatternSourceArmGeneration (EnvironmentTyping)
open CommonPatternSourceArmsSolved (SourceArm)
open CommonPatternTyping (valueAt)

/-- Every finite typed source data arm list, every typed integer subject and
arbitrary captured logical environment. Static interval coverage plus the
source typing derivations imply actual first-match selection and value
safety, without a successful matcher/callback/case premise. -/
theorem integer_runArms_progress (outer : EnvironmentHolds outerNames environment actualOuter)
    (arms : List SourceArm)
    (typed : ∀ arm ∈ arms, ∃ guardRow,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body input guardRow result)
    (coverage : CommonCaseIntegerCoverage.checkInteger arms = true)
    (inputInteger : Common.Subtype input (.base .int)) (floatCheck : Empty → Empty → Bool)
    (value : CommonData.Value) (valid : valueAt input value) (index : Nat) :
    ∃ output, (ScopedCaseEvaluation.runArms floatCheck CaseDataTerms.defaultEval actualOuter
        (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) value index arms).result = .ok (some output) ∧
      valueAt result.1 output := by
  have safe := CommonPatternConcreteCaseTotal.actual_runArms_safe outer arms typed floatCheck value valid index
  obtain ⟨literal, rfl, scalar⟩ := CommonPatternLookup.literal_of_base valid .int inputInteger
  cases literal with
  | int integer =>
      have selected := covered_not_unmatched floatCheck CaseDataTerms.defaultEval actualOuter
        (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) arms coverage integer index
      cases observed : (ScopedCaseEvaluation.runArms floatCheck CaseDataTerms.defaultEval actualOuter
          (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) (.literal (.int integer)) index arms).result with
      | error => rw [observed] at safe; cases safe
      | ok option =>
          cases option with
          | none => exact False.elim (selected observed)
          | some output => exact ⟨output, rfl, by simpa only [observed, ResultHolds] using safe⟩
  | float empty => exact empty.elim
  | str | bool | unit => cases scalar

theorem integer_program_progress (outer : EnvironmentHolds outerNames environment actualOuter)
    (program : CaseDataProgram.Program Empty) (subject : Comp Common.model)
    (subjectTyped : CommonSyntax.Typing Common.model environment (Data.embed outerNames program.scrutinee) subject)
    (typed : ∀ arm ∈ program.arms, ∃ guardRow,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body subject.1 guardRow result)
    (coverage : CommonCaseIntegerCoverage.checkInteger program.arms = true)
    (inputInteger : Common.Subtype subject.1 (.base .int)) (floatCheck : Empty → Empty → Bool) :
    ∃ output, (ScopedCaseDataProgram.eval floatCheck actualOuter program).result = .ok (some output) ∧ valueAt result.1 output := by
  obtain ⟨value, evaluated, safe⟩ := CommonPatternDataSafety.typing_evaluates program.scrutinee outerNames environment
    actualOuter subject outer subjectTyped
  have valueTyped := CommonPatternLookup.typing_change_result safe (Comp.pure Common.model subject.1) (Common.subtype_refl _)
  obtain ⟨output, selected, outputType⟩ := integer_runArms_progress outer program.arms typed coverage inputInteger
    floatCheck value valueTyped 0
  exact ⟨output, by simpa only [ScopedCaseDataProgram.eval, ScopedCaseEvaluation.eval, Logged.prepend_result,
    Logged.bind_result, evaluated, Except.bind] using selected, outputType⟩

end Yulang.CommonCaseIntegerOrdered
