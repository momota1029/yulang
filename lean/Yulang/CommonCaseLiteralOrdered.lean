import Yulang.CommonCaseLiteralCoverage
import Yulang.CommonCaseIntegerOrdered

/-! Every Common literal base reaches the original first-match evaluator.
Pure concrete source data discharges callback safety internally; no selected
arm or successful matcher is an assumption of these progress results. -/

namespace Yulang.CommonCaseLiteralOrdered

open CaseValues EvaluationTrace
open CaseEvaluation (Arm Event ResultHolds)

theorem covered_not_unmatched (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged (Event E) R (Value Empty)) (environment : Bindings Empty)
    (guardEval : G → Bindings Empty → Logged (Event E) R Bool)
    (bodyEval : B → Bindings Empty → Logged (Event E) R (Value Empty))
    (base : Inference.Base) (arms : List (Arm Empty D G B))
    (coverage : CommonCaseLiteralCoverage.checkBase base arms = true)
    (actual : LiteralValues.Literal Empty) (actualBase : Core.CommonData.literalBase actual = base) (index : Nat) :
    (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval (.literal actual) index arms).result ≠ .ok none := by
  intro unmatched
  have misses := (CommonCaseOrderedPaths.runArms_unmatched_exact floatCheck defaultEval environment guardEval bodyEval
    (.literal actual) index arms).mp unmatched
  obtain ⟨arm, member, unguarded, bindings, matched⟩ :=
    (CommonCaseLiteralCoverage.checkBase_matches_exact floatCheck defaultEval environment base arms).mp coverage actual actualBase
  exact CommonCaseIntegerOrdered.allMiss_no_unguarded_match floatCheck defaultEval environment guardEval
    misses arm member unguarded bindings matched

open Core
open PresenceGeneration (Comp)
open CommonPatternDataSafety (EnvironmentHolds)
open CommonPatternSourceArmGeneration (EnvironmentTyping)
open CommonPatternSourceArmsSolved (SourceArm)
open CommonPatternTyping (valueAt)

theorem literal_runArms_progress (outer : EnvironmentHolds outerNames environment actualOuter)
    (arms : List SourceArm)
    (typed : ∀ arm ∈ arms, ∃ guardRow,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body input guardRow result)
    (base : Inference.Base) (coverage : CommonCaseLiteralCoverage.checkBase base arms = true)
    (inputScalar : Common.Subtype input (.base base)) (floatCheck : Empty → Empty → Bool)
    (value : CommonData.Value) (valid : valueAt input value) (index : Nat) :
    ∃ output, (ScopedCaseEvaluation.runArms floatCheck CaseDataTerms.defaultEval actualOuter
      (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) value index arms).result = .ok (some output) ∧
      valueAt result.1 output := by
  have safe := CommonPatternConcreteCaseTotal.actual_runArms_safe outer arms typed floatCheck value valid index
  obtain ⟨literal, rfl, scalar⟩ := CommonPatternLookup.literal_of_base valid base inputScalar
  have selected := covered_not_unmatched floatCheck CaseDataTerms.defaultEval actualOuter
    (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) base arms coverage literal scalar index
  cases observed : (ScopedCaseEvaluation.runArms floatCheck CaseDataTerms.defaultEval actualOuter
    (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) (.literal literal) index arms).result with
  | error => rw [observed] at safe; cases safe
  | ok option =>
      cases option with
      | none => exact False.elim (selected observed)
      | some output => exact ⟨output, rfl, by simpa only [observed, ResultHolds] using safe⟩

theorem literal_program_progress (outer : EnvironmentHolds outerNames environment actualOuter)
    (program : CaseDataProgram.Program Empty) (subject : Comp Common.model)
    (subjectTyped : CommonSyntax.Typing Common.model environment (Data.embed outerNames program.scrutinee) subject)
    (typed : ∀ arm ∈ program.arms, ∃ guardRow,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body subject.1 guardRow result)
    (base : Inference.Base) (coverage : CommonCaseLiteralCoverage.checkBase base program.arms = true)
    (inputScalar : Common.Subtype subject.1 (.base base)) (floatCheck : Empty → Empty → Bool) :
    ∃ output, (ScopedCaseDataProgram.eval floatCheck actualOuter program).result = .ok (some output) ∧ valueAt result.1 output := by
  obtain ⟨value, evaluated, safe⟩ := CommonPatternDataSafety.typing_evaluates program.scrutinee outerNames environment
    actualOuter subject outer subjectTyped
  have valueTyped := CommonPatternLookup.typing_change_result safe (Comp.pure Common.model subject.1) (Common.subtype_refl _)
  obtain ⟨output, selected, outputType⟩ := literal_runArms_progress outer program.arms typed base coverage inputScalar
    floatCheck value valueTyped 0
  exact ⟨output, by simpa only [ScopedCaseDataProgram.eval, ScopedCaseEvaluation.eval, Logged.prepend_result,
    Logged.bind_result, evaluated, Except.bind] using selected, outputType⟩

end Yulang.CommonCaseLiteralOrdered
