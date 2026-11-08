import Yulang.CommonCaseCoreDataPrefixSolved
import Yulang.CommonCaseCoreRecordPrefixExamples

/-! A source-gated family is nonempty and its fixed actual evaluator returns
the default through the original Core binder. Neither a callback nor a
successful-run premise is supplied. -/

namespace Yulang.CommonCaseCoreDataPrefixExamples

set_option backward.isDefEq.respectTransparency false

open Core
open CommonCaseCoreRecordPrefixExamples (subject arm assignment)
open CommonPatternPrefixNoMiss (Returns returns_bind returns_ret)

theorem source_gate : CommonCaseCoreDataGate.check subject [arm] = true := rfl

theorem real_scheme_instance :
    ∃ scheme ∈ CommonCaseCoreDataPrefixSolved.solvePremises [] subject [arm], ∃ parameters : scheme.Parameters,
      CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) assignment :=
  (CommonCaseCoreDataPrefixSolved.premises_instances_exact [] subject [arm] assignment).mp
    ⟨CommonCaseCoreRecordPrefixExamples.premises, (CommonCaseCoreDataGate.check_exact subject [arm]).mp source_gate⟩

theorem returns_logged (computation : EvaluationTrace.Logged (CaseEvaluation.Event E) R A) (value : A) :
    Returns (CommonCoreDataPrefixes.ofLogged computation) value ↔ computation.result = .ok value := by
  simp [Returns, CommonCoreDataPrefixes.completed_exact, eq_comm]

/-- The actual fixed prefix computation has a completed successful trace
returning seven. No evaluator, successful callback, or selected arm is given. -/
theorem actual_result :
    Returns (CommonCaseCoreDataPrefixSolved.run subject [arm]) (some (.literal (.int 7))) := by
  simp [CommonCaseCoreDataPrefixSolved.run, CommonCaseComputations.eval, CommonCaseComputations.runArms,
    CommonCaseComputations.testArm, CommonPatternComputations.run, CommonPatternComputations.andThen,
    CommonPatternFinitePrefixes.ops, CommonCaseFinitePrefixes.visits,
    CommonCasePrefixCoverage.returns_prepend, returns_bind, returns_ret,
    CommonCoreDataPrefixes.evaluate, returns_logged, CommonCoreDataEvaluation.eval,
    CommonCoreDataEvaluation.pure, EvaluationTrace.Logged.ofResult, EvaluationTrace.Logged.prepend,
    CommonCaseCoreBoundedGeneration.runtimeArm, subject, arm, CommonCaseCoreRecordPrefixExamples.fallback,
    CaseValues.lookup]

end Yulang.CommonCaseCoreDataPrefixExamples
