import Yulang.CommonCaseCoreDataPrefixSolved
import Yulang.CommonCaseCoreRecordPrefixExamples

/-! A source-gated family is nonempty. Its default and body use the original
Core literal and indexed binder. Neither a callback nor a successful-run
premise is supplied to construct the actual finite scheme instance. -/

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

end Yulang.CommonCaseCoreDataPrefixExamples
