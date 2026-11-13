import Yulang.GeneralDictionaryCapturedInstallationBlocked
import Yulang.GeneralDictionarySharedCapturedFinalCurrentEvidence
import Yulang.GeneralDictionarySharedCapturedReportTransport

/-! Nonvacuous regression: current producer evidence and the consumer's trusted
input delay coexist along the actual source-formed Shared trace. -/
namespace Yulang.GeneralDictionaryCapturedEvidenceDelay
open GeneralNominalSaturationState GeneralNominalCommonBridge
open GeneralDictionarySharedCapturedResumption GeneralDictionarySharedCapturedTargets
open GeneralDictionarySharedCapturedProducer GeneralDictionarySharedCapturedModel

theorem actual_evidence_with_trusted_delay :
    GeneralNominalSharedSteps.SourceFormed registry root observed ∧
    (∃ assignment, Models observed.current assignment) ∧
    (∀ assignment, Models observed.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry observed.current.context assignment
        producer (.node declaration.id [])) ∧
    ¬ GeneralNominalState.RootPending observed.current.context.state consumer.demand ∧
    ¬ GeneralNominalSharedSupport.ReadyAt observed 2 :=
  ⟨observed_formed,⟨model,inhabited⟩,
    GeneralDictionarySharedCapturedFinalCurrentEvidence.current_evidence,
    consumer_raw_ready,GeneralDictionaryCapturedInputCountermodel.consumer_input_not_ready⟩
end Yulang.GeneralDictionaryCapturedEvidenceDelay
