import Yulang.GeneralDictionarySource168Transport
import Yulang.GeneralDictionarySharedCapturedReportTransport
import Yulang.GeneralDictionarySharedCapturedFinalCurrentEvidence

namespace Yulang.GeneralDictionarySource168Transport
open GeneralDictionarySharedCapturedProducer GeneralDictionarySharedCapturedFinalProducer
open GeneralDictionaryCapturedScalarRefresh GeneralDictionarySharedCapturedFinalEvidence
open GeneralDictionarySharedCapturedResumption

theorem actual_schemas : GeneralNominalPacketSupport.namedSchema finalPacket =
    GeneralNominalPacketSupport.namedSchema candidate := by
  rw [GeneralDictionarySharedCapturedFinalEvidence.schema_exact,GeneralDictionarySharedCapturedProducer.schema_exact]

theorem actual_sources (slot : Fin candidate.context.state.base.slots) :
    finalPacket.context.state.base.source slot = candidate.context.state.base.source slot := rfl

theorem actual_seed : finalPacket.context.state.seed = candidate.context.state.seed :=
  GeneralDictionarySharedCapturedFinalEvidence.packet_seed candidate

set_option maxHeartbeats 5000 in
theorem actual_producer_branch (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models observed.current model) :
    finalPacket.Holds model := by
  exact branch_relocated candidate.registry candidate.context finalPacket.context
    candidate.site.occurrence candidate.declaration candidate.checked candidate.bounds finalPacket.bounds
    (fun slot => slot) actual_sources actual_seed
    GeneralDictionarySharedCapturedReportTransport.exact_relocation
    actual_schemas model valid.1 (old_branch model valid)
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedModel
open GeneralDictionarySharedCapturedFinalCurrentEvidence

theorem actual_current_evidence (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models observed.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence candidate.registry observed.current.context model
      producer (.node declaration.id []) := by
  apply GeneralDictionaryRecursiveEvidence.evidence_node candidate.registry observed.current.context model
    producer declaration.id [] []
  · change GeneralDictionaryRecursiveEvidence.Instance candidate.registry scalarContext model
      producer declaration.id []
    refine ⟨declaration,by simp,GeneralDictionaryRecursiveObstruction.declaration_checked,
      rfl,rfl,[(3,4)],GeneralDictionarySharedCapturedFinalCurrentEvidence.bounds,
      GeneralDictionarySharedCapturedFinalProducer.finished,request_ready,?_,
      GeneralDictionarySharedMetadata.formed_metadata observed_formed,actual_producer_branch model valid⟩
    exact terminal.symm
  · exact .nil
end Yulang.GeneralDictionarySource168Transport
