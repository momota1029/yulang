import Yulang.GeneralNominalReportSourceTransport
import Yulang.GeneralDictionarySharedCapturedFinalProducer

/-! The generic relocation bridge applies to the actual scalar-refreshed
producer. Inspection equality is proved from both computed reports, not assumed. -/
namespace Yulang.GeneralDictionarySharedCapturedReportTransport
open GeneralDictionarySharedCapturedProducer GeneralDictionarySharedCapturedFinalProducer
open GeneralDictionaryCapturedScalarRefresh
open GeneralNominalReportSourceTransport

 theorem exact_relocation :
    GeneralNominalPacketSupport.report finalPacket =
      moveReport (before := candidate.context.state) (after := scalarState) (fun slot => slot)
        (GeneralNominalPacketSupport.report candidate) := by
  rw [GeneralDictionarySharedCapturedFinalProducer.report_exact,
    GeneralDictionarySharedCapturedProducer.report_exact]
  rfl

 theorem projections_equivalent (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalRecursiveInspection.ProjectionModels scalarState
      (GeneralNominalPacketSupport.report finalPacket) model ↔
    GeneralNominalRecursiveInspection.ProjectionModels candidate.context.state
      (GeneralNominalPacketSupport.report candidate) model := by
  rw [exact_relocation]
  exact projections_iff (before := candidate.context.state) (after := scalarState) (fun slot => slot) (fun _ => rfl) _ _
end Yulang.GeneralDictionarySharedCapturedReportTransport
