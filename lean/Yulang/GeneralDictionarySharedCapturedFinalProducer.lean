import Yulang.GeneralDictionarySharedCapturedResumption
import Yulang.GeneralDictionarySharedCapturedProducerEvidence
/-! Final-context inspection recovery only. This certifies that the scalar
refresh leaves the nominal producer report and repeated-capture bindings intact.
It does not transport BranchModels or Evidence across the changed context. -/
namespace Yulang.GeneralDictionarySharedCapturedFinalProducer
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDictionarySharedOutputBinderScope GeneralDictionarySharedCapturedTargets
open GeneralDictionarySharedCapturedModel GeneralDictionarySharedCapturedProducer GeneralDictionaryCapturedScalarRefresh
open GeneralDictionarySharedCapturedResumption
open GeneralDeclarationExamples (roles)

noncomputable abbrev finalPacket : Packet roles :=
  {candidate with context := scalarContext, bounds := [(3,4)]}

theorem report_exact : GeneralNominalPacketSupport.report finalPacket =
    { captures := [⟨0,(2,2),some leftOrigin⟩,⟨0,(2,2),some rightOrigin⟩],
      inspected := [(3,4)], checked := [(3,4),(3,4),(2,2),(2,2)],
      anchors := [(leftOrigin,(2,2)),(rightOrigin,(2,2))] } := by
  have queries : GeneralNominalInspection.queries scalarState scalarContext.interpretation declaration =
      [.nominal 0 [.variables [0]]] := by
    exact GeneralDictionarySharedCapturedProducer.queries
  have inner : inspectMany scalarState [.nominal 0 [.variables [0]]] [(3,4)] (fun _ => none) 0 =
    { captures := [⟨0,(2,2),some leftOrigin⟩,⟨0,(2,2),some rightOrigin⟩],
      inspected := [(3,4)], checked := [(3,4),(2,2),(2,2)],
      anchors := [(leftOrigin,(2,2)),(rightOrigin,(2,2))] } := by
    simp only [inspectMany.eq_def]
    rw [inspect.eq_def]
    change Report.append
      (Report.visit (3,4) none (.nominal 0 1)
        ((inspectMany scalarState [.variables [0]] [(2,2)]
          (fun index => some (.nominal (.source lo) 0 index)) 0).append
         (inspectMany scalarState [.variables [0]] [(2,2)]
          (fun index => some (.nominal (.source hi) 0 index)) 0))) {} = _
    simp only [inspectMany.eq_def,inspect.eq_def]
    rfl
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  rw [queries,inner]
  rfl

theorem finished : Finished (GeneralNominalPacketSupport.report finalPacket) := by
  rw [report_exact]
  exact ⟨rfl,rfl,rfl⟩

theorem repeated_bindings : finalPacket.bindings = [(0,(2,2)),(0,(2,2))] := by
  change GeneralNominalRecursiveInspection.bindings scalarState (GeneralNominalPacketSupport.report finalPacket) = _
  rw [report_exact]
  rfl

end Yulang.GeneralDictionarySharedCapturedFinalProducer
