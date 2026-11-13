import Yulang.GeneralDictionarySharedCapturedFinalEvidence

/-! The terminal captured producer has source evidence in every model of the
actual post-scalar-refresh journal. No scalar-refresh/ordinary-extension
identification and no desired evidence premise is used. -/
namespace Yulang.GeneralDictionarySharedCapturedFinalCurrentEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalCommonBridge
open GeneralDictionarySharedOutputBinderScope GeneralDictionarySharedCapturedTargets
open GeneralDictionarySharedCapturedProducer GeneralDictionarySharedCapturedProducerResolution
open GeneralDictionarySharedCapturedResumption GeneralDictionaryCapturedScalarRefresh
open GeneralDictionarySharedCapturedFinalProducer GeneralDictionarySharedCapturedFinalEvidence
open GeneralDictionarySharedCapturedModel
open GeneralDeclarationExamples (roles)

 theorem bounds : GeneralNominalRecursiveCandidates.arguments scalarContext producer = some [(3,4)] := by
  have left := (GeneralDictionaryBinderLocations.sourceSlot_exact scalarBase lo (3 : Fin 5)).mpr rfl
  have right := (GeneralDictionaryBinderLocations.sourceSlot_exact scalarBase hi (4 : Fin 5)).mpr rfl
  have args : List.ofFn producer.demand.arguments = [(lo,hi)] := by
    rw [show producer.demand.arguments = fun _ => (lo,hi) from
      funext GeneralDictionarySharedCapturedInstallation.producer_inputs]
    rfl
  change GeneralCandidateBoundaryParts.locate scalarBase (List.ofFn producer.demand.arguments) = _
  rw [args]
  simp [GeneralCandidateBoundaryParts.locate,left,right,Option.bind]

 theorem terminal : finalPacket.children = [] := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements]
  change (GeneralDeclarationDemands.emitAll producer.identity
    {declaration with requirements := [].mergeSort (fun a b => decide (a.id ≤ b.id))} _ _ _).map _ = []
  simp only [List.mergeSort_nil]
  rfl

 theorem request_ready : GeneralNominalRecursiveCandidates.RequestReady registry scalarContext producer declaration
    GeneralDictionaryRecursiveObstruction.declaration_checked [(3,4)] := by
  refine ⟨?_,?_⟩
  · intro output h
    rw [producer_output] at h
    cases List.mem_singleton.mp h
    exact ⟨GeneralDictionaryRecursiveObstruction.equation,by simp,rfl⟩
  · change (GeneralNominalPacketSupport.namedSchema finalPacket).unknown = false
    rw [GeneralDictionarySharedCapturedFinalEvidence.schema_exact]

 theorem current_instance (assignment : Assignment) (valid : Models observed.current assignment) :
    GeneralDictionaryRecursiveEvidence.Instance registry observed.current.context assignment producer declaration.id [] := by
  change GeneralDictionaryRecursiveEvidence.Instance registry scalarContext assignment producer declaration.id []
  refine ⟨declaration,by simp,GeneralDictionaryRecursiveObstruction.declaration_checked,
    rfl,rfl,[(3,4)],bounds,finished,request_ready,?_,
    GeneralDictionarySharedMetadata.formed_metadata observed_formed,branch_models assignment valid⟩
  exact terminal.symm

 theorem current_evidence (assignment : Assignment) (valid : Models observed.current assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence registry observed.current.context assignment producer
      (.node declaration.id []) :=
  GeneralDictionaryRecursiveEvidence.evidence_node _ _ _ _ _ _ _
    (current_instance assignment valid) .nil

 theorem concrete_evidence : GeneralDictionaryRecursiveEvidence.Evidence registry observed.current.context
    GeneralDictionarySharedCapturedModel.model producer (.node declaration.id []) :=
  current_evidence _ GeneralDictionarySharedCapturedResumption.inhabited
end Yulang.GeneralDictionarySharedCapturedFinalCurrentEvidence
