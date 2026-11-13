import Yulang.GeneralDictionarySharedCapturedFinalProducer
import Yulang.GeneralDictionarySharedMetadata

/-! Producer evidence is re-established in the observed scalar context, rather
than identified with the stored packet context.  The journal supplies the old
branch obligations; exact reports and unchanged source names transport them. -/
namespace Yulang.GeneralDictionarySharedCapturedFinalEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalCommonBridge
open GeneralDictionarySharedOutputBinderScope GeneralDictionarySharedCapturedTargets
open GeneralDictionarySharedCapturedProducer GeneralDictionarySharedCapturedProducerResolution
open GeneralDictionarySharedCapturedResumption GeneralDictionaryCapturedScalarRefresh
open GeneralDictionarySharedCapturedFinalProducer
open GeneralDeclarationExamples (roles)

 theorem old_branch (assignment : Assignment) (valid : Models observed.current assignment) :
    candidate.Holds assignment := by
  exact valid.2.1 candidate producer_recorded

 theorem packet_seed (p : Packet roles) : p.privateContext.state.seed = p.context.state.seed := by
  rfl

 theorem seed_preserved : before.state.seed = GeneralDictionarySharedCapturedInstallation.after.current.context.state.seed := by
  exact packet_seed candidate

 theorem constructors_preserved : before.state.constructors = GeneralDeclarationExamples.constructors := by
  rfl

 theorem interpretation_preserved : before.interpretation = GeneralNominalExamples.interpretation := by
  rfl

 theorem ordinary (assignment : Assignment) (valid : Models observed.current assignment) :
    GeneralNominalPacketSupport.Ordinary finalPacket assignment := by
  have old := ((GeneralNominalPacketSupport.private_exact candidate assignment).mp
    (old_branch assignment valid).1).2
  unfold GeneralNominalPacketSupport.Ordinary at old ⊢
  rw [GeneralDictionarySharedCapturedProducer.candidate_bindings,
    GeneralDictionarySharedCapturedProducer.report_exact] at old
  rw [repeated_bindings,GeneralDictionarySharedCapturedFinalProducer.report_exact]
  simpa [GeneralNominalAllocation.merges,GeneralNominalAllocation.capture,GeneralNominalAllocation.source,GeneralNominalRecursiveInspection.selfChecks, GeneralNominalRecursiveCandidates.privateState, GeneralNominalAllocation.propagate, GeneralNominalState.extend,seed_preserved] using old

 theorem projections (assignment : Assignment) (valid : Models observed.current assignment) :
    GeneralNominalRecursiveInspection.ProjectionModels scalarState
      (GeneralNominalPacketSupport.report finalPacket) assignment := by
  have old := (old_branch assignment valid).2.1
  change GeneralNominalRecursiveInspection.ProjectionModels _
    (GeneralNominalPacketSupport.report candidate) assignment at old
  rw [GeneralDictionarySharedCapturedProducer.report_exact] at old
  rw [GeneralDictionarySharedCapturedFinalProducer.report_exact]
  simpa [GeneralNominalRecursiveInspection.ProjectionModels,GeneralNominalRecursiveInspection.Fits] using old

 theorem schema_exact : GeneralNominalPacketSupport.namedSchema finalPacket =
    { tests := [(.source target,.scalar .int)] } := by
  have canon : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by
    change {declaration with requirements := GeneralCanonicalChildOrder.canonicalRequirements []} = declaration
    simp [GeneralCanonicalChildOrder.canonicalRequirements]
  unfold GeneralNominalPacketSupport.namedSchema GeneralNominalRecursiveCandidates.generated
    GeneralNominalMaterialization.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canon]
  simp [declaration,GeneralDictionaryRecursiveObstruction.declaration,
    GeneralNominalMaterialization.rootRequests,GeneralDictionaryRecursiveObstruction.equation,
    producer_output,GeneralDeclarationDemands.emitAll,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
    GeneralDeclarationPatterns.normalize,GeneralNominalSharedEmission.childSite,
    GeneralDeclarationPatterns.normalizeArgs,constructors_preserved,interpretation_preserved]


 theorem outputs (assignment : Assignment) (valid : Models observed.current assignment) :
    GeneralNominalPacketSupport.Outputs finalPacket assignment := by
  have old := (old_branch assignment valid).2.2
  change GeneralNominalPacketSupport.Outputs candidate assignment at old
  unfold GeneralNominalPacketSupport.Outputs GeneralNominalPacketSupport.capture at old ⊢
  rw [GeneralDictionarySharedCapturedProducer.candidate_bindings,
    GeneralDictionarySharedCapturedProducer.report_exact,
    GeneralDictionarySharedCapturedProducer.schema_exact] at old
  rw [repeated_bindings,GeneralDictionarySharedCapturedFinalProducer.report_exact,schema_exact]
  simpa [GeneralNominalMaterialization.Models] using old

 theorem branch_models (assignment : Assignment) (valid : Models observed.current assignment) :
    finalPacket.Holds assignment := by
  refine ⟨(GeneralNominalPacketSupport.private_exact finalPacket assignment).mpr
    ⟨valid.1,ordinary assignment valid⟩,projections assignment valid,outputs assignment valid⟩
end Yulang.GeneralDictionarySharedCapturedFinalEvidence
