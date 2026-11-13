import Yulang.GeneralNominalSharedExamples

/-! The source Len fixture has no output obligations or children. Its packet is
already semantically committed, so generation/coherence alone do not give a
novel installation. This is not a failure of its source readiness. -/
namespace Yulang.GeneralDictionarySharedLenCommitted
open GeneralNominalSaturationState GeneralNominalSharedExamples
open GeneralNominalRecursiveExamples
open GeneralNominalUnaryCaptureFacts
open GeneralNominalMixedExamples (context state descriptor)
open GeneralDeclarationExamples (roles)

theorem children : lenPacket.children = [] := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    len,GeneralDeclarationDemands.emitAll]

theorem source_holds (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) : lenPacket.Holds model := by
  have pair := private_models context lenRegistry lenRoot len 1 descriptor rfl 0 rfl (0,0) rfl
    (by
      simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
        GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralNominalInspection.translate,GeneralNominalExamples.interpretation])
    model valid
  refine ⟨pair.1,pair.2,?_⟩
  change GeneralNominalMaterialization.Models _ _ _ _ (GeneralNominalPacketSupport.namedSchema lenPacket) model
  have empty : GeneralNominalPacketSupport.namedSchema lenPacket = {} := len_schema
  rw [empty]
  exact GeneralNominalMaterialization.empty_models ..

theorem committed : GeneralNominalFeedbackSteps.Committed
    (GeneralNominalSupport.initial context lenRoot).current lenPacket := by
  refine ⟨fun model valid => source_holds model valid.1,?_⟩
  intro child member
  rw [children] at member
  cases member

theorem no_novel : ¬ (¬ GeneralNominalFeedbackSteps.Committed
    (GeneralNominalSupport.initial context lenRoot).current lenPacket) := fun denied => denied committed

end Yulang.GeneralDictionarySharedLenCommitted
