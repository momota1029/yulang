import Yulang.GeneralDictionarySharedCapturedProducerResolution
import Yulang.GeneralDictionarySharedCurrentEvidence
namespace Yulang.GeneralDictionarySharedCapturedProducerEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge GeneralDictionaryRecursiveEvidence
open GeneralDictionarySharedOutputBinderScope GeneralDictionarySharedCapturedTargets
open GeneralDictionarySharedCapturedRefresh GeneralDictionarySharedCapturedProducer
open GeneralDictionarySharedCapturedProducerResolution

theorem terminal : candidate.children = [] := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements]
  change (GeneralDeclarationDemands.emitAll producer.identity
    {declaration with requirements := [].mergeSort (fun a b => decide (a.id ≤ b.id))} _ _ _).map _ = []
  simp only [List.mergeSort_nil]
  rfl

/-- All successor models have the leaf producer dictionary at the actual
private successor context, not merely at the stored inspection context. -/
theorem current_evidence (assignment : Assignment) (valid : Models installed.current assignment) :
    Evidence registry installed.current.context assignment producer (.node declaration.id []) :=
  GeneralDictionarySharedCurrentEvidence.terminal_current_evidence candidate []
    GeneralDictionarySharedCapturedProducerEnabled.enabled terminal assignment valid
end Yulang.GeneralDictionarySharedCapturedProducerEvidence
