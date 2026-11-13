import Yulang.GeneralDictionaryRecursive168Transport
import Yulang.GeneralDictionaryActual168Transport

/-! A concrete non-identity scalar refresh carries the same finite source tree.
The local report comparison is checked only for its selected visible key. -/
namespace Yulang.GeneralDictionaryCapturedTree168Transport
open GeneralSourceDictionaries GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursive168Transport GeneralDictionarySource168Transport
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedModel
open GeneralDictionarySharedCapturedProducer GeneralDictionarySharedCapturedFinalProducer
open GeneralDictionarySharedCapturedFinalEvidence GeneralDictionarySharedCapturedResumption
open GeneralDictionaryCapturedScalarRefresh

abbrev tree : Dictionary GeneralDeclarationExamples.roles := .node producer declaration.id []

theorem locality : RelocatesAt candidate.registry candidate.context finalPacket.context
    (fun slot => slot) producer declaration.id := by
  intro selected checked bs visible key located _finished
  have equal := GeneralDictionaryEmissionPlans.declaration_key_unique candidate.registry
    registry_checked selected declaration visible (by simp) key
  subst selected
  have equal := Option.some.inj (located.symm.trans GeneralDictionarySharedCapturedProducer.bounds)
  subst bs
  exact ⟨finalPacket.bounds,GeneralDictionarySharedCapturedFinalCurrentEvidence.bounds,
    GeneralDictionarySharedCapturedReportTransport.exact_relocation,actual_schemas⟩

theorem tree_locality : RelocatesTree candidate.registry candidate.context finalPacket.context
    (fun slot => slot) tree := by
  intro occurrence key member
  have equal : (occurrence,key) = (producer,declaration.id) := List.mem_singleton.mp member
  cases equal
  exact locality

theorem stored_instance (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models observed.current model) :
    GeneralDictionaryRecursiveEvidence.Instance candidate.registry candidate.context model
      producer declaration.id [] := by
  have preparation := GeneralDictionarySharedCapturedPreparation.prepared
  obtain ⟨metadata,_,_,bs,located,finished,ready,_⟩ := preparation
  have equal := Option.some.inj (located.symm.trans GeneralDictionarySharedCapturedProducer.bounds)
  subst bs
  exact ⟨declaration,by simp,GeneralDictionaryRecursiveObstruction.declaration_checked,rfl,rfl,
    candidate.bounds,GeneralDictionarySharedCapturedProducer.bounds,finished,ready,
    GeneralDictionarySharedCapturedProducerEvidence.terminal.symm,metadata,old_branch model valid⟩

theorem old_tree (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models observed.current model) :
    Evidence (GeneralDictionaryRecursiveEvidence.Instance candidate.registry candidate.context model) tree :=
  .node (stored_instance model valid) (by intro _ impossible; cases impossible)

theorem actual_tree (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models observed.current model) :
    Evidence (GeneralDictionaryRecursiveEvidence.Instance candidate.registry finalPacket.context model) tree :=
  indexed_relocated candidate.registry candidate.context finalPacket.context (fun slot => slot)
    actual_sources actual_seed (GeneralDictionarySharedMetadata.formed_metadata observed_formed)
    model valid.1 tree (old_tree model valid) tree_locality

theorem actual_payload (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models observed.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence candidate.registry finalPacket.context model
      producer (.node declaration.id []) :=
  ⟨tree,⟨rfl,rfl⟩,actual_tree model valid⟩

end Yulang.GeneralDictionaryCapturedTree168Transport
