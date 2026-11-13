import Yulang.GeneralDictionaryUnaryCurrentEvidence
import Yulang.GeneralDictionaryMixedCarrierRefresh

/-! Non-vacuous current Instance for the actual carrier-changing mixed packet.
The full variable-bearing source branch is derived from its installation history. -/
namespace Yulang.GeneralDictionaryUnaryCurrentExample
open GeneralDictionaryMixedCatalogExample GeneralDictionaryMixedCarrierRefresh
open GeneralNominalExamples (displayRoot model)
open GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralDictionaryRecursiveEvidence

noncomputable def prior : GeneralNominalRefinements.Refines packet.context.state snapshot :=
  ⟨refines.base,refines.heads,refines.nominals,(by intro _ h; cases h),refines.known,
    (by intro _ h; cases h),(by intro _ h; cases h),rfl,rfl⟩

noncomputable def shape : GeneralDictionaryUnaryCurrentEvidence.Shape packet refreshedContext where
  refinement := prior
  interpretation := rfl
  slot := 0
  descriptor := GeneralNominalExamples.listDescriptor
  nominal := rfl
  binder := 0
  bounds := (1,1)
  parameters := rfl
  query := GeneralDictionaryMixedCatalogInhabited.query
  packetBounds := rfl
  names := rfl
  located := rfl
  role := rfl
  defined := by intro name member; cases member

noncomputable abbrev children := GeneralNominalAllocation.children snapshot registry displayRoot declaration checked
  (GeneralNominalRecursiveInspection.bindings snapshot (report refreshedContext declaration shape.currentBounds))

theorem current_instance (m : GeneralNominalCommonBridge.Assignment) (valid : Models refreshed.current m) :
    Instance registry refreshedContext m displayRoot declaration.id children :=
  GeneralDictionaryUnaryCurrentEvidence.current_instance packet displayRoot refreshed refreshed_reachable
    packet_recorded shape GeneralDictionarySupportRecursiveExample.initial_source.metadata m valid

theorem positive_instance : Models refreshed.current model ∧
    Instance registry refreshedContext model displayRoot declaration.id children :=
  ⟨refreshed_inhabited,current_instance model refreshed_inhabited⟩

theorem nonterminal : children ≠ [] := by
  simp only [children,GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children]
  simp [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,declaration,List.mergeSort_pair,
    GeneralDeclarationDemands.emitAll]
end Yulang.GeneralDictionaryUnaryCurrentExample
