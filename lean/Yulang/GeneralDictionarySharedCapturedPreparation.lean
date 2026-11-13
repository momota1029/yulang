import Yulang.GeneralDictionarySharedCapturedProducer
import Yulang.GeneralDictionarySharedCapturedInputReady
import Yulang.GeneralDictionarySharedMetadata
import Yulang.GeneralNominalAllocationSupport

/-! Actual post-parent-refresh source ownership and producer applicability.
Freshness follows from the parent reservation pool; it is not an extra
precondition asserting the desired selected result. -/
namespace Yulang.GeneralDictionarySharedCapturedPreparation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDictionarySharedOutputBinderScope GeneralDictionarySharedCapturedTargets
open GeneralDictionarySharedCapturedModel GeneralDictionarySharedCapturedRefresh
open GeneralDictionarySharedCapturedProducer
open GeneralDeclarationExamples (roles)

theorem source_pool (identity : Nat) (member : identity ∈ GeneralNominalState.sources snapshot) :
    identity ∈ GeneralNominalState.sources source ++ GeneralNominalAllocation.reserved source registry root.identity := by
  have old := certificate.support identity member
  exact GeneralNominalAllocationSupport.private_sources packet (by simp)
    (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h) old

theorem fresh (invocation : Nat) : GeneralNominalAllocation.Fresh snapshot registry invocation := by
  intro key _ collision
  rcases List.mem_append.mp (source_pool _ collision) with old | reserved
  · have small := initial_source.below_seed _ old
    have large := GeneralNominalIdentities.source_above_seed source.seed key
    change GeneralNominalAllocation.source snapshot registry invocation key ≤ 2 at small
    change 2 < GeneralNominalAllocation.source snapshot registry invocation key at large
    omega
  · obtain ⟨previous,owned,equal⟩ := List.mem_map.mp reserved
    have same : previous = key := (GeneralNominalIdentities.source_identity source.seed previous key).mp equal
    subst previous
    exact List.mem_append_right _ owned

theorem linked : GeneralNominalState.Linked snapshot producer.demand := by
  constructor
  · intro index
    rw [GeneralDictionarySharedCapturedInstallation.producer_inputs]
    exact ⟨GeneralNominalAllocationSupport.slot_source snapshot (3 : Fin 5),
      GeneralNominalAllocationSupport.slot_source snapshot (4 : Fin 5)⟩
  · intro output present
    rw [producer_output] at present
    cases List.mem_singleton.mp present
    apply GeneralNominalRefinements.sources certificate.refines
    exact (GeneralNominalSourceFormation.installation_reserves packet
      (GeneralNominalAllocation.origin root.identity capturedProposal.id 5 111 0)
      (by decide +kernel)).1

theorem prepared : Prepared registry refreshedContext producer declaration
    GeneralDictionaryRecursiveObstruction.declaration_checked := by
  refine ⟨GeneralDictionarySharedMetadata.formed_metadata formed,linked,fresh _,
    [(3,4)],bounds,?_,?_,model,branch_models⟩
  · change Finished (GeneralNominalPacketSupport.report candidate)
    rw [GeneralDictionarySharedCapturedProducer.report_exact]; exact ⟨rfl,rfl,rfl⟩
  · refine ⟨(by intro output h; rw [producer_output] at h; cases List.mem_singleton.mp h; exact ⟨GeneralDictionaryRecursiveObstruction.equation,by simp,rfl⟩),?_⟩
    change (GeneralNominalPacketSupport.namedSchema candidate).unknown = false
    rw [GeneralDictionarySharedCapturedProducer.schema_exact]

theorem survivor : Survivor registry refreshedContext producer declaration.id candidate.children :=
  ⟨producer_ready,declaration,by simp,GeneralDictionaryRecursiveObstruction.declaration_checked,
    rfl,rfl,[(3,4)],bounds,prepared,rfl⟩
end Yulang.GeneralDictionarySharedCapturedPreparation
