import Yulang.GeneralNominalCenteredPermutationInstallationGuard

set_option backward.isDefEq.respectTransparency false

/-! Private contexts and raw emitted sites retain the same observation core
when a current-context counterpart is installed. -/
namespace Yulang.GeneralNominalCenteredPermutationEmission
open GeneralDeclarations GeneralRegistryReordering GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalMetadataEquivalence (replace)
open GeneralNominalJournalPermutation (ContextPair)
variable {roles : Roles.RoleDecls}
variable (packet : Packet roles) (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)

private theorem metadata_private_eq :
    (GeneralNominalPacketMetadata.rebase packet allocated reserved).privateContext.state =
      replace packet.privateContext.state
        (allocated ++ GeneralNominalAllocation.keys packet.registry packet.site.occurrence.identity)
        ((reserved ++ GeneralNominalAllocation.reserved packet.context.state packet.registry packet.site.occurrence.identity) ++ []) := by
  unfold Packet.privateContext GeneralNominalRecursiveCandidates.privateState
  change GeneralNominalState.extend (GeneralNominalAllocation.propagate _ _ _ _
      (GeneralNominalPacketMetadata.rebase packet allocated reserved).bindings) []
      (GeneralNominalRecursiveInspection.selfChecks _ (GeneralNominalPacketSupport.report _)) = _
  rw [GeneralNominalPacketMetadata.bindings,GeneralNominalPacketMetadata.report]
  rfl

theorem metadata_private (keys : ∀ key, key ∈ allocated ↔ key ∈ packet.context.state.allocated)
    (names : ∀ name, name ∈ reserved ↔ name ∈ packet.context.state.reserved) :
    ContextPair packet.privateContext (GeneralNominalPacketMetadata.rebase packet allocated reserved).privateContext := by
  refine ⟨⟨_,_,metadata_private_eq packet allocated reserved,?_,?_⟩,rfl⟩
  · intro key
    change key ∈ allocated ++ _ ↔ key ∈ packet.context.state.allocated ++ _
    simp only [List.mem_append,keys]
  · intro name
    change name ∈ (reserved ++ _) ++ [] ↔ name ∈ (packet.context.state.reserved ++ _) ++ []
    simp only [List.mem_append,names]

variable {registry : Registry} {decl : Declaration}

theorem registry_private (order : Reorders packet.registry registry) (pair : DeclarationReorders packet.declaration decl) :
    ContextPair packet.privateContext (GeneralNominalPacketReordering.rebase packet order pair).privateContext := by
  refine ⟨⟨_,_,?_,GeneralNominalPacketReordering.allocated_membership order pair,
    GeneralNominalPacketReordering.reserved_membership order pair⟩,rfl⟩
  unfold Packet.privateContext GeneralNominalRecursiveCandidates.privateState
  simp only [GeneralNominalPacketReordering.rebase,GeneralDictionaryRecursiveOrder.report_reorders packet.context _ _ pair,
    GeneralNominalAllocation.propagate,GeneralNominalAllocation.merges,GeneralNominalAllocation.capture,
    GeneralNominalAllocation.source,Declaration.inputNames,pair.head,pair.id,GeneralNominalState.extend,replace]

theorem rebased_private {other : Packet roles}
    (paired : GeneralNominalCenteredPermutationRepresentation.RebasedPacket first last packet other) :
    ContextPair packet.privateContext other.privateContext := by
  obtain ⟨_,decl,order,pair,allocated,reserved,keys,names,rfl⟩ := paired
  have one := registry_private packet order pair
  have two := metadata_private (GeneralNominalPacketReordering.rebase packet order pair) allocated reserved keys names
  exact ⟨GeneralNominalMetadataEquivalence.trans one.state two.state,one.interpretation.trans two.interpretation⟩

theorem clause_child (clause : Clause) (valid : clause.Signature roles) :
    GeneralNominalFeedbackSites.clauseChild (GeneralNominalPacketMetadata.rebase packet allocated reserved) clause valid =
      GeneralNominalFeedbackSites.clauseChild packet clause valid := by
  unfold GeneralNominalFeedbackSites.clauseChild GeneralNominalFeedbackSites.frame
  rw [GeneralNominalPacketMetadata.bindings]
  rfl

theorem usable (name origin) :
    GeneralNominalSharedCaptures.Usable (GeneralNominalPacketMetadata.rebase packet allocated reserved) name origin ↔
      GeneralNominalSharedCaptures.Usable packet name origin := by
  unfold GeneralNominalSharedCaptures.Usable
  have models := funext (fun model => propext (GeneralNominalPacketMetadata.holds packet allocated reserved model))
  rw [models]
  apply and_congr ((GeneralNominalPacketMetadata.observation packet allocated reserved).captured _ name origin).symm
  simp only [GeneralNominalSharedCaptures.InputBound,GeneralNominalPacketMetadata.holds,
    GeneralNominalPacketMetadata.capture]

theorem shared_origin (child position origin) :
    GeneralNominalSharedEmission.OriginAt (GeneralNominalPacketMetadata.rebase packet allocated reserved) child position origin ↔
      GeneralNominalSharedEmission.OriginAt packet child position origin := by
  simp only [GeneralNominalSharedEmission.OriginAt,GeneralNominalSharedEmission.clauseChild,
    usable,clause_child]
  rfl

theorem fallback_origin (child position origin) :
    GeneralNominalFeedbackSites.OriginAt (GeneralNominalPacketMetadata.rebase packet allocated reserved) child position origin ↔
      GeneralNominalFeedbackSites.OriginAt packet child position origin := by
  unfold GeneralNominalFeedbackSites.OriginAt
  simp only [clause_child]
  change (∃ clause ∈ packet.declaration.requirements, ∃ valid, ∃ index, _ ∧ _ ∧
    ∃ capture ∈ (GeneralNominalPacketSupport.report (GeneralNominalPacketMetadata.rebase packet allocated reserved)).captures, _) ↔ _
  rw [GeneralNominalPacketMetadata.report]
  constructor
  · rintro ⟨clause,member,valid,index,childEq,positionEq,capture,recorded,declared,found,pattern⟩
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp recorded
    exact ⟨clause,member,valid,index,childEq,positionEq,original,present,declared,found,pattern⟩
  · rintro ⟨clause,member,valid,index,childEq,positionEq,capture,recorded,declared,found,pattern⟩
    exact ⟨clause,member,valid,index,childEq,positionEq,
      GeneralNominalReportMetadata.capture packet.context.state allocated reserved capture,
      List.mem_map.mpr ⟨capture,recorded,rfl⟩,declared,found,pattern⟩

open Classical in
private theorem choice_option {α : Type u} {first last : α → Prop}
    (same : ∀ value, first value ↔ last value) (fallback : Option α) :
    (if h : ∃ value, first value then some (Classical.choose h) else fallback) =
      (if h : ∃ value, last value then some (Classical.choose h) else fallback) := by
  have equal : first = last := funext (fun value => propext (same value))
  cases equal
  rfl

theorem child_origin (child : Occurrence roles) (index : Fin (roles child.demand.role).arity) :
    GeneralNominalSharedEmission.childOrigin (GeneralNominalPacketMetadata.rebase packet allocated reserved) child index =
      GeneralNominalSharedEmission.childOrigin packet child index := by
  classical
  unfold GeneralNominalSharedEmission.childOrigin
  have fallback : GeneralNominalFeedbackSites.childOrigin (GeneralNominalPacketMetadata.rebase packet allocated reserved) child index =
      GeneralNominalFeedbackSites.childOrigin packet child index := by
    unfold GeneralNominalFeedbackSites.childOrigin
    exact choice_option (fallback_origin packet allocated reserved child index.val) _
  rw [fallback]
  exact choice_option (shared_origin packet allocated reserved child index.val) _

theorem emitted :
    (GeneralNominalSharedEmission.emitted (GeneralNominalPacketMetadata.rebase packet allocated reserved)).sites =
      (GeneralNominalSharedEmission.emitted packet).sites := by
  change (GeneralNominalPacketMetadata.rebase packet allocated reserved).children.map _ = packet.children.map _
  rw [GeneralNominalPacketMetadata.children]
  apply List.map_congr_left
  intro child _
  unfold GeneralNominalSharedEmission.childSite
  congr 1
  exact congrArg List.ofFn (funext (child_origin packet allocated reserved child))

theorem rebased_emitted {other : Packet roles}
    (paired : GeneralNominalCenteredPermutationRepresentation.RebasedPacket first last packet other)
    (roleEq : first.roles = roles) :
    (GeneralNominalSharedEmission.emitted other).sites = (GeneralNominalSharedEmission.emitted packet).sites := by
  obtain ⟨registry,decl,order,pair,allocated,reserved,_,_,rfl⟩ := paired
  rw [emitted,GeneralNominalPacketReordering.shared_emitted_sites order pair (registry ▸ roleEq)]

end Yulang.GeneralNominalCenteredPermutationEmission
