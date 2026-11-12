import Yulang.GeneralNominalFiniteHistoricalBranch
import Yulang.GeneralDictionaryOrdinarySelectedReplay

/-! Same-model selected evidence from structurally covered recorded packets.
Current uniqueness IDENTIFIES the historical key; key agreement is not assumed.
Source-formed packet provenance supplies declaration visibility and role.
This remains a terminal, recorded-path-covered fragment, not unrestricted V5. -/
namespace Yulang.GeneralNominalHistoricalSelectedEvidence
open GeneralDeclarations GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralNominalSharedJournalPaths
open GeneralDictionaryRecursiveEvidence

/-- Source formation records the exact role of an installed declaration. -/
theorem packet_role (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (formed : GeneralNominalSupportSteps.SourceFormed registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.current.packets) :
    packet.declaration.role = packet.site.occurrence.demand.role := by
  obtain ⟨before,support,_,_,enabled,_,_,_⟩ :=
    GeneralDictionaryInstallationOrigin.packet_origin registry root state formed packet member
  exact enabled.1.2.2.2.2.1

/-- Definedness depends on the declaration and occurrence, not its observation
context, so the actual earlier installation already supplies it. -/
theorem packet_root_defined (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (formed : GeneralNominalSupportSteps.SourceFormed registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.current.packets) :
    GeneralNominalMaterialization.RootDefined packet.declaration packet.site.occurrence := by
  obtain ⟨before,support,_,_,enabled,_,_,_⟩ :=
    GeneralDictionaryInstallationOrigin.packet_origin registry root state formed packet member
  have prepared := enabled.1.2.2.2.2.2.2.1
  obtain ⟨_,_,_,bounds,_,_,ready,_⟩ := prepared
  exact ready.1

theorem selected_evidence (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (formed : GeneralNominalSupportSteps.SourceFormed registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.current.packets)
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (headBounds : packet.bounds = [(oldSlot,oldSlot)]) {n : Nat} (names : Fin n → Nat)
    (declared : ∀ i, names i ∈ packet.declaration.inputNames)
    (oldBounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (oldParameters : oldDescriptor.arguments = List.ofFn fun i => .type (oldBounds i))
    (oldQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (slot : Fin state.current.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.current.context.state.base.slots)
    (recorded : state.current.context.state.nominals slot = some descriptor)
    (bounds : Fin n → GeneralNominalInspection.Bounds state.current.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries state.current.context.state state.current.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (lowerPaths : ∀ i, RecordedPath state.current.context.state
      (packet.context.state.base.source (oldBounds i).1)
      (state.current.context.state.base.source (bounds i).1))
    (upperPaths : ∀ i, RecordedPath state.current.context.state
      (packet.context.state.base.source (oldBounds i).2)
      (state.current.context.state.base.source (bounds i).2))
    (headPath : RecordedPath state.current.context.state
      (packet.context.state.base.source oldSlot) (state.current.context.state.base.source slot))
    (name : oldDescriptor.declaration.name = descriptor.declaration.name)
    (seed : packet.context.state.seed = state.current.context.state.seed)
    (terminal : packet.declaration.requirements = [])
    (outputPaths : ∀ output ∈ packet.site.occurrence.demand.outputs,
      RecordedPath state.current.context.state output.target (state.current.context.state.base.source slot))
    (translated : ∀ output ∈ packet.site.occurrence.demand.outputs, ∀ equation,
      packet.declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate state.current.context.state.constructors state.current.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model)
    (located : arguments state.current.context packet.site.occurrence = some [(slot,slot)])
    (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state packet.site.occurrence (.selected key children)) :
    packet.declaration.id = key ∧ children = [] ∧
      GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model packet.site.occurrence key [] ∧
      GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model packet.site.occurrence (.node key []) := by
  let checked : DeclarationChecked registry.constructors roles packet.declaration := by
    have reg := GeneralDictionarySupportJournal.packet_registry registry root state formed packet member
    rw [← reg]
    exact packet.checked
  have defined := packet_root_defined registry root state formed packet member
  have branch := GeneralNominalFiniteHistoricalBranch.branch_after_steps registry root state state .refl packet member
    oldSlot oldDescriptor oldRecorded headBounds names declared oldBounds oldParameters oldQuery
    slot descriptor recorded bounds parameters query lowerPaths upperPaths headPath name seed checked terminal
    outputPaths translated model valid
  have finished := report_finished state.current.context packet.declaration slot descriptor recorded names bounds parameters query
  have ready := (GeneralNominalAssociatedSourceTransport.request_ready_iff state.current.context registry
    packet.site.occurrence packet.declaration checked terminal [(slot,slot)] descriptor.declaration.name names translated).mpr defined
  have emitted : GeneralNominalAllocation.children state.current.context.state registry packet.site.occurrence
      packet.declaration checked (bindings state.current.context.state (report state.current.context packet.declaration [(slot,slot)])) = [] := by
    simp [GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children,
      GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
      GeneralCanonicalChildOrder.canonicalRequirements,GeneralDeclarationDemands.emitAll,terminal]
  cases selected with
  | selected safe unique =>
    have metadata : Metadata registry state.current.context := by
      obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := unique.1
      exact prepared.1
    have inst : Instance registry state.current.context model packet.site.occurrence packet.declaration.id [] :=
      ⟨packet.declaration,GeneralDictionarySupportJournal.packet_visible registry root state formed packet member,
        checked,rfl,packet_role registry root state formed packet member,[(slot,slot)],located,finished,ready,
        emitted.symm,metadata,branch⟩
    have identities := unique.2 _ _ (GeneralDictionaryOrdinarySelectedReplay.survivor_of_instance registry
      state.current.context packet.site.occurrence key children unique.1 model packet.declaration.id [] inst)
    have result : Instance registry state.current.context model packet.site.occurrence key [] := identities.1 ▸ inst
    exact ⟨identities.1,identities.2.symm,result,(evidence_leaf_iff registry state.current.context model packet.site.occurrence key).mpr result⟩
end Yulang.GeneralNominalHistoricalSelectedEvidence
