import Yulang.GeneralNominalHistoricalSelectedEvidence
import Yulang.GeneralNominalWhereAssociatedFacts

/-! Node evidence in the current caller model, with actual nonterminal canonical
children. Historical key agreement is derived from current selection uniqueness.
Historical graph generation and child evidence remain separate obligations. -/
namespace Yulang.GeneralNominalHistoricalNodeEvidence
open GeneralDeclarations GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralNominalSharedJournalPaths
open GeneralDictionaryRecursiveEvidence GeneralNominalHistoricalSelectedEvidence

theorem selected_node (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
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
    (noOutputBinders : packet.declaration.outputNames = [])
    (variables : ∀ clause ∈ packet.declaration.requirements, ∀ pattern ∈ clause.arguments,
      ∃ name, GeneralDeclarationPatterns.normalize pattern = .var name)
    (outputPaths : ∀ output ∈ packet.site.occurrence.demand.outputs,
      RecordedPath state.current.context.state output.target (state.current.context.state.base.source slot))
    (translated : ∀ output ∈ packet.site.occurrence.demand.outputs, ∀ equation,
      packet.declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate state.current.context.state.constructors state.current.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (childTranslated : ∀ clause ∈ packet.declaration.requirements, ∀ equation ∈ clause.outputs,
      GeneralNominalInspection.translate state.current.context.state.constructors state.current.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
          .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (childPaths : ∀ clause ∈ packet.declaration.requirements, ∀ equation ∈ clause.outputs,
      RecordedPath state.current.context.state
        (GeneralDeclarationDemands.outputTarget packet.declaration
          (GeneralNominalAllocation.capture state.current.context.state registry packet.site.occurrence.identity packet.declaration.id
            (bindings state.current.context.state (report state.current.context packet.declaration [(slot,slot)])))
          (GeneralNominalAllocation.allocation (roles := roles) state.current.context.state registry
            packet.site.occurrence.identity packet.declaration.id clause).outputs equation)
        (state.current.context.state.base.source slot))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model)
    (located : arguments state.current.context packet.site.occurrence = some [(slot,slot)])
    (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state packet.site.occurrence (.selected key children))
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (Evidence registry state.current.context model) children dictionaries) :
    packet.declaration.id = key ∧
      Instance registry state.current.context model packet.site.occurrence key children ∧
      Evidence registry state.current.context model packet.site.occurrence (.node key dictionaries) := by
  let checked : DeclarationChecked registry.constructors roles packet.declaration := by
    have reg := GeneralDictionarySupportJournal.packet_registry registry root state formed packet member
    rw [← reg]
    exact packet.checked
  have coherent := GeneralNominalSharedJournalFacts.coherent_after_steps registry root state state .refl
    packet member oldSlot oldDescriptor oldRecorded headBounds names oldBounds oldParameters oldQuery model valid
  rw [name] at coherent
  have currentCoherent := coherent_of_equivalent model _ _ _ names (headPath.sound model valid.1) coherent
  have merges := merges_after_steps_of_journal_paths registry root state state .refl packet member
    oldSlot oldDescriptor oldRecorded headBounds names oldBounds oldParameters oldQuery
    slot descriptor recorded bounds parameters query lowerPaths upperPaths seed model valid
  have branch := (GeneralNominalWhereAssociatedFacts.branch_models_iff state.current.context registry
    packet.site.occurrence packet.declaration checked noOutputBinders variables slot descriptor recorded
    names declared bounds parameters query translated childTranslated model
    (fun output member => (outputPaths output member).sound model valid.1)
    (fun clause hc equation he => (childPaths clause hc equation he).sound model valid.1)).mpr
      ⟨valid.1,currentCoherent,merges⟩
  have finished := report_finished state.current.context packet.declaration slot descriptor recorded names bounds parameters query
  have ready := (GeneralNominalWhereAssociatedFacts.request_ready_iff state.current.context registry
    packet.site.occurrence packet.declaration checked variables [(slot,slot)] descriptor.declaration.name names
    translated childTranslated).mpr (packet_root_defined registry root state formed packet member)
  let emitted := GeneralNominalAllocation.children state.current.context.state registry packet.site.occurrence
    packet.declaration checked (bindings state.current.context.state (report state.current.context packet.declaration [(slot,slot)]))
  cases selected with
  | selected safe unique =>
    have metadata : Metadata registry state.current.context := by
      obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := unique.1
      exact prepared.1
    have inst : Instance registry state.current.context model packet.site.occurrence packet.declaration.id emitted :=
      ⟨packet.declaration,GeneralDictionarySupportJournal.packet_visible registry root state formed packet member,
        checked,rfl,packet_role registry root state formed packet member,[(slot,slot)],located,finished,ready,
        rfl,metadata,branch⟩
    have identities := unique.2 _ _ (GeneralDictionaryOrdinarySelectedReplay.survivor_of_instance registry
      state.current.context packet.site.occurrence key children unique.1 model packet.declaration.id emitted inst)
    have result : Instance registry state.current.context model packet.site.occurrence key children :=
      identities.1 ▸ identities.2 ▸ inst
    exact ⟨identities.1,result,evidence_node registry state.current.context model packet.site.occurrence key children dictionaries result given⟩
end Yulang.GeneralNominalHistoricalNodeEvidence
