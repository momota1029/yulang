import Yulang.GeneralNominalHistoricalOutputRecovery
import Yulang.GeneralDictionarySupportSourceInvariants

/-! The strongest recorded nominal fragment: root and child output equalities
are recovered from actual prior materialization, not supplied as paths or semantic
premises. Source-formed history also derives allocation seed preservation. Current
selection identifies the original declaration key and actual current children. -/
namespace Yulang.GeneralNominalRecoveredNodeEvidence
open GeneralDeclarations GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralNominalSharedJournalPaths
open GeneralDictionaryRecursiveEvidence GeneralNominalHistoricalSelectedEvidence

theorem selected_node_without_output_paths (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
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
    (noOutputBinders : packet.declaration.outputNames = [])
    (variables : ∀ clause ∈ packet.declaration.requirements, ∀ pattern ∈ clause.arguments,
      ∃ name, GeneralDeclarationPatterns.normalize pattern = .var name)
    (translated : ∀ output ∈ packet.site.occurrence.demand.outputs, ∀ equation,
      packet.declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate state.current.context.state.constructors state.current.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (childTranslated : ∀ clause ∈ packet.declaration.requirements, ∀ equation ∈ clause.outputs,
      GeneralNominalInspection.translate state.current.context.state.constructors state.current.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
          .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (oldTranslated : ∀ output ∈ packet.site.occurrence.demand.outputs, ∀ equation,
      packet.declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (oldChildTranslated : ∀ clause ∈ packet.declaration.requirements, ∀ equation ∈ clause.outputs,
      GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
          .nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i]))
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
  have seed := GeneralDictionarySupportSourceInvariants.packet_seed registry root state formed packet member
  have headEqual := headPath.sound model valid.1
  have roots := GeneralNominalHistoricalOutputRecovery.root_outputs_equivalent registry root state formed packet member
    oldSlot oldDescriptor oldRecorded headBounds names oldBounds oldParameters oldQuery oldTranslated model valid
  have childOld := GeneralNominalHistoricalOutputRecovery.child_outputs_equivalent state.current packet member
    oldSlot oldDescriptor oldRecorded headBounds names oldBounds oldParameters oldQuery oldChildTranslated model valid
  have childCurrent (clause : Clause) (hc : clause ∈ packet.declaration.requirements)
      (equation : Equation) (he : equation ∈ clause.outputs) := childOld clause hc equation he
  have childTargets : ∀ clause ∈ packet.declaration.requirements, ∀ equation ∈ clause.outputs,
      CommonNominalFullCarrier.Equivalent (model (GeneralDeclarationDemands.outputTarget packet.declaration
        (GeneralNominalAllocation.capture state.current.context.state registry packet.site.occurrence.identity packet.declaration.id
          (bindings state.current.context.state (report state.current.context packet.declaration [(slot,slot)])))
        (GeneralNominalAllocation.allocation (roles := roles) state.current.context.state registry
          packet.site.occurrence.identity packet.declaration.id clause).outputs equation)).1
      (model (state.current.context.state.base.source slot)).1 := by
    intro clause hc equation he
    have eq := childCurrent clause hc equation he
    rw [GeneralNominalHistoricalOutputRecovery.child_target_same_seed packet.context.state state.current.context.state
      packet.registry registry packet.site.occurrence packet.declaration noOutputBinders packet.bindings
      (bindings state.current.context.state (report state.current.context packet.declaration [(slot,slot)])) clause equation seed] at eq
    exact ⟨CommonNominalFullCarrier.subtype_trans eq.1 headEqual.1,
      CommonNominalFullCarrier.subtype_trans headEqual.2 eq.2⟩
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
    (fun output member => ⟨CommonNominalFullCarrier.subtype_trans (roots output member).1 headEqual.1,
      CommonNominalFullCarrier.subtype_trans headEqual.2 (roots output member).2⟩) childTargets).mpr
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
end Yulang.GeneralNominalRecoveredNodeEvidence
