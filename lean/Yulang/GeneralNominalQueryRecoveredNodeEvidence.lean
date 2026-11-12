import Yulang.GeneralNominalRecoveredNodeEvidence
import Yulang.GeneralDictionarySupportMetadataInvariants

/-! Query-only structural coverage: historic RHS translations, head name and
allocation seed are derived from actual provenance, not independently assumed. -/
namespace Yulang.GeneralNominalQueryRecoveredNodeEvidence
open GeneralDeclarations GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralNominalSharedJournalPaths
open GeneralDictionaryRecursiveEvidence GeneralNominalHistoricalSelectedEvidence

/-- Nominal invariance identifies old/current head names at the same caller
assignment. Recorded head equality is stronger than just interval compatibility. -/
theorem packet_head_name (state : GeneralNominalSaturationState.State roles)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.packets)
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (slot : Fin state.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.context.state.base.slots)
    (recorded : state.context.state.nominals slot = some descriptor)
    (headPath : RecordedPath state.context.state
      (packet.context.state.base.source oldSlot) (state.context.state.base.source slot))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state model) :
    oldDescriptor.declaration.name = descriptor.declaration.name := by
  have branch := valid.2.1 packet member
  have oldValid := (branch_interval_sound packet.registry packet.context packet.site.occurrence packet.declaration
    packet.checked packet.bounds model branch).1
  obtain ⟨oldArgs,_,oldEqual⟩ := oldValid.2.1 oldSlot oldDescriptor oldRecorded
  obtain ⟨args,_,equal⟩ := valid.1.2.1 slot descriptor recorded
  have headEqual := headPath.sound model valid.1
  exact ((CommonNominalFullCarrier.nominal_regular_invariant_exact ..).mp
    (CommonNominalFullCarrier.subtype_trans oldEqual.2
      (CommonNominalFullCarrier.subtype_trans headEqual.1 equal.1))).1

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
  have name := packet_head_name state.current packet member oldSlot oldDescriptor oldRecorded
    slot descriptor recorded headPath model valid
  have oldQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i])] := by
    rw [GeneralDictionarySupportMetadataInvariants.packet_queries registry root state formed packet member,query,name]
  have oldTranslated : ∀ output ∈ packet.site.occurrence.demand.outputs, ∀ equation,
      packet.declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i]) := by
    intro output ho equation found
    rw [GeneralDictionarySupportMetadataInvariants.packet_translate registry root state formed packet member,
      translated output ho equation found,name]
  have oldChildTranslated : ∀ clause ∈ packet.declaration.requirements, ∀ equation ∈ clause.outputs,
      GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i]) := by
    intro clause hc equation he
    rw [GeneralDictionarySupportMetadataInvariants.packet_translate registry root state formed packet member,
      childTranslated clause hc equation he,name]
  exact GeneralNominalRecoveredNodeEvidence.selected_node_without_output_paths registry root state formed packet member
    oldSlot oldDescriptor oldRecorded headBounds names declared oldBounds oldParameters oldQuery
    slot descriptor recorded bounds parameters query lowerPaths upperPaths headPath name noOutputBinders variables
    translated childTranslated oldTranslated oldChildTranslated model valid located key children selected dictionaries given
end Yulang.GeneralNominalQueryRecoveredNodeEvidence
