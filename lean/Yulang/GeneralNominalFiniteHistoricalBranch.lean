import Yulang.GeneralNominalSharedJournalPaths
import Yulang.GeneralNominalAssociatedSourceTransport

/-! Historical same-model branches with arbitrary finite sharing and finite
associated request lists. Neither generated materialization nor merge equations
nor coherence is an extra hypothesis of the branch theorem. -/
namespace Yulang.GeneralNominalFiniteHistoricalBranch
open GeneralDeclarations GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralNominalMergeCongruence GeneralNominalAllocation
open GeneralNominalSharedJournalPaths

theorem branch_after_steps (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ before.current.packets)
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (headBounds : packet.bounds = [(oldSlot,oldSlot)]) {n : Nat} (names : Fin n → Nat)
    (declared : ∀ i, names i ∈ packet.declaration.inputNames)
    (oldBounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (oldParameters : oldDescriptor.arguments = List.ofFn fun i => .type (oldBounds i))
    (oldQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (slot : Fin after.current.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor after.current.context.state.base.slots)
    (recorded : after.current.context.state.nominals slot = some descriptor)
    (bounds : Fin n → GeneralNominalInspection.Bounds after.current.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries after.current.context.state after.current.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (lowerPaths : ∀ i, RecordedPath after.current.context.state
      (packet.context.state.base.source (oldBounds i).1)
      (after.current.context.state.base.source (bounds i).1))
    (upperPaths : ∀ i, RecordedPath after.current.context.state
      (packet.context.state.base.source (oldBounds i).2)
      (after.current.context.state.base.source (bounds i).2))
    (headPath : RecordedPath after.current.context.state
      (packet.context.state.base.source oldSlot) (after.current.context.state.base.source slot))
    (name : oldDescriptor.declaration.name = descriptor.declaration.name)
    (seed : packet.context.state.seed = after.current.context.state.seed)
    (checked : DeclarationChecked registry.constructors roles packet.declaration)
    (terminal : packet.declaration.requirements = [])
    (outputPaths : ∀ output ∈ packet.site.occurrence.demand.outputs,
      RecordedPath after.current.context.state output.target (after.current.context.state.base.source slot))
    (translated : ∀ output ∈ packet.site.occurrence.demand.outputs, ∀ equation,
      packet.declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate after.current.context.state.constructors after.current.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model) :
    BranchModels registry after.current.context packet.site.occurrence packet.declaration checked [(slot,slot)] model := by
  apply (GeneralNominalAssociatedSourceTransport.branch_models_iff after.current.context registry
    packet.site.occurrence packet.declaration checked terminal slot descriptor recorded
    names declared bounds parameters query translated model
    (fun output member => (outputPaths output member).sound model valid.1)).mpr
  refine ⟨valid.1,?_,?_⟩
  · have same := GeneralNominalSharedJournalFacts.coherent_after_steps registry root before after path packet member
      oldSlot oldDescriptor oldRecorded headBounds names oldBounds oldParameters oldQuery model valid
    rw [name] at same
    exact coherent_of_equivalent model _ _ _ names
      (headPath.sound model valid.1) same
  · exact merges_after_steps_of_journal_paths registry root before after path packet member oldSlot oldDescriptor oldRecorded headBounds
      names oldBounds oldParameters oldQuery slot descriptor recorded bounds parameters query lowerPaths upperPaths seed model valid
end Yulang.GeneralNominalFiniteHistoricalBranch
