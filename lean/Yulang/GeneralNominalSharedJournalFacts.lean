import Yulang.GeneralNominalSharedCaptureFacts
import Yulang.GeneralNominalSupportSteps

/-! Finite sharing constraints recovered from actual historical packet models.
No current Joint, Installable or observed-coherence premise is needed. -/
namespace Yulang.GeneralNominalSharedJournalFacts
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalLinearCaptureFacts GeneralNominalSharedCaptureFacts
open GeneralNominalSaturationState GeneralNominalSupport GeneralDeclarations

theorem coherent_after_steps (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after)
    (packet : Packet roles) (member : packet ∈ before.current.packets)
    (slot : Fin packet.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (recorded : packet.context.state.nominals slot = some descriptor)
    (headBounds : packet.bounds = [(slot,slot)]) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    Coherent model (packet.context.state.base.source slot) descriptor.declaration.name names := by
  have prior := GeneralNominalSupportSteps.steps_models path model valid
  have branch := prior.2.1 packet member
  change BranchModels packet.registry packet.context packet.site.occurrence packet.declaration packet.checked packet.bounds model at branch
  rw [headBounds] at branch
  have projection := branch.2.1
  rw [report_exact packet.context packet.declaration slot descriptor recorded names bounds parameters query] at projection
  exact coherent_of_projection packet.context.state model slot descriptor.declaration.name names bounds projection

/-- A later head may rename binders or remove sharing, provided every current
same-name pair was also shared in the historical packet. Its interval syntax
may change freely; this theorem concerns inspection projection, not allocation. -/
theorem projection_after_steps (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after)
    (packet : Packet roles) (member : packet ∈ before.current.packets)
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (headBounds : packet.bounds = [(oldSlot,oldSlot)]) {n : Nat}
    (oldNames names : Fin n → Nat)
    (oldBounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (oldParameters : oldDescriptor.arguments = List.ofFn fun i => .type (oldBounds i))
    (oldQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [oldNames i])])
    (slot : Fin after.current.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor after.current.context.state.base.slots)
    (recorded : after.current.context.state.nominals slot = some descriptor)
    (bounds : Fin n → GeneralNominalInspection.Bounds after.current.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (sharing : ∀ i j, names i = names j → oldNames i = oldNames j)
    (source : after.current.context.state.base.source slot = packet.context.state.base.source oldSlot)
    (name : descriptor.declaration.name = oldDescriptor.declaration.name)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    ProjectionModels after.current.context.state
      (captured after.current.context.state slot descriptor.declaration.name names bounds) model := by
  apply projection_of_coherent after.current.context.state model valid.1 slot descriptor recorded names bounds parameters
  rw [source,name]
  have old := coherent_after_steps registry root before after path packet member oldSlot oldDescriptor oldRecorded
    headBounds oldNames oldBounds oldParameters oldQuery model valid
  intro i j same
  exact old i j (sharing i j same)
end Yulang.GeneralNominalSharedJournalFacts
