import Yulang.GeneralNominalRepeatedMaterializationFacts
import Yulang.GeneralNominalSupportSteps

/-! Repeated-parameter equality survives actual support transitions because
it is recovered from a recorded packet at the caller's unchanged assignment.
This uses journal membership, not Installable, Joint, or a branch premise. -/
namespace Yulang.GeneralNominalRepeatedJournalFacts
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalBinaryCaptureFacts GeneralNominalRepeatedCaptureFacts
open GeneralNominalSaturationState GeneralNominalSupport GeneralDeclarations

/-- Recover observed parameter equality from a real earlier journal packet.
The subsequent path may contain installation, merge, refresh, or reobservation;
its direction is important: an after-model is also a before-model. -/
theorem same_after_steps (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after)
    (packet : Packet roles) (member : packet ∈ before.current.packets)
    (slot : Fin packet.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (recorded : packet.context.state.nominals slot = some descriptor)
    (bounds : packet.bounds = [(slot,slot)]) (binder : Nat)
    (left right : GeneralNominalInspection.Bounds packet.context.state)
    (parameters : descriptor.arguments = [.type left,.type right])
    (query : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name [.variables [binder],.variables [binder]]])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    SameParameters model (packet.context.state.base.source slot) descriptor.declaration.name := by
  have prior := GeneralNominalSupportSteps.steps_models path model valid
  have branch := prior.2.1 packet member
  change BranchModels packet.registry packet.context packet.site.occurrence packet.declaration packet.checked packet.bounds model at branch
  rw [bounds] at branch
  have projection := branch.2.1
  rw [report_exact packet.context packet.declaration slot descriptor recorded binder binder left right parameters query] at projection
  exact projection_requires_same packet.context.state model slot descriptor.declaration.name binder left right projection

/-- Recompute projection for a later repeated head after the actual history.
The current bounds may differ from the earlier bounds; only the observed
source/name identity is shared. No current SameParameters premise is needed. -/
theorem projection_after_steps (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after)
    (packet : Packet roles) (member : packet ∈ before.current.packets)
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (oldBounds : packet.bounds = [(oldSlot,oldSlot)]) (oldBinder : Nat)
    (oldLeft oldRight : GeneralNominalInspection.Bounds packet.context.state)
    (oldParameters : oldDescriptor.arguments = [.type oldLeft,.type oldRight])
    (oldQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal oldDescriptor.declaration.name [.variables [oldBinder],.variables [oldBinder]]])
    (slot : Fin after.current.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor after.current.context.state.base.slots)
    (recorded : after.current.context.state.nominals slot = some descriptor) (binder : Nat)
    (left right : GeneralNominalInspection.Bounds after.current.context.state)
    (parameters : descriptor.arguments = [.type left,.type right])
    (source : after.current.context.state.base.source slot = packet.context.state.base.source oldSlot)
    (name : descriptor.declaration.name = oldDescriptor.declaration.name)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    ProjectionModels after.current.context.state
      (captured after.current.context.state slot descriptor.declaration.name binder binder left right) model := by
  apply projection_of_same after.current.context.state model valid.1 slot descriptor recorded binder left right parameters
  rw [source,name]
  exact same_after_steps registry root before after path packet member oldSlot oldDescriptor oldRecorded oldBounds
    oldBinder oldLeft oldRight oldParameters oldQuery model valid

end Yulang.GeneralNominalRepeatedJournalFacts
