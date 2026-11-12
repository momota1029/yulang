import Yulang.GeneralNominalRepeatedMergeTransport

/-! An integrated same-assignment branch result for the covered point-to-point
repeated-head historical family. It is not the unrestricted V5 node theorem. -/
namespace Yulang.GeneralNominalRepeatedHistoricalBranch
open GeneralDeclarations GeneralNominalRecursiveCandidates

/-- Actual history supplies all semantic residuals. No BranchModels,
SameParameters, merge-equation, Joint, or Installable premise occurs. -/
theorem branch_after_steps (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after)
    (packet : GeneralNominalSaturationState.Packet roles)
    (member : packet ∈ before.current.packets)
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (oldBounds : packet.bounds = [(oldSlot,oldSlot)]) (binder : Nat)
    (inputs : packet.declaration.inputNames = [binder])
    (oldLeft oldRight : GeneralNominalInspection.Bounds packet.context.state)
    (oldParameters : oldDescriptor.arguments = [.type oldLeft,.type oldRight])
    (oldQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal oldDescriptor.declaration.name [.variables [binder],.variables [binder]]])
    (slot : Fin after.current.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor after.current.context.state.base.slots)
    (recorded : after.current.context.state.nominals slot = some descriptor)
    (left right : GeneralNominalInspection.Bounds after.current.context.state)
    (parameters : descriptor.arguments = [.type left,.type right])
    (query : GeneralNominalInspection.queries after.current.context.state after.current.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name [.variables [binder],.variables [binder]]])
    (oldLeftPoint : oldLeft.1 = oldLeft.2) (oldRightPoint : oldRight.1 = oldRight.2)
    (leftPoint : left.1 = left.2) (rightPoint : right.1 = right.2)
    (source : packet.context.state.base.source oldSlot = after.current.context.state.base.source slot)
    (name : oldDescriptor.declaration.name = descriptor.declaration.name)
    (seed : packet.context.state.seed = after.current.context.state.seed)
    (checked : DeclarationChecked registry.constructors roles packet.declaration)
    (terminal : packet.declaration.requirements = []) (equation : Equation)
    (associated : packet.declaration.associated = [equation])
    (output : packet.site.occurrence.demand.outputs = [⟨equation.name,after.current.context.state.base.source slot⟩])
    (translated : GeneralNominalInspection.translate after.current.context.state.constructors after.current.context.interpretation
      (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name [.variables [binder],.variables [binder]])
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model) :
    BranchModels registry after.current.context packet.site.occurrence packet.declaration checked [(slot,slot)] model := by
  apply (GeneralNominalRepeatedMaterializationFacts.branch_models_iff after.current.context registry
    packet.site.occurrence packet.declaration checked terminal equation associated slot descriptor recorded binder
    (by rw [inputs]; simp) left right parameters query output translated model).mpr
  refine ⟨valid.1,?_,?_⟩
  · have same := GeneralNominalRepeatedJournalFacts.same_after_steps registry root before after path packet member
      oldSlot oldDescriptor oldRecorded oldBounds binder oldLeft oldRight oldParameters oldQuery model valid
    simpa only [source,name] using same
  · exact GeneralNominalRepeatedMergeTransport.merges_after_steps registry root before after path packet member
      oldSlot oldDescriptor oldRecorded oldBounds binder inputs oldLeft oldRight oldParameters oldQuery
      slot descriptor recorded left right parameters query oldLeftPoint oldRightPoint leftPoint rightPoint
      source name seed model valid

end Yulang.GeneralNominalRepeatedHistoricalBranch
