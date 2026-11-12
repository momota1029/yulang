import Yulang.GeneralNominalRepeatedJournalFacts

/-! Allocation equations survive changes of interval syntax when the endpoints
have the same denotation. Point descriptors provide this denotational condition
from shared actual observations, without assuming the new merge equations. -/
namespace Yulang.GeneralNominalRepeatedMergeTransport
open CommonNominalFullCarrier GeneralNominalAllocation GeneralDeclarations
open GeneralSourceState (Interval)
open Core.PresenceGeneration (TyTerm)
open GeneralNominalRecursiveInspection

theorem union_equivalent {a b c d : Ty} (first : Equivalent a c) (last : Equivalent b d) :
    Equivalent (.union a b) (.union c d) := by
  have one := (common_union_is_join a b (.union a b)).mp (subtype_refl _)
  have two := (common_union_is_join c d (.union c d)).mp (subtype_refl _)
  exact ⟨(common_union_is_join ..).mpr ⟨subtype_trans first.1 two.1,subtype_trans last.1 two.2⟩,
    (common_union_is_join ..).mpr ⟨subtype_trans first.2 one.1,subtype_trans last.2 one.2⟩⟩

theorem inter_equivalent {a b c d : Ty} (first : Equivalent a c) (last : Equivalent b d) :
    Equivalent (.inter a b) (.inter c d) := by
  have one := (common_inter_is_meet a b (.inter a b)).mp (subtype_refl _)
  have two := (common_inter_is_meet c d (.inter c d)).mp (subtype_refl _)
  exact ⟨(common_inter_is_meet ..).mpr ⟨subtype_trans one.1 first.1,subtype_trans one.2 last.1⟩,
    (common_inter_is_meet ..).mpr ⟨subtype_trans two.1 first.2,subtype_trans two.2 last.2⟩⟩

theorem equations_congr (model : GeneralNominalCommonBridge.Assignment) (source : Nat)
    (first last : TyTerm Nat)
    (same : Equivalent (first.eval CommonNominalFullCarrier.model model) (last.eval CommonNominalFullCarrier.model model)) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model (equations source first) ↔
    PresenceNormalForm.All CommonNominalFullCarrier.model model (equations source last) := by
  rw [GeneralNominalCaptureMerges.equations_exact,GeneralNominalCaptureMerges.equations_exact]
  exact ⟨fun h => ⟨subtype_trans h.1 same.1,subtype_trans same.2 h.2⟩,
    fun h => ⟨subtype_trans h.1 same.2,subtype_trans same.1 h.2⟩⟩

/-- Allocation origins are stable even if the surrounding state/registry and
interval source syntax differ. Only the seed, invocation, declaration, binder,
and the endpoint denotations matter here. -/
theorem merges_iff (before after : GeneralNominalState.State) (oldRegistry newRegistry : Registry)
    (invocation : Nat) (declaration : Declaration) (binder : Nat)
    (inputs : declaration.inputNames = [binder]) (seed : before.seed = after.seed)
    (oldLeft oldRight newLeft newRight : Interval)
    (model : GeneralNominalCommonBridge.Assignment)
    (leftLo : Equivalent (model oldLeft.1).1 (model newLeft.1).1)
    (leftHi : Equivalent (model oldLeft.2).1 (model newLeft.2).1)
    (rightLo : Equivalent (model oldRight.1).1 (model newRight.1).1)
    (rightHi : Equivalent (model oldRight.2).1 (model newRight.2).1) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges before oldRegistry invocation declaration [(binder,oldLeft),(binder,oldRight)]) ↔
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges after newRegistry invocation declaration [(binder,newLeft),(binder,newRight)]) := by
  simp only [merges,inputs,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  simp only [occurrences,List.filter_cons,beq_self_eq_true,ite_true,List.filter_nil,List.map_cons,List.map_nil]
  simp only [capture,occurrences,List.filter_cons,beq_self_eq_true,ite_true,List.filter_nil,List.map_cons,List.map_nil,source,seed]
  rw [PresenceNormalForm.all_append,PresenceNormalForm.all_append]
  apply and_congr
  · apply equations_congr
    exact union_equivalent leftLo rightLo
  · apply equations_congr
    exact inter_equivalent leftHi rightHi

/-- Point bounds for the same observed nominal parameter determine equivalent
endpoints, even across different descriptor snapshots and source slots. -/
theorem point_bounds_equivalent (before after : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment)
    (oldModels : GeneralNominalState.Models before model) (newModels : GeneralNominalState.Models after model)
    (oldSlot : Fin before.base.slots) (newSlot : Fin after.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor before.base.slots)
    (newDescriptor : GeneralNominalState.Descriptor after.base.slots)
    (oldRecorded : before.nominals oldSlot = some oldDescriptor)
    (newRecorded : after.nominals newSlot = some newDescriptor)
    (index : Nat) (oldBounds : GeneralNominalInspection.Bounds before) (newBounds : GeneralNominalInspection.Bounds after)
    (oldParameter : oldDescriptor.arguments[index]? = some (.type oldBounds))
    (newParameter : newDescriptor.arguments[index]? = some (.type newBounds))
    (oldPoint : oldBounds.1 = oldBounds.2) (newPoint : newBounds.1 = newBounds.2)
    (source : before.base.source oldSlot = after.base.source newSlot)
    (name : oldDescriptor.declaration.name = newDescriptor.declaration.name) :
    Equivalent (model (before.base.source oldBounds.1)).1 (model (after.base.source newBounds.1)).1 := by
  have old := nominal_argument_bounds before model oldModels oldSlot oldDescriptor oldRecorded index oldBounds oldParameter
  have new := nominal_argument_bounds after model newModels newSlot newDescriptor newRecorded index newBounds newParameter
  obtain ⟨actual,seen⟩ := old.1
  have seen' : Observes model (.nominal (.source (after.base.source newSlot)) newDescriptor.declaration.name index) actual := by
    simpa [source,name] using seen
  have one := old.2 actual seen
  have two := new.2 actual seen'
  rw [← oldPoint] at one
  rw [← newPoint] at two
  exact ⟨subtype_trans one.1 two.2,subtype_trans two.1 one.2⟩

/-- A real earlier packet supplies the old allocation equations. If both
old and current binary descriptors are point-valued at the same observed
head, the current equations follow, not merely the fitting inequalities.
The source slots/endpoints and current registry may change. -/
theorem merges_after_steps (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
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
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges after.current.context.state registry packet.site.occurrence.identity packet.declaration
        (bindings after.current.context.state
          (GeneralNominalRecursiveCandidates.report after.current.context packet.declaration [(slot,slot)]))) := by
  have prior := GeneralNominalSupportSteps.steps_models path model valid
  have branch := prior.2.1 packet member
  change GeneralNominalRecursiveCandidates.BranchModels packet.registry packet.context packet.site.occurrence
    packet.declaration packet.checked packet.bounds model at branch
  rw [oldBounds] at branch
  have propagated := ((GeneralNominalState.extend_models ..).mp branch.1).1
  have parts := (propagate_models ..).mp propagated
  have first := point_bounds_equivalent packet.context.state after.current.context.state model parts.1 valid.1
    oldSlot slot oldDescriptor descriptor oldRecorded recorded 0 oldLeft left
    (by rw [oldParameters]; rfl) (by rw [parameters]; rfl) oldLeftPoint leftPoint source name
  have last := point_bounds_equivalent packet.context.state after.current.context.state model parts.1 valid.1
    oldSlot slot oldDescriptor descriptor oldRecorded recorded 1 oldRight right
    (by rw [oldParameters]; rfl) (by rw [parameters]; rfl) oldRightPoint rightPoint source name
  have oldMerge := parts.2.2
  rw [GeneralNominalBinaryCaptureFacts.report_exact packet.context packet.declaration oldSlot oldDescriptor
    oldRecorded binder binder oldLeft oldRight oldParameters oldQuery] at oldMerge
  rw [GeneralNominalBinaryCaptureFacts.report_exact after.current.context packet.declaration slot descriptor
    recorded binder binder left right parameters query]
  simp only [bindings,GeneralNominalBinaryCaptureFacts.captured,List.map_cons,List.map_nil] at oldMerge ⊢
  apply (merges_iff packet.context.state after.current.context.state packet.registry registry
    packet.site.occurrence.identity packet.declaration binder inputs seed _ _ _ _ model first ?_ last ?_).mp oldMerge
  · simpa only [← oldLeftPoint,← leftPoint] using first
  · simpa only [← oldRightPoint,← rightPoint] using last

end Yulang.GeneralNominalRepeatedMergeTransport
