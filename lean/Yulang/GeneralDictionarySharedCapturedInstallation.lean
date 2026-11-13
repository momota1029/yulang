import Yulang.GeneralDictionarySharedCapturedInstallable

/-! The checked captured-input proposal has an actual Shared parent step from
initial source data and an inhabited resulting journal. This is only the parent
installation: neither emitted child is claimed installed or resumed. -/
namespace Yulang.GeneralDictionarySharedCapturedInstallation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralDictionarySharedOutputBinderScope
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedModel
open GeneralDictionarySharedCapturedGuards GeneralDictionarySharedCapturedInstallable
open GeneralDeclarationExamples (roles)
local instance : NeZero source.base.slots := ⟨by change 3 ≠ 0; omega⟩

theorem children : packet.children = [producer,consumer] := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canonical]
  simp [GeneralDeclarationDemands.emitAll,GeneralNominalFeedbackSites.clauseChild,
    GeneralNominalFeedbackSites.frame,packet,GeneralDictionaryEmissionPlans.occurrence,
    producer,GeneralDictionarySharedCapturedTargets.consumer,capturedProposal]

theorem guard : GeneralNominalSharedSteps.PacketGuard start packet [] := by
  have old : GeneralNominalSupportChoices.PacketGuard start packet [] :=
    ⟨⟨decisions.1,decisions.2.1,
      decisions.2.2 capturedProposal (by simp) rfl [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] located⟩,decisions⟩
  exact ⟨GeneralNominalValueSupport.source_packet start packet old,
    GeneralNominalSharedPositive.initial_decision context root root registry [] decisions,
    generation start,coherent⟩

noncomputable def after : GeneralNominalSupport.Tracked roles :=
  GeneralNominalSharedSteps.install start packet []

theorem step : GeneralNominalSharedSteps.Step registry root start after := by
  refine ⟨root,.root,.install packet [] enabled ?_ guard⟩
  intro committed
  have absent := committed.2 producer (by rw [children]; simp)
  cases absent

theorem formed : GeneralNominalSharedSteps.SourceFormed registry root after :=
  .update (.initial context initial_source) step

theorem inhabited : Models after.current model :=
  (GeneralNominalSharedSteps.install_models (state := start) (packet := packet)
    (support := []) rfl model).mpr
    ⟨(initial_models context root model).mpr source_models,branch_models⟩

theorem children_generated : Generated after.current root producer ∧ Generated after.current root consumer := by
  constructor
  all_goals apply Generated.child .root
  all_goals change _ ∈ [] ++ packet.children.map (fun child => (packet.site.occurrence,child))
  all_goals rw [children]
  all_goals simp [GeneralNominalDemandMerging.pointSite]

theorem captured_still_unknown : ¬ GeneralNominalState.Known after.current.context.state 2 := captured_unknown

theorem consumer_pending : GeneralNominalState.RootPending after.current.context.state consumer.demand := by
  refine ⟨⟨0,by decide +kernel⟩,?_⟩
  rw [consumer_input]
  exact captured_still_unknown

theorem producer_inputs : ∀ index, producer.demand.arguments index = (lo,hi) := by
  intro index
  have zero : index = ⟨0,by decide +kernel⟩ := Fin.ext (by have h : index.val < 1 := index.isLt; change index.val = 0; omega)
  subst index
  rfl

theorem producer_still_unknown : ¬ GeneralNominalState.Known after.current.context.state lo := by
  rintro ⟨slot,equal,_⟩
  have bound : (slot : Nat) ≤ 2 := by have := slot.isLt; change slot.val < 3 at this; omega
  exact lo_fresh slot.val bound equal.symm

theorem producer_pending : GeneralNominalState.RootPending after.current.context.state producer.demand := by
  refine ⟨⟨0,by decide +kernel⟩,?_⟩
  rw [producer_inputs]
  exact producer_still_unknown

/-- The initial parent supplies semantic shape constraints even though no
base slot for its fresh producer endpoint has yet been added. -/
theorem producer_shape (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current assignment) :
    Test.Holds (.nominal 0 1) (assignment lo).1 ∧
    Test.Holds (.nominal 0 1) (assignment hi).1 := by
  have parent := valid.2.1 packet (by simp [after,GeneralNominalSharedSteps.install,GeneralNominalFeedbackSites.install])
  have left : (.source lo,Test.nominal 0 1) ∈ (GeneralNominalPacketSupport.namedSchema packet).tests := by
    rw [schema_exact]; simp
  have right : (.source hi,Test.nominal 0 1) ∈ (GeneralNominalPacketSupport.namedSchema packet).tests := by
    rw [schema_exact]; simp
  exact ⟨(parent.2.2.1 _ left).2 _ (.source lo),(parent.2.2.1 _ right).2 _ (.source hi)⟩

theorem output_capture_equivalent (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current assignment) :
    CommonNominalFullCarrier.Equivalent (assignment target).1 (assignment 2).1 := by
  have parent := valid.2.1 packet (by simp [after,GeneralNominalSharedSteps.install,GeneralNominalFeedbackSites.install])
  exact output_equals_captured assignment parent.2.2

theorem reached_parent :
    GeneralNominalSharedSteps.Step registry root start after ∧
    Models after.current model ∧
    Generated after.current root producer ∧ Generated after.current root consumer ∧
    GeneralNominalState.RootPending after.current.context.state consumer.demand :=
  ⟨step,inhabited,children_generated.1,children_generated.2,consumer_pending⟩

end Yulang.GeneralDictionarySharedCapturedInstallation
