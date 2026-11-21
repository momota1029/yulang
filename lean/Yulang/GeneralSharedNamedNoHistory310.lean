import Yulang.GeneralSharedNamedFinalFlow310
import Yulang.GeneralVersionedCheckedResidual310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27500
set_option maxHeartbeats 16000000
/-! The two selected receivers use the prospective branch of the soundness
analysis: their parent is recorded, but neither receiver has a packet in the
aliased class. Their actual current installability is derived, not assumed. -/
namespace Yulang.GeneralSharedNamedNoHistory310
open GeneralSharedNamedSource310 (root registry compiled checked leafBody)
open GeneralSharedNamedNodes310 (Node plan focus key links)
open GeneralSharedNamedSelection310 (actual_pick ready certificate)
open GeneralSharedNamedMerge310 (merged reached inhabited root_not_alias_child)
open GeneralSharedNamedCurrent310 (receiver receiver_request)
open GeneralSharedNamedLeaf310 (Side site named_requests)
open GeneralNominalVersionedJournal232 (Effect Models)
open GeneralNominalVersionedMixedKernel234 (Installable Committed)
open GeneralVersionedCheckedResidual310 (UnrecordedClass Represented)
open GeneralVersionedExplicitFromHolds310 (Explicit)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationExamples (roles)

def index : Side → Node | .low => .low | .high => .high

theorem outmatch (side : Side) : focus (index side) = (site side).occurrence := by cases side <;> rfl

noncomputable def effect (side : Side) : Effect roles :=
  GeneralNominalVersionedMixedFrameSelection235.effect_of_selected
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp (actual_pick (index side)))
    (GeneralSharedNamedNodes310.current_frame (index side)) (ready (index side))

theorem current_plan (side : Side) : (effect side).plan = receiver side := by cases side <;> rfl

theorem no_history (side : Side) :
    UnrecordedClass merged (site side).occurrence := by
  intro packet member alias
  change packet ∈ [GeneralSharedNamedPlan310.packet] at member
  cases List.mem_singleton.mp member
  exact GeneralSharedNamedLeafFrame310.invocations side (root_not_alias_child (.symm alias))

theorem represented (side : Side) : Represented merged (site side).occurrence := by
  apply GeneralVersionedCheckedResidual310.represented_of_same_requests
  intro output member
  rw [receiver_request side output member,named_requests]
  exact List.mem_singleton_self _

theorem explicit (side : Side) : Explicit (receiver side) (site side).occurrence.demand.outputs := by
  intro output member
  rw [named_requests] at member
  cases List.mem_singleton.mp member
  refine ⟨leafBody,List.mem_singleton_self _,rfl,.primitive (.scalar .int) [],?_⟩
  cases side <;> rfl

theorem compatible (side : Side) :
    GeneralNominalCycleSteps.ChoiceCompatible merged.core.erased.current (effect side).plan.packet := by
  apply GeneralVersionedCheckedResidual310.choice_fresh
  cases side
  · exact no_history .low
  · exact no_history .high

theorem installable (side : Side) : Installable compiled merged (effect side) := by
  cases side
  · exact GeneralVersionedCheckedResidual310.installable_of_explicit ⟨rfl,checked⟩ reached
      (effect .low) rfl rfl (actual_pick .low) (no_history .low) (explicit .low) (represented .low)
      ⟨_,inhabited,(certificate .low _ inhabited).packet,
        (GeneralSharedNamedCurrent310.receiver_classes .low _ inhabited).2⟩
  · exact GeneralVersionedCheckedResidual310.installable_of_explicit ⟨rfl,checked⟩ reached
      (effect .high) rfl rfl (actual_pick .high) (no_history .high) (explicit .high) (represented .high)
      ⟨_,inhabited,(certificate .high _ inhabited).packet,
        (GeneralSharedNamedCurrent310.receiver_classes .high _ inhabited).2⟩

theorem committed_without_packet (side : Side) : Committed merged (receiver side) := by
  refine ⟨?_,?_⟩
  · intro m valid
    exact ⟨(GeneralSharedNamedCurrent310.receiver_certificate side m valid).packet,
      GeneralSharedNamedCurrent310.receiver_classes side m valid⟩
  · intro child member
    change child ∈ GeneralNominalVersionedFrame231.children
      (GeneralNominalVersionedTransport231.extendedPacket [] GeneralSharedNamedMerge310.added []
        (GeneralSharedNamedLeaf310.packet side)) at member
    rw [GeneralNominalVersionedTransport231.children_eq,GeneralSharedNamedLeaf310.no_children] at member
    cases member

/-- A receiver can be certified and selected with no recorded packet. The
    positive result is not an assertion that the receiver was installed. -/
theorem witness (side : Side) :
    UnrecordedClass merged (site side).occurrence ∧
    Installable compiled merged (effect side) ∧ Committed merged (receiver side) :=
  ⟨no_history side,installable side,committed_without_packet side⟩

end Yulang.GeneralSharedNamedNoHistory310
