import Yulang.GeneralDictionaryDefaultSemanticReplay209
import Yulang.GeneralDictionaryDefaultGap206State
import Yulang.GeneralDictionaryDefaultTransportExamples209

/-! Whole-packet semantic recentering on the scalar fixture. These are semantic
plans, not assertions that the new sites are recorded in the initial state. -/
namespace Yulang.GeneralDictionaryDefaultReplayExamples209
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryDefaultTransportExamples209
open GeneralDictionaryDefaultSemanticReplay209

 theorem total_at_center (name : Nat) :
    GeneralNominalCenteredHeadMatStepPackets.Holds (pointPlan name) model := by
  exact recenter_holds (historical := plan) (pointSite name) rfl (fun _ => rfl)
    (point_holds name) (GeneralDictionaryDefaultGap206State.total_packet model inhabited)

 theorem distinct_inputs : (pointPlan 1).input ≠ (pointPlan 2).input := by
  intro equal
  exact distinct_centers (congrArg (fun site => site.center (0 : Fin 1)) equal)

 theorem replay_one_to_two :
    GeneralNominalCenteredHeadMatStepPackets.Holds
      (recenter (pointPlan 1) (pointSite 2) rfl) model :=
  recenter_holds (historical := pointPlan 1) (pointSite 2) rfl (fun _ => rfl)
    (point_holds 2) (total_at_center 1)

 theorem distinct_total_packets :
    (pointPlan 1).input ≠ (pointPlan 2).input ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds (pointPlan 1) model ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds (pointPlan 2) model :=
  ⟨distinct_inputs,total_at_center 1,replay_one_to_two⟩

end Yulang.GeneralDictionaryDefaultReplayExamples209
