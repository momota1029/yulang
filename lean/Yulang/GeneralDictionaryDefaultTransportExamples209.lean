import Yulang.GeneralDictionaryDefaultPointTransport209
import Yulang.GeneralDictionaryDefaultGap206Source
import Yulang.GeneralNominalPointCycleSource
import Yulang.GeneralNominalCenteredHeadMatHeadShape

/-! Semantic transport genuinely allows different center names. The negative
example only refutes dropping the point-argument hypothesis, not EvidenceNode. -/
namespace Yulang.GeneralDictionaryDefaultTransportExamples209
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatEffects CommonNominalFullCarrier
open GeneralDictionaryDefaultGap206Source

abbrev pointSite (name : Nat) : Site roles := ⟨root,fun _ => name⟩
abbrev pointPlan (name : Nat) : Plan roles := ⟨packet,pointSite name,rfl⟩

theorem point_holds (name : Nat) : (pointSite name).Holds model := by
  intro index
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem distinct_centers : (pointSite 1).center (0 : Fin 1) ≠ (pointSite 2).center (0 : Fin 1) := by decide

theorem point_default (name : Nat) :
    BodyHolds (pointPlan name) 0 model (.default 0 0 (.var 0)) := by
  apply (positional_default (pointPlan name) model (0 : Fin 1)).mpr
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem distinct_default_transport :
    BodyHolds (pointPlan 1) 0 model (.default 0 0 (.var 0)) ↔
      BodyHolds (pointPlan 2) 0 model (.default 0 0 (.var 0)) :=
  GeneralDictionaryDefaultPointTransport209.default_transport rfl rfl rfl (fun _ => rfl)
    (point_holds 1) (point_holds 2)

abbrev intervalRoot : Occurrence roles := ⟨101,⟨0,fun _ => (0,1),[],by simp⟩⟩
abbrev intervalSite (name : Nat) : Site roles := ⟨intervalRoot,fun _ => name⟩
abbrev intervalPacket : GeneralNominalSaturationState.Packet roles :=
  { packet with site := (intervalSite 0).observed }
abbrev intervalPlan (name : Nat) : Plan roles := ⟨intervalPacket,intervalSite name,rfl⟩
abbrev intervalModel : GeneralNominalCommonBridge.Assignment :=
  fun n => (if n = 0 then .bottom else .base .int,(model n).2)

theorem interval_bottom_holds : (intervalSite 0).Holds intervalModel := by
  intro index
  exact ⟨subtype_refl _,GeneralNominalPointCycleSource.bottom_le _⟩

theorem interval_int_holds : (intervalSite 1).Holds intervalModel := by
  intro index
  exact ⟨GeneralNominalPointCycleSource.bottom_le _,subtype_refl _⟩

theorem interval_not_point : ¬ ∀ index,
    (intervalRoot.demand.arguments index).1 = (intervalRoot.demand.arguments index).2 := by
  intro point
  exact Nat.zero_ne_one (point (0 : Fin 1))

theorem interval_default_bottom :
    BodyHolds (intervalPlan 0) 0 intervalModel (.default 0 0 (.var 0)) := by
  apply (positional_default (intervalPlan 0) intervalModel (0 : Fin 1)).mpr
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem interval_default_int_false :
    ¬ BodyHolds (intervalPlan 1) 0 intervalModel (.default 0 0 (.var 0)) := by
  intro holds
  have equal := (positional_default (intervalPlan 1) intervalModel (0 : Fin 1)).mp holds
  exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.scalar .int) equal

theorem point_premise_necessary :
    (intervalSite 0).Holds intervalModel ∧ (intervalSite 1).Holds intervalModel ∧
    BodyHolds (intervalPlan 0) 0 intervalModel (.default 0 0 (.var 0)) ∧
    ¬ BodyHolds (intervalPlan 1) 0 intervalModel (.default 0 0 (.var 0)) :=
  ⟨interval_bottom_holds,interval_int_holds,interval_default_bottom,interval_default_int_false⟩

end Yulang.GeneralDictionaryDefaultTransportExamples209
