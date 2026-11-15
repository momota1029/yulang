import Yulang.GeneralDictionaryDefaultCollapsedCenters209
import Yulang.GeneralDictionaryDefaultTransportExamples209

/-! Syntactically different interval endpoints may denote equivalent values.
This positive case complements the noncollapsed negative interval regression. -/
namespace Yulang.GeneralDictionaryDefaultCollapsedExamples209
open GeneralDictionaryDefaultTransportExamples209
open GeneralDictionaryDefaultGap206Source
open GeneralNominalCenteredHeadMatEffects CommonNominalFullCarrier

theorem interval_holds (name : Nat) : (intervalSite name).Holds model := by
  intro index
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem interval_collapsed : ∀ index,
    Equivalent (model (intervalRoot.demand.arguments index).1).1
      (model (intervalRoot.demand.arguments index).2).1 := by
  intro index
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem nonpoint_centers (index : Nat) :
    Equivalent (model ((List.ofFn (intervalSite 0).center)[index]?.getD 0)).1
      (model ((List.ofFn (intervalSite 1).center)[index]?.getD 0)).1 :=
  GeneralDictionaryDefaultCollapsedCenters209.centers_equivalent _ _ rfl interval_collapsed
    (interval_holds 0) (interval_holds 1) index

theorem nonpoint_default_transport :
    BodyHolds (intervalPlan 0) 0 model (.default 0 0 (.var 0)) ↔
      BodyHolds (intervalPlan 1) 0 model (.default 0 0 (.var 0)) := by
  apply GeneralDictionaryDefaultBodyTransport209.body_transport
    (first := intervalPlan 0) (last := intervalPlan 1) rfl rfl
  · intro name; exact GeneralDictionaryDefaultExpression209.equivalent_refl _
  · exact nonpoint_centers

end Yulang.GeneralDictionaryDefaultCollapsedExamples209
