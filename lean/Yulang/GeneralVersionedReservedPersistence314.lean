import Yulang.GeneralVersionedSameOwnerChoice314

set_option backward.isDefEq.respectTransparency false
/-! Installing a frame commits its exact versioned reservation to the live
raw domain, and all later actual mixed actions preserve it. -/
namespace Yulang.GeneralVersionedReservedPersistence314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedTraceDomain313 (raw)
open GeneralVersionedInstallDomain313 (reserve)
open GeneralNominalVersionedMixedKernel234 (Step)

def Retained (s : State roles) : Prop :=
  ∀ p ∈ s.plans, reserve p.packet ⊆ raw s

theorem next {before after : State roles}
    (step : Step registry root before after) (earlier : Retained before) : Retained after := by
  have growth := GeneralVersionedHistoricalDomain313.growth step
  have keep (p : Plan roles) (found : p ∈ before.plans) : reserve p.packet ⊆ raw after :=
    fun _ listed => growth (earlier p found listed)
  obtain ⟨focus,generated,action⟩ := step
  unfold Retained
  cases action with
  | administrative action => cases action <;> exact keep
  | refresh | merge => exact keep
  | install effect enabled _ =>
    intro p member n seen
    rcases List.mem_cons.mp member with rfl|other
    · apply List.mem_append_left
      apply List.mem_append_right
      change n ∈ effect.plan.packet.context.state.reserved ++ reserve effect.plan.packet
      exact List.mem_append_right _ seen
    · exact keep p other seen

theorem reached {s : State roles} (actual : Reachable registry root s) : Retained s := by
  obtain ⟨start,⟨legacy,_,rfl⟩,steps⟩ := actual
  induction steps with
  | refl => intro p member; cases member
  | tail _ action ih => exact next action ih

end Yulang.GeneralVersionedReservedPersistence314
