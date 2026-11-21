import Yulang.GeneralVersionedNewOwnerInstall314

set_option backward.isDefEq.respectTransparency false
/-! Actual install guards give stable declaration identity at a fixed numeric
owner in the historical ledger. Alias keys across different owners are
deliberately not claimed to have agreed at all earlier moments. -/
namespace Yulang.GeneralVersionedStoredOwnerKeys314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralVersionedHistoryEvidence310 (Compiled)

def SameKey (s : State roles) : Prop :=
  ∀ p ∈ s.plans, ∀ q ∈ s.plans, p.packet.site.occurrence.identity = q.packet.site.occurrence.identity →
    p.packet.declaration.id = q.packet.declaration.id

theorem next {before after : State roles}
    (actual : Reachable registry root before)
    (step : Step (Compiled registry) root before after)
    (older : SameKey before) : SameKey after := by
  rcases GeneralNominalVersionedMixedProgressSplit236.split actual step with admin|⟨effect,enabled,_,rfl⟩
  · unfold SameKey
    rw [GeneralNominalVersionedMixedProgressSplit236.administrative_plans admin]
    exact older
  · have old_key (p : Plan roles) (stored : p ∈ before.plans)
        (same : effect.plan.packet.site.occurrence.identity = p.packet.site.occurrence.identity) :
        p.packet.declaration.id = effect.plan.packet.declaration.id := by
      have packet : p.packet ∈ before.core.erased.current.packets := by
        rw [(GeneralNominalVersionedMixedChoiceHistory236.reachable actual).2]
        exact List.mem_map.mpr ⟨p,stored,rfl⟩
      exact (enabled.choice p.packet packet (same ▸ GeneralNominalSaturationState.Alias.refl _)).symm
    intro p hp q hq identity
    rcases List.mem_cons.mp hp with rfl|hp <;> rcases List.mem_cons.mp hq with rfl|hq
    · rfl
    · exact (old_key q hq identity).symm
    · exact old_key p hp identity.symm
    · exact older p hp q hq identity

theorem reached {s : State roles} (actual : Reachable registry root s) : SameKey s := by
  obtain ⟨start,formed,steps⟩ := actual
  induction steps with
  | refl =>
    obtain ⟨legacy,_,rfl⟩ := formed
    intro p present
    cases present
  | tail prior action ih =>
    exact next ⟨start,formed,prior⟩ action ih

theorem full_decl {s : State roles} {p q : Plan roles}
    (actual : Reachable registry root s)
    (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (pIn : p ∈ s.plans) (qIn : q ∈ s.plans)
    (same : p.packet.site.occurrence.identity = q.packet.site.occurrence.identity) :
    p.packet.declaration = q.packet.declaration := by
  have packetOf (t : Plan roles) (h : t ∈ s.plans) : t.packet ∈ s.core.erased.current.packets := by
    rw [(GeneralNominalVersionedMixedChoiceHistory236.reachable actual).2]
    exact List.mem_map.mpr ⟨t,h,rfl⟩
  exact GeneralDictionaryEmissionPlans.declaration_key_unique _
    (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2 _ _
    (GeneralNominalVersionedMixedChoiceHistory236.visible actual (packetOf p pIn))
    (GeneralNominalVersionedMixedChoiceHistory236.visible actual (packetOf q qIn))
    (reached actual p pIn q qIn same)

end Yulang.GeneralVersionedStoredOwnerKeys314
