import Yulang.GeneralVersionedReservedPersistence314
import Yulang.GeneralVersionedPrivateOrigins314

set_option backward.isDefEq.respectTransparency false
/-! If an aggregate coordinate of a checked declaration is present through
a genuine historical allocation/capture, the exact per-name version is
also present in the live raw domain. This is about addresses, not values. -/
namespace Yulang.GeneralVersionedAggregateOrigins314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedTraceDomain313 (seed raw context)
open GeneralNominalIdentities (Origin source source_identity)
open GeneralNominalAllocation (origin occurrences)
open GeneralNominalVersionedFrame231 (binder capture frame childSite emittedCenter)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalCenteredFrame179 (siteSources)
open GeneralVersionedPrivateOrigins314 (distinct)

structure Declared (registry : Registry) (k : Origin) : Prop where
  mode : k.2.2.1 = 0 ∨ k.2.2.1 = 1
  declared : ∃ d ∈ (Compiled registry).declarations, d.id = k.2.1 ∧ k.2.2.2.1 ∈ d.inputNames

abbrev RawIf (s : State roles) (k : Origin) (n : Nat) :=
  n = source (seed s) k → source (seed s) k ∈ raw s

theorem small {s : State roles} {k : Origin} {n : Nat} (h : n ≤ seed s) : RawIf s k n :=
  fun eq => False.elim (Nat.not_lt_of_ge (eq ▸ h) (GeneralNominalIdentities.source_above_seed _ _))

theorem historical {s : State roles} {p : Plan roles} {k : Origin} {n : Nat}
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (old : n ∈ GeneralNominalState.sources p.packet.context.state) : RawIf s k n :=
  fun h => h ▸ GeneralVersionedHistoricalDomain313.reached actual p stored old

theorem install_reserve {s : State roles} {p : Plan roles} {k : Origin} {n : Nat}
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (reserved : n ∈ GeneralVersionedInstallDomain313.reserve p.packet) : RawIf s k n :=
  fun h => h ▸ GeneralVersionedReservedPersistence314.reached actual p stored reserved

theorem wrong_kind {s : State roles} {k : Origin} {p : Plan roles} {j : Origin}
    (seedEq : p.packet.context.state.seed = seed s)
    (different : j.2.2.1 ≠ k.2.2.1) :
    RawIf s k (source p.packet.context.state.seed j) := by
  rw [seedEq]
  exact fun eq => False.elim (distinct different _ eq)

theorem stored_slot {s : State roles} {p : Plan roles} {k : Origin}
    (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (target : Declared registry k) (name : Nat) (mode : Nat)
    (polarity : mode = 0 ∨ mode = 1) :
    RawIf s k (GeneralNominalAggregateVersion231.slot p.packet.context.state.seed
      p.packet.site.occurrence.identity p.packet.declaration.id mode name p.packet.bindings) := by
  intro hit
  have seedEq : p.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
  have fields : GeneralNominalAggregateVersion231.key p.packet.site.occurrence.identity
      p.packet.declaration.id mode name p.packet.bindings = k := by
    apply (source_identity (seed s) _ _).mp
    unfold GeneralNominalAggregateVersion231.slot at hit
    rw [seedEq] at hit
    exact hit
  have packet : p.packet ∈ s.core.erased.current.packets := by
    rw [(GeneralNominalVersionedMixedChoiceHistory236.reachable actual).2]
    exact List.mem_map.mpr ⟨p,stored,rfl⟩
  have visible := GeneralNominalVersionedMixedChoiceHistory236.visible actual packet
  obtain ⟨d,inRegistry,dId,named⟩ := target.declared
  have sameKey := congrArg (fun x : Origin => x.2.1) fields
  have sameName : name = k.2.2.2.1 := congrArg (fun x : Origin => x.2.2.2.1) fields
  have declaration := GeneralDictionaryEmissionPlans.declaration_key_unique _
    (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2 _ _ visible inRegistry
    (sameKey.trans dId.symm)
  have used : name ∈ p.packet.declaration.inputNames := by rw [declaration,sameName]; exact named
  have regEq := (GeneralNominalVersionedMixedRegistry234.reachable actual).2.1 p stored
  have slots := GeneralNominalVersionedAllocation231.aggregate_reserved
    (state := p.packet.context.state) (root := p.packet.site.occurrence.identity) (bindings := p.packet.bindings)
    (regEq.symm ▸ visible) used
  rcases polarity with rfl|rfl
  · exact install_reserve actual stored slots.1 hit
  · exact install_reserve actual stored slots.2 hit

theorem input {s : State roles} {p : Plan roles} {k : Origin}
    (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (target : Declared registry k) (name : Nat) :
    RawIf s k ((capture p.packet).inputs name).1 ∧ RawIf s k ((capture p.packet).inputs name).2 := by
  have singleton (interval : GeneralSourceState.Interval) (same : occurrences p.packet.bindings name = [interval]) :
      RawIf s k interval.1 ∧ RawIf s k interval.2 := by
    have within : interval ∈ occurrences p.packet.bindings name := same ▸ List.mem_singleton_self _
    have ep := GeneralNominalAllocationSupport.occurrences_endpoints
      (GeneralNominalAllocationSupport.report_endpoints p.packet.context.state (GeneralNominalPacketSupport.report p.packet))
      name interval within
    exact ⟨historical actual stored ep.1,historical actual stored ep.2⟩
  have slots := And.intro (stored_slot checked actual stored target name 0 (.inl rfl))
    (stored_slot checked actual stored target name 1 (.inr rfl))
  unfold capture frame GeneralNominalVersionedAllocation231.capture
  cases here : occurrences p.packet.bindings name with
  | nil => simpa only [here] using slots
  | cons a as =>
    cases as with
    | nil => simpa only [here] using singleton a here
    | cons b bs => simpa only [here] using slots

theorem binder_of_domain {s : State roles} {p : Plan roles} {k : Origin}
    (seedEq : p.packet.context.state.seed = seed s)
    (inDomain : GeneralNominalState.sources p.packet.context.state ⊆ raw s)
    (target : k.2.2.1 = 0 ∨ k.2.2.1 = 1) (name : Nat) :
    RawIf s k (binder p name) := by
  unfold binder
  split
  · apply wrong_kind (p := p) (j := origin p.packet.site.occurrence.identity p.packet.declaration.id 2 name 0) seedEq
    change (2 : Nat) ≠ k.2.2.1
    omega
  · rename_i notOut
    have neither := GeneralNominalAggregateVersion231.distinct_purpose p.packet.context.state.seed
      p.packet.site.occurrence.identity p.packet.declaration.id 0 1 name p.packet.bindings p.packet.bindings (by decide)
    have freshCase : RawIf s k (source p.packet.context.state.seed
        (origin p.packet.site.occurrence.identity p.packet.declaration.id 8 name 0)) :=
      wrong_kind (p := p) seedEq (by change (8 : Nat) ≠ k.2.2.1; omega)
    have singleton (interval : GeneralSourceState.Interval) (same : occurrences p.packet.bindings name = [interval]) :
        RawIf s k interval.1 := by
      have within : interval ∈ occurrences p.packet.bindings name := same ▸ List.mem_singleton_self _
      have ep := GeneralNominalAllocationSupport.occurrences_endpoints
        (GeneralNominalAllocationSupport.report_endpoints p.packet.context.state (GeneralNominalPacketSupport.report p.packet))
        name interval within
      exact fun hit => hit ▸ inDomain ep.1
    unfold capture frame GeneralNominalVersionedAllocation231.capture
    cases here : occurrences p.packet.bindings name with
    | nil => simpa only [here,neither,ite_false] using (show RawIf s k (fresh p.packet.context.state.seed p.packet.site.occurrence.identity p.packet.declaration.id 8 name 0) from freshCase)
    | cons a as =>
      cases as with
      | nil =>
        simp only [here]
        split
        · exact singleton a here
        · exact freshCase
      | cons b bs => simpa only [here,neither,ite_false] using (show RawIf s k (fresh p.packet.context.state.seed p.packet.site.occurrence.identity p.packet.declaration.id 8 name 0) from freshCase)

theorem binder_raw {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (target : k.2.2.1 = 0 ∨ k.2.2.1 = 1) (name : Nat) : RawIf s k (binder p name) :=
  binder_of_domain (GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored)
    (GeneralVersionedHistoricalDomain313.reached actual p stored) target name

end Yulang.GeneralVersionedAggregateOrigins314
