import Yulang.GeneralVersionedSameOwnerChoice314

set_option backward.isDefEq.respectTransparency false
/-! Exact provenance for purpose-8 actual-binder coordinates. Capture
endpoints, compound allocations, raw reservations and output targets
cannot accidentally introduce them. -/
namespace Yulang.GeneralVersionedPrivateOrigins314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedTraceDomain313 (seed raw)
open GeneralNominalIdentities (Origin source source_identity source_above_seed)
open GeneralNominalAllocation (origin occurrences)
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedFrame231 (binder capture frame emittedCenter childSite)
open GeneralVersionedBinderTargets312 (actualName)
open GeneralNominalCenteredFrame179 (siteSources)

theorem distinct {a b : Origin} (tag : a.2.2.1 ≠ b.2.2.1) (seed : Nat) :
    source seed a ≠ source seed b :=
  fun same => tag (congrArg (fun k : Origin => k.2.2.1) ((source_identity _ _ _).mp same))

theorem raw_absent {s : State roles} {k : Origin}
    (actual : Reachable registry root s) (mode : k.2.2.1 = 8) :
    source (seed s) k ∉ raw s := by
  intro member
  rcases GeneralVersionedTraceDomain313.reached actual _ (List.mem_append_left _ member) with small|⟨p,stored,h⟩
  · exact Nat.not_lt_of_ge small (source_above_seed _ _)
  · have seedEq : p.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
    rw [← seedEq] at h
    have bound := GeneralVersionedInstallDomain313.reserve_purpose p.packet h
    omega

def Witness (s : State roles) (k : Origin) : Prop :=
  ∃ p ∈ s.plans, ∃ name, actualName p name = source (seed s) k ∧ binder p name = source (seed s) k

abbrev Explains (s : State roles) (k : Origin) (n : Nat) :=
  n = source (seed s) k → Witness s k

theorem historical_absent {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (tag : k.2.2.1 = 8) {n : Nat} (old : n ∈ GeneralNominalState.sources p.packet.context.state) :
    n ≠ source (seed s) k :=
  fun h => raw_absent actual tag (h ▸ GeneralVersionedHistoricalDomain313.reached actual p stored old)

theorem input_ne {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (tag : k.2.2.1 = 8) (name : Nat) :
    ((capture p.packet).inputs name).1 ≠ source (seed s) k ∧
    ((capture p.packet).inputs name).2 ≠ source (seed s) k := by
  have actualSeed : p.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
  have added (mode : Nat) (small : mode ≤ 1) :
      GeneralNominalAggregateVersion231.slot p.packet.context.state.seed
        p.packet.site.occurrence.identity p.packet.declaration.id mode name p.packet.bindings ≠ source (seed s) k := by
    rw [actualSeed]
    apply distinct
    change mode ≠ k.2.2.1
    omega
  have singleton (interval : GeneralSourceState.Interval) (exactPair : occurrences p.packet.bindings name = [interval]) :
      interval.1 ≠ source (seed s) k ∧ interval.2 ≠ source (seed s) k := by
    have within : interval ∈ occurrences p.packet.bindings name := exactPair ▸ List.mem_singleton_self _
    have ep := GeneralNominalAllocationSupport.occurrences_endpoints
      (GeneralNominalAllocationSupport.report_endpoints p.packet.context.state (GeneralNominalPacketSupport.report p.packet))
      name interval within
    exact ⟨historical_absent actual stored tag ep.1,historical_absent actual stored tag ep.2⟩
  unfold capture frame GeneralNominalVersionedAllocation231.capture
  cases here : occurrences p.packet.bindings name with
  | nil => simpa only [here] using And.intro (added 0 (by decide)) (added 1 (by decide))
  | cons a as =>
    cases as with
    | nil => simpa only [here] using singleton a here
    | cons b bs => simpa only [here] using And.intro (added 0 (by decide)) (added 1 (by decide))

theorem binder_witness {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (tag : k.2.2.1 = 8) (name : Nat) :
    Explains s k (binder p name) := by
  intro hit
  have current (h : binder p name = actualName p name) : Witness s k :=
    ⟨p,stored,name,h.symm.trans hit,hit⟩
  apply current
  unfold binder at hit ⊢
  by_cases out : name ∈ p.packet.declaration.outputNames
  · simp only [out,ite_true] at hit ⊢
    have actualSeed : p.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
    change source p.packet.context.state.seed (origin p.packet.site.occurrence.identity p.packet.declaration.id 2 name 0) = _ at hit
    rw [actualSeed] at hit
    exact False.elim (distinct (by change (2 : Nat) ≠ k.2.2.1; omega) _ hit)
  · simp only [out,ite_false] at hit ⊢
    by_cases pt : ((capture p.packet).inputs name).1 = ((capture p.packet).inputs name).2
    · simp only [pt,ite_true] at hit
      exact False.elim ((input_ne actual stored tag name).2 hit)
    · simp only [pt,ite_false]

theorem child {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (tag : k.2.2.1 = 8) (clause : Clause) (sig : clause.Signature roles) :
    ∀ n ∈ siteSources (childSite p clause sig), Explains s k n := by
  have actualSeed : p.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
  have interval (i : Fin (roles clause.role).arity) :
      ((childSite p clause sig).occurrence.demand.arguments i).1 ≠ source (seed s) k ∧
      ((childSite p clause sig).occurrence.demand.arguments i).2 ≠ source (seed s) k := by
    change let pat := clause.arguments[i.val]'(by rw [sig.1]; exact i.isLt)
      let bounds := GeneralDeclarationDemands.inputInterval (capture p.packet)
        (((frame p.packet).allocation p.packet.declaration.id clause).arguments i) pat
      bounds.1 ≠ source (seed s) k ∧ bounds.2 ≠ source (seed s) k
    dsimp only
    unfold GeneralDeclarationDemands.inputInterval
    split
    · exact input_ne actual stored tag _
    · constructor
      · change source p.packet.context.state.seed (origin p.packet.site.occurrence.identity p.packet.declaration.id 3 clause.id i.val) ≠ _
        rw [actualSeed]
        apply distinct
        change (3 : Nat) ≠ k.2.2.1
        omega
      · change source p.packet.context.state.seed (origin p.packet.site.occurrence.identity p.packet.declaration.id 4 clause.id i.val) ≠ _
        rw [actualSeed]
        apply distinct
        change (4 : Nat) ≠ k.2.2.1
        omega
  intro n h hit
  obtain ⟨row,present,within⟩ := List.mem_flatten.mp h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at within
  rcases within with rfl|rfl|rfl
  · exact False.elim ((interval i).1 hit)
  · exact False.elim ((interval i).2 hit)
  · change emittedCenter p clause.id i.val (clause.arguments[i.val]'(by rw [sig.1]; exact i.isLt)) = _ at hit
    unfold emittedCenter at hit
    split at hit
    · exact binder_witness actual stored tag _ hit
    · erw [actualSeed] at hit
      exact False.elim (distinct (by change (9 : Nat) ≠ k.2.2.1; omega) _ hit)

end Yulang.GeneralVersionedPrivateOrigins314
