import Yulang.GeneralVersionedHistoricalDomain313
import Yulang.GeneralVersionedSchemaOrigins313

set_option backward.isDefEq.respectTransparency false
/-! An actually registered center either reads historical raw source data
or uses a private coordinate of the plan which emitted it. An unseen owner
cannot occur in any such center or candidate head origins. -/
namespace Yulang.GeneralVersionedUnseenOwnerCenters313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDeclarationPatterns (normalize)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedTraceDomain313 (seed raw context)
open GeneralNominalVersionedFrame231 (binder capture emittedCenter childSite)
open GeneralNominalAllocation (occurrences)
open GeneralNominalIdentities (Origin source source_identity source_above_seed)
open GeneralVersionedHistoricalDomain313 (IncludesHistory)

def OldCenter (p : Plan roles) (n : Nat) : Prop :=
  n ∈ GeneralNominalState.sources p.packet.context.state ∨
    ∃ k : Origin, k.1 = p.packet.site.occurrence.identity ∧ source p.packet.context.state.seed k = n

theorem binder_origin (p : Plan roles) (name : Nat) : OldCenter p (binder p name) := by
  have privateName : OldCenter p (fresh p.packet.context.state.seed p.packet.site.occurrence.identity
      p.packet.declaration.id 8 name 0) := .inr ⟨_,rfl,rfl⟩
  have differing := GeneralNominalAggregateVersion231.distinct_purpose p.packet.context.state.seed
    p.packet.site.occurrence.identity p.packet.declaration.id 0 1 name p.packet.bindings p.packet.bindings (by decide)
  unfold binder
  split
  · exact .inr ⟨_,rfl,rfl⟩
  · unfold capture GeneralNominalVersionedFrame231.frame GeneralNominalVersionedAllocation231.capture
    cases found : occurrences p.packet.bindings name with
    | nil => simpa only [found,differing,ite_false] using privateName
    | cons first rest =>
      cases rest with
      | nil =>
        simp only [found]
        split
        · have known : first ∈ occurrences p.packet.bindings name := found ▸ List.mem_singleton_self _
          exact .inl ((GeneralNominalAllocationSupport.occurrences_endpoints
            (GeneralNominalAllocationSupport.report_endpoints p.packet.context.state (GeneralNominalPacketSupport.report p.packet))
            name first known).1)
        · exact privateName
      | cons b tail => simpa only [found,differing,ite_false] using privateName

theorem emitted_origin (p : Plan roles) (clause : Clause) (sig : clause.Signature roles)
    (pos : Fin (roles clause.role).arity) : OldCenter p ((childSite p clause sig).center pos) := by
  change OldCenter p (emittedCenter p clause.id pos.val (clause.arguments[pos.val]'(by rw [sig.1]; exact pos.isLt)))
  unfold emittedCenter
  split
  · exact binder_origin p _
  · exact .inr ⟨_,rfl,rfl⟩

theorem avoids {s : State roles} {key : Origin}
    (actual : Reachable registry root s)
    (absent : ∀ p ∈ s.plans, p.packet.site.occurrence.identity ≠ key.1)
    (site : Site roles) (registered : site ∈ s.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity) :
    site.center index ≠ source (seed s) key := by
  obtain ⟨initial,⟨legacy,⟨ctx,labels,formation,point,ground,coverage,rfl⟩,rfl⟩,steps⟩ := actual
  have actual : Reachable registry root s :=
    ⟨_,⟨_,⟨ctx,labels,formation,point,ground,coverage,rfl⟩,rfl⟩,steps⟩
  have seed_same : seed s = ctx.state.seed := (GeneralNominalVersionedMixedGrowth234.steps steps).seed
  rcases (GeneralVersionedSiteOrigins312.trace steps).origin site registered with own|⟨parent,present,born⟩
  · subst site
    rw [point_center ctx.state.seed root index (point index),seed_same]
    intro equal
    have small := formation.below_seed _ (formation.linked.1 index).1
    rw [equal] at small
    exact Nat.not_lt_of_ge small (source_above_seed _ _)
  · obtain ⟨clause,_,sig,rfl⟩ := GeneralVersionedSiteOrigins312.emitted_origin born
    intro equal
    rcases emitted_origin parent clause sig index with direct|⟨k,owner,same⟩
    · have remains := GeneralVersionedHistoricalDomain313.reached actual parent present direct
      rw [equal] at remains
      exact GeneralVersionedTraceDomain313.no_owner actual absent (List.mem_append_left _ remains)
    · have seedEq := GeneralNominalVersionedMixedSeedLedger237.reachable actual parent present
      change parent.packet.context.state.seed = seed s at seedEq
      have keys : k = key := (source_identity (seed s) _ _).mp (by rw [seedEq] at same; exact same.trans equal)
      exact absent parent present (owner.symm.trans (congrArg Prod.fst keys))

theorem head_origins_unowned {s : State roles} {p : Plan roles} {key : Origin}
    (actual : Reachable registry root s) (absent : ∀ prior ∈ s.plans, prior.packet.site.occurrence.identity ≠ key.1)
    (registered : p.input ∈ s.core.sites) :
    source (seed s) key ∉ GeneralVersionedHeadFromSharing313.origins p := by
  have outside : 0 ≠ source (seed s) key := by
    intro eq
    have less := source_above_seed (seed s) key
    omega
  exact fun member => (GeneralVersionedSchemaOrigins313.centers p (· ≠ source (seed s) key)
    outside (avoids actual absent p.input registered) _ member) rfl

end Yulang.GeneralVersionedUnseenOwnerCenters313
