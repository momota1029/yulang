import Yulang.GeneralVersionedOwnedCoordinates314
import Yulang.GeneralVersionedHistoricalDomain313

set_option backward.isDefEq.respectTransparency false
/-! Every source/registered coordinate is explained by the original seed or
a genuine already installed numeric owner. No freshness assumption is made
about another version of an installed owner. -/
namespace Yulang.GeneralVersionedOwnerEnvelope314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedTraceDomain313 (seed raw context)
open GeneralNominalIdentities (Origin source source_identity source_above_seed)
open GeneralNominalState (sources)
open GeneralNominalCenteredFrame179 (siteSources)
open GeneralNominalCenteredEmptyFrame179 (rawSiteSources)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralVersionedOwnedCoordinates314 (Owned)

def Envelope (s : State roles) (n : Nat) : Prop :=
  n ≤ seed s ∨ ∃ p ∈ s.plans, ∃ k : Origin, k.1 = p.packet.site.occurrence.identity ∧ source (seed s) k = n

theorem never {s : State roles} {key : Origin}
    (unseen : ∀ p ∈ s.plans, p.packet.site.occurrence.identity ≠ key.1) :
    ¬ Envelope s (source (seed s) key) := by
  rintro (small | ⟨p,found,k,owner,equal⟩)
  · exact Nat.not_lt_of_ge small (source_above_seed _ _)
  · have eq := (source_identity _ _ _).mp equal
    exact unseen p found (owner.symm.trans (congrArg Prod.fst eq))

theorem raw_or_outputs {s : State roles} (actual : Reachable registry root s)
    (member : n ∈ GeneralNominalVersionedMixedAdministrative236.support s) : Envelope s n := by
  rcases GeneralVersionedTraceDomain313.reached actual n member with small|⟨p,found,reserved⟩
  · exact .inl small
  · obtain ⟨key,keyMem,equal⟩ := List.mem_map.mp reserved
    have owner := GeneralVersionedInstallDomain313.reserve_owner p.packet (equal.symm ▸ reserved)
    have same := GeneralNominalVersionedMixedSeedLedger237.reachable actual p found
    exact .inr ⟨p,found,key,owner,by rw [← show p.packet.context.state.seed = seed s from same]; exact equal⟩

theorem current {s : State roles} (actual : Reachable registry root s)
    (member : n ∈ raw s) : Envelope s n :=
  raw_or_outputs actual (List.mem_append_left _ member)

theorem history {s : State roles} {p : Plan roles} (actual : Reachable registry root s)
    (stored : p ∈ s.plans) (member : n ∈ sources p.packet.context.state) : Envelope s n :=
  current actual (GeneralVersionedHistoricalDomain313.reached actual p stored member)

theorem owned {s : State roles} {p : Plan roles} (actual : Reachable registry root s)
    (stored : p ∈ s.plans) (member : Owned p.packet n) : Envelope s n := by
  rcases member with old|⟨key,owner,eq⟩
  · exact history actual stored old
  · have same := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
    exact .inr ⟨p,stored,key,owner,by rw [← show p.packet.context.state.seed = seed s from same]; exact eq⟩

theorem initial_source_subset {s : State roles}
    (actual : Reachable registry root s) : sources s.core.erased.source.state ⊆ raw s := by
  obtain ⟨start,⟨legacy,⟨ctx,labels,formation,point,ground,cover,rfl⟩,rfl⟩,steps⟩ := actual
  have context := GeneralNominalVersionedMixedGrowth234.steps_source steps
  rw [context]
  intro id member
  induction steps with
  | refl => exact member
  | tail _ action ih => exact GeneralVersionedHistoricalDomain313.growth action (ih (GeneralNominalVersionedMixedGrowth234.steps_source ‹B4Target.Steps _ _ _›))

theorem registered {s : State roles} (actual : Reachable registry root s) (site : Site roles)
    (recorded : site ∈ s.core.sites) :
    ∀ n ∈ siteSources site, Envelope s n := by
  obtain ⟨initial,⟨legacy,⟨ctx,labels,formation,point,ground,coverage,rfl⟩,rfl⟩,steps⟩ := actual
  have actual : Reachable registry root s := ⟨_,⟨_,⟨ctx,labels,formation,point,ground,coverage,rfl⟩,rfl⟩,steps⟩
  rcases (GeneralVersionedSiteOrigins312.trace steps).origin site recorded with same|⟨p,stored,born⟩
  · subst site
    intro n found
    obtain ⟨row,inRow,within⟩ := List.mem_flatten.mp found
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp inRow
    change n ∈ [(root.demand.arguments i).1,(root.demand.arguments i).2,(rootSite ctx.state.seed root).center i] at within
    rw [point_center ctx.state.seed root i (point i)] at within
    simp only [List.mem_cons,List.not_mem_nil,or_false] at within
    have seedEq : seed s = ctx.state.seed := (GeneralNominalVersionedMixedGrowth234.steps steps).seed
    apply Or.inl
    rw [seedEq]
    rcases within with rfl|rfl|rfl
    · exact formation.below_seed _ (formation.linked.1 i).1
    · exact formation.below_seed _ (formation.linked.1 i).2
    · exact formation.below_seed _ (formation.linked.1 i).1
  · obtain ⟨clause,_,sig,rfl⟩ := GeneralVersionedSiteOrigins312.emitted_origin born
    exact fun n h => owned actual stored (GeneralVersionedOwnedCoordinates314.child_footprint p clause sig n h)

theorem raw_site_subset (site : Site roles) : rawSiteSources site.observed ⊆ siteSources site := by
  intro n h
  rcases List.mem_append.mp h with intervals|origins
  · obtain ⟨row,found,within⟩ := List.mem_flatten.mp intervals
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp found
    exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at within ⊢
      exact within.elim Or.inl (fun e => .inr (.inl e))⟩
  · obtain ⟨origin,observed,rfl⟩ := List.mem_map.mp origins
    obtain ⟨value,read,same⟩ := List.mem_filterMap.mp observed
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp read
    cases Option.some.inj same
    exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

theorem registered_raw {s : State roles} (actual : Reachable registry root s)
    (site : GeneralNominalDemandMerging.Site roles) (recorded : site ∈ s.core.erased.current.sites) :
    ∀ n ∈ rawSiteSources site, Envelope s n := by
  obtain ⟨center,found,rfl⟩ := GeneralVersionedCurrentFrame312.raw_observed actual site recorded
  exact fun n member => registered actual center found n (raw_site_subset center member)

theorem outputs {s : State roles} (actual : Reachable registry root s)
    (site : GeneralNominalDemandMerging.Site roles) (registered : site ∈ s.core.erased.current.sites)
    (rq : GeneralSourceState.Output) (listed : rq ∈ site.occurrence.demand.outputs) : Envelope s rq.target := by
  obtain ⟨center,found,rfl⟩ := GeneralVersionedCurrentFrame312.raw_observed actual site registered
  apply raw_or_outputs actual
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨center.observed,List.mem_map.mpr ⟨center,found,rfl⟩,
    List.mem_map.mpr ⟨rq,listed,rfl⟩⟩)

end Yulang.GeneralVersionedOwnerEnvelope314
