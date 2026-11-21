import Yulang.GeneralNominalVersionedTraceSupport237
import Yulang.GeneralVersionedInstallDomain313
import Yulang.GeneralNominalVersionedMixedProgressSplit236
import Yulang.GeneralNominalVersionedMixedSeedLedger237

set_option backward.isDefEq.respectTransparency false
/-! The actual mixed trace never creates a raw source ID except as a genuine
instruction-owned reservation. Refreshed aliases cannot mint owner IDs. -/
namespace Yulang.GeneralVersionedTraceDomain313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedAdministrative236 (Update support sources_bounded sites)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralVersionedInstallDomain313 (reserve replay_sources output_reserved reserve_owner)
open GeneralNominalState (sources)
open GeneralNominalIdentities (Origin source source_above_seed)
open GeneralNominalVersionedTraceSupport237 (Reachable append_steps)
open GeneralNominalAdministrativeProgress (outputs)

abbrev context (s : State roles) := s.core.erased.current.context
abbrev raw (s : State roles) := sources (context s).state
abbrev seed (s : State roles) := (context s).state.seed

def FromPlans (s : State roles) (n : Nat) : Prop :=
  n ≤ seed s ∨ ∃ p ∈ s.plans, n ∈ reserve p.packet

def Traced (s : State roles) : Prop :=
  ∀ n ∈ support s, FromPlans s n

theorem initial (formed : (boundary roles).Initial registry root s) : Traced s := by
  obtain ⟨legacy,⟨ctx,labels,formation,point,ground,cover,rfl⟩,rfl⟩ := formed
  intro n member
  apply Or.inl
  apply formation.below_seed
  rcases List.mem_append.mp member with raw | output
  · exact raw
  · obtain ⟨site,present,source⟩ := List.mem_flatMap.mp output
    have same := List.mem_singleton.mp present
    subst site
    obtain ⟨request,wanted,rfl⟩ := List.mem_map.mp source
    exact formation.linked.2 request wanted

theorem observation (path : Reachable registry root before)
    (action : Step (GeneralNominalCenteredHeadAllocEncoding.registry registry) root before after)
    (old : Traced before) : Traced after := by
  have growth := GeneralNominalVersionedMixedGrowth234.step action
  have transport {n} (known : FromPlans before n) : FromPlans after n := by
    rcases known with small|⟨p,history,hit⟩
    · apply Or.inl; change n ≤ (context after).state.seed; rw [growth.seed]; exact small
    · exact Or.inr ⟨p,growth.plans history,hit⟩
  rcases GeneralNominalVersionedMixedProgressSplit236.split path action with update|⟨effect,enabled,_,rfl⟩
  · intro n present
    rcases List.mem_append.mp present with fromRaw|fromSite
    · exact transport (old n (sources_bounded update fromRaw))
    · exact transport (old n (List.mem_append_right _ ((congrArg (fun xs => outputs (xs.map Site.observed)) (sites update)) ▸ fromSite)))
  · have view := effect.frame.context_eq.trans
      (congrArg (fun core => core.erased.current.context) enabled.snapshot_eq)
    have visible : effect.plan.packet.declaration ∈ effect.plan.packet.registry.declarations := by
      rw [effect.frame.registry_eq]; exact effect.frame.visible
    intro n present
    rcases List.mem_append.mp present with fromRaw|fromSite
    · rcases List.mem_append.mp (replay_sources effect.plan visible fromRaw) with oldSide|newSide
      · exact transport (old n (List.mem_append_left _ (view ▸ oldSide)))
      · exact Or.inr ⟨effect.plan,List.mem_cons_self ..,newSide⟩
    · change n ∈ outputs ((before.core.sites ++ GeneralNominalVersionedChildren232.emitted effect.plan).map Site.observed) at fromSite
      rw [List.map_append] at fromSite
      change n ∈ List.flatMap _ (_ ++ _) at fromSite
      rw [List.flatMap_append] at fromSite
      rcases List.mem_append.mp fromSite with earlier|later
      · exact transport (old n (List.mem_append_right _ earlier))
      · obtain ⟨site,member,requested⟩ := List.mem_flatMap.mp later
        obtain ⟨emitted,inEmitted,rfl⟩ := List.mem_map.mp member
        obtain ⟨request,inRequest,rfl⟩ := List.mem_map.mp requested
        exact Or.inr ⟨effect.plan,List.mem_cons_self ..,
          output_reserved effect.plan visible emitted inEmitted request inRequest⟩

theorem reached (actual : Reachable registry root s) : Traced s := by
  obtain ⟨start,formed,steps⟩ := actual
  induction steps with
  | refl => exact initial formed
  | tail prior action ih =>
    exact observation ⟨start,formed,prior⟩ action ih

theorem origin {s : State roles} {k : Origin}
    (actual : Reachable registry root s) (found : source (seed s) k ∈ support s) :
    ∃ p ∈ s.plans, p.packet.site.occurrence.identity = k.1 := by
  rcases reached actual _ found with small|⟨p,stored,known⟩
  · exact False.elim (Nat.not_lt_of_ge small (source_above_seed _ _))
  · have same : p.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
    rw [← same] at known
    exact ⟨p,stored,(reserve_owner p.packet known).symm⟩

theorem no_owner {s : State roles} {k : Origin}
    (actual : Reachable registry root s)
    (absent : ∀ p ∈ s.plans, p.packet.site.occurrence.identity ≠ k.1) :
    source (seed s) k ∉ support s :=
  fun h => let ⟨p,m,eq⟩ := origin actual h; absent p m eq

end Yulang.GeneralVersionedTraceDomain313
