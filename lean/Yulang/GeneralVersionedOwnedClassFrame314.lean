import Yulang.GeneralVersionedOwnedPacketFrame314

set_option backward.isDefEq.respectTransparency false
/-! An actual class-effect body reads the installed producer's own capture
or its recorded actual input; class targets come from historical registered sites. -/
namespace Yulang.GeneralVersionedOwnedClassFrame314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralVersionedOwnerEnvelope314 (Envelope outputs registered owned)
open GeneralDictionaryDefault214ActualBodyFrame (bodySources classSources)
open GeneralVersionedUnseenOwnerCenters313 (binder_origin)
open GeneralVersionedTraceDomain313 (seed)

def Retained (s : State roles) : Prop :=
  ∀ effect ∈ s.effects, effect.snapshot.erased.current.sites ⊆ s.core.erased.current.sites

theorem step {before after : State roles} (action : Step registry root before after)
    (old : Retained before) : Retained after := by
  have growth := (GeneralNominalVersionedMixedGrowth234.step action).legacy.rawSites
  obtain ⟨focus,generated,action⟩ := action
  have comes (p : Effect roles) (stor : p ∈ before.effects) :
      p.snapshot.erased.current.sites ⊆ after.core.erased.current.sites :=
    fun _ h => growth (old p stor h)
  cases action with
  | administrative update =>
    cases update <;> exact comes
  | refresh | merge => exact comes
  | install effect enabled novel =>
    intro p member
    rcases List.mem_cons.mp member with rfl|prior
    · rw [enabled.snapshot_eq]
      exact growth
    · exact comes p prior

theorem snapshots {s : State roles} (actual : Reachable registry root s) : Retained s := by
  obtain ⟨start,⟨legacy,_,rfl⟩,steps⟩ := actual
  induction steps with
  | refl => intro e member; cases member
  | tail _ action ih => exact step action ih

theorem default_origin {s : State roles} {p : Plan roles} (actual : Reachable registry root s)
    (registeredCenter : p.input ∈ s.core.sites) (i : Nat) :
    Envelope s ((List.ofFn p.input.center)[i]?.getD 0) := by
  by_cases inside : i < (roles p.input.occurrence.demand.role).arity
  · simp only [List.getElem?_ofFn,inside,↓reduceDIte,Option.getD_some]
    apply registered actual p.input registeredCenter
    apply List.mem_flatten.mpr
    exact ⟨_,List.mem_ofFn.mpr ⟨⟨i,inside⟩,rfl⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩
  · simp only [List.getElem?_ofFn,inside,↓reduceDIte,Option.getD_none]
    exact .inl (Nat.zero_le _)

theorem reads {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (input : p.input ∈ s.core.sites) (target : Nat) (allowed : Envelope s target)
    (body : GeneralDictionaryAssociatedProvenance.Body) :
    ∀ n ∈ bodySources p target body, Envelope s n := by
  intro n member
  cases body with
  | explicit eq =>
    rcases List.mem_cons.mp member with rfl|later
    · exact allowed
    · obtain ⟨name,_,rfl⟩ := List.mem_map.mp later
      rw [← GeneralNominalVersionedFrame231.binder_eq]
      exact owned actual stored (binder_origin p name)
  | default role name term =>
    change n ∈ GeneralDictionaryDefaultModeSupport213.schemaSources
      (GeneralDictionaryDefaultTotalFrame212.bodyResolve p (.default role name term))
      (GeneralNominalCenteredHeadMatEffects.bodySchema p target (.default role name term)) at member
    unfold GeneralNominalCenteredHeadMatEffects.bodySchema at member
    split at member
    · obtain ⟨eq,he,source⟩ := List.mem_flatMap.mp member
      cases List.mem_singleton.mp he
      rcases List.mem_cons.mp source with rfl|read
      · exact allowed
      · rw [GeneralDictionaryDefaultModeSupport213.actual_reads] at read
        obtain ⟨index,_,rfl⟩ := List.mem_map.mp read
        exact default_origin actual input index
    · cases member

theorem class_frame {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (visibleSites : core.erased.current.sites ⊆ s.core.erased.current.sites) :
    ∀ n ∈ classSources core focus p, Envelope s n := by
  have input := (GeneralVersionedSiteOrigins312.reached actual).choose_spec.input p stored
  intro n listed
  obtain ⟨rq,found,within⟩ := List.mem_flatMap.mp listed
  obtain ⟨site,registered,_,requested⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp found
  have h := outputs actual site (visibleSites registered) rq requested
  rcases List.mem_cons.mp within with rfl|source
  · exact h
  · obtain ⟨body,_,read⟩ := List.mem_flatMap.mp source
    exact reads actual stored input rq.target h body _ read

theorem effect_frame {s : State roles} {e : Effect roles}
    (actual : Reachable registry root s) (recorded : e ∈ s.effects) :
    ∀ n ∈ GeneralNominalVersionedJournalFrame236.effectSources s e, Envelope s n := by
  have stored : e.plan ∈ s.plans := by
    rw [(GeneralNominalVersionedMixedPlanLedger235.reachable actual).1]
    exact List.mem_map.mpr ⟨e,recorded,rfl⟩
  have visible : e.plan.packet.declaration ∈ e.plan.packet.registry.declarations :=
    e.frame.registry_eq ▸ e.frame.visible
  intro n found
  rcases List.mem_append.mp found with first|last
  · rcases List.mem_append.mp first with head|snapshot
    · exact owned actual stored (GeneralVersionedOwnedPacketFrame314.head_owned e.plan.packet visible n head)
    · exact class_frame actual stored (snapshots actual e recorded) n snapshot
  · exact class_frame actual stored (fun _ h => h) n last

end Yulang.GeneralVersionedOwnedClassFrame314
