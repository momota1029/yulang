import Yulang.GeneralVersionedHighPacket315

set_option backward.isDefEq.respectTransparency false
/-! An actual class-effect body reads the installed producer's own capture
or its recorded actual input; class targets come from historical registered sites. -/
namespace Yulang.GeneralVersionedHighClass315
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralVersionedHighOrigins315 (Absent binder_absent raw_absent)
open GeneralVersionedHighPacket315 (outputs_ne registered packet_head)
open GeneralNominalIdentities (Origin source source_above_seed)
open GeneralDictionaryDefault214ActualBodyFrame (bodySources classSources)
open GeneralVersionedUnseenOwnerCenters313 (binder_origin)
open GeneralVersionedTraceDomain313 (seed)

theorem default_origin {s : State roles} {p : Plan roles} {key : Origin} (actual : Reachable registry root s) (tag : 9 < key.2.2.1)
    (registeredCenter : p.input ∈ s.core.sites) (i : Nat) :
    Absent s key ((List.ofFn p.input.center)[i]?.getD 0) := by
  by_cases inside : i < (roles p.input.occurrence.demand.role).arity
  · simp only [List.getElem?_ofFn,inside,↓reduceDIte,Option.getD_some]
    apply registered actual tag p.input registeredCenter
    apply List.mem_flatten.mpr
    exact ⟨_,List.mem_ofFn.mpr ⟨⟨i,inside⟩,rfl⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩
  · simp only [List.getElem?_ofFn,inside,↓reduceDIte,Option.getD_none]
    exact fun same => by have above := source_above_seed (seed s) key; omega

theorem reads {s : State roles} {p : Plan roles}
    {key : Origin} (actual : Reachable registry root s) (tag : 9 < key.2.2.1) (stored : p ∈ s.plans)
    (input : p.input ∈ s.core.sites) (target : Nat) (allowed : Absent s key target)
    (body : GeneralDictionaryAssociatedProvenance.Body) :
    ∀ n ∈ bodySources p target body, Absent s key n := by
  intro n member
  cases body with
  | explicit eq =>
    rcases List.mem_cons.mp member with rfl|later
    · exact allowed
    · obtain ⟨name,_,rfl⟩ := List.mem_map.mp later
      rw [← GeneralNominalVersionedFrame231.binder_eq]
      exact binder_absent actual stored tag name
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
        exact default_origin actual tag input index
    · cases member

theorem class_frame {s : State roles} {p : Plan roles}
    {key : Origin} (actual : Reachable registry root s) (tag : 9 < key.2.2.1) (stored : p ∈ s.plans)
    (visibleSites : core.erased.current.sites ⊆ s.core.erased.current.sites) :
    ∀ n ∈ classSources core focus p, Absent s key n := by
  have input := (GeneralVersionedSiteOrigins312.reached actual).choose_spec.input p stored
  intro n listed
  obtain ⟨rq,found,within⟩ := List.mem_flatMap.mp listed
  obtain ⟨site,registered,_,requested⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp found
  have h : Absent s key rq.target := outputs_ne actual tag site (visibleSites registered) rq requested
  rcases List.mem_cons.mp within with rfl|source
  · exact h
  · obtain ⟨body,_,read⟩ := List.mem_flatMap.mp source
    exact reads actual tag stored input rq.target h body _ read

theorem effect_frame {s : State roles} {e : Effect roles}
    {key : Origin} (actual : Reachable registry root s) (tag : 9 < key.2.2.1) (recorded : e ∈ s.effects) :
    ∀ n ∈ GeneralNominalVersionedJournalFrame236.effectSources s e, Absent s key n := by
  have stored : e.plan ∈ s.plans := by
    rw [(GeneralNominalVersionedMixedPlanLedger235.reachable actual).1]
    exact List.mem_map.mpr ⟨e,recorded,rfl⟩
  have visible : e.plan.packet.declaration ∈ e.plan.packet.registry.declarations :=
    e.frame.registry_eq ▸ e.frame.visible
  intro n found
  rcases List.mem_append.mp found with first|last
  · rcases List.mem_append.mp first with head|snapshot
    · exact packet_head actual stored tag visible n head
    · exact class_frame actual tag stored (GeneralVersionedOwnedClassFrame314.snapshots actual e recorded) n snapshot
  · exact class_frame actual tag stored (fun _ h => h) n last

end Yulang.GeneralVersionedHighClass315
