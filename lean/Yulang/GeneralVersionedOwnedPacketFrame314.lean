import Yulang.GeneralVersionedOwnerEnvelope314

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
/-! Every semantic read in a stored versioned packet has an actual source
or owner. The proof examines the generated rows, not a notional public view. -/
namespace Yulang.GeneralVersionedOwnedPacketFrame314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedOwnerEnvelope314 (Envelope registered owned outputs)
open GeneralVersionedOwnedCoordinates314 (Owned variable_read where_target child_footprint input_endpoints output)
open GeneralNominalCenteredFrame179 (siteSources)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalVersionedFrame231 (binder capture)
open GeneralVersionedUnseenOwnerCenters313 (binder_origin)
open GeneralNominalVersionedPacketFrame236 (sources headSources captureSources childSources privateSources)
open GeneralVersionedHeadFromSharing313 (origins)
open GeneralNominalVersionedInstall232

theorem head_owned (p : Packet roles) (visible : p.declaration ∈ p.registry.declarations) :
    ∀ n ∈ headSources p, Owned p n := by
  have old (n : Nat) (h : n ∈ GeneralNominalState.sources p.context.state) : Owned p n := .inl h
  have reserved (n : Nat) (h : n ∈ GeneralVersionedInstallDomain313.reserve p) : Owned p n := by
    obtain ⟨key,joined,equal⟩ := List.mem_map.mp h
    exact .inr ⟨key,GeneralVersionedInstallDomain313.reserve_owner p (equal.symm ▸ h),equal⟩
  intro n h
  rcases List.mem_append.mp h with head|other
  · have rawPrivate := GeneralNominalSemanticRawFrame236.contained _ head
    have same (id : Nat) (item : id ∈ GeneralNominalState.sources (GeneralNominalVersionedPlans231.privateState p)) :
        id ∈ GeneralVersionedInstallDomain313.pool p := by
      apply GeneralNominalAllocationSupport.extend_sources _ [] _
        ?_ (by intro _ no; cases no) ?_ item
      · refine GeneralNominalAllocationSupport.extend_sources p.context.state (GeneralVersionedInstallDomain313.reserve p) _ (fun _ h => List.mem_append_left _ h)
          (fun _ h => List.mem_append_right _ h) ?_
        intro atom present
        rcases List.mem_append.mp present with cross|merges
        · exact GeneralNominalAllocationSupport.cross_sources (GeneralVersionedInstallDomain313.extension_endpoints p) atom cross
        · exact GeneralVersionedInstallDomain313.merge_atom p visible atom merges
      · exact fun atom member => GeneralNominalAllocationSupport.checks_sources _ _
          (fun _ m => List.mem_append_left _ m) atom member
    exact (List.mem_append.mp (same n rawPrivate)).elim (old n) (reserved n)
  · exact old n (GeneralNominalSemanticRawFrame236.contained _ (GeneralNominalSemanticRawFrame236.report_sources_subset p.context p.declaration p.bounds other))

theorem roots {s : State roles} {p : Plan roles} (actual : Reachable registry root s)
    (input : p.input ∈ s.core.sites) :
    ∀ n ∈ origins p, Envelope s n := by
  apply GeneralVersionedSchemaOrigins313.centers p (Envelope s) (.inl (Nat.zero_le _))
  intro i
  exact registered actual p.input input _
    (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩)

theorem schema {s : State roles} {p : Plan roles} (actual : Reachable registry root s)
    (stored : p ∈ s.plans) (input : p.input ∈ s.core.sites) :
    ∀ n ∈ GeneralNominalVersionedHeadFrame236.schemaSources p p.headSchema, Envelope s n := by
  intro n member
  rcases List.mem_append.mp member with test|vars
  · exact roots actual input n (List.mem_append_left _ test)
  · obtain ⟨use,found,inside⟩ := List.mem_flatMap.mp vars
    have mode := GeneralNominalHeadSchemaNames186.head_actual p use found
    simp only [GeneralNominalVersionedHeadFrame236.variableSources,mode,ite_true,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl|rfl
    · exact roots actual input _ (List.mem_append_right _ (List.mem_map.mpr ⟨use,found,rfl⟩))
    · exact owned actual stored (binder_origin p use.name)

theorem emitted_target {s : State roles} {p : Plan roles} (actual : Reachable registry root s)
    (stored : p ∈ s.plans) (registered : p.packet.site ∈ s.core.erased.current.sites)
    (eq : GeneralNominalCenteredHeadMatSchemas.Equation)
    (member : eq ∈ GeneralVersionedJointWrites312.equations p) :
    Envelope s eq.target := by
  rw [GeneralVersionedRootWrites312.separates] at member
  rcases List.mem_append.mp member with rootEq|localEq
  · obtain ⟨rq,visible,row⟩ := GeneralVersionedRootWrites312.from_request rootEq
    obtain ⟨out,reported,rqMatch⟩ := List.mem_flatMap.mp visible
    obtain ⟨rule,_,rfl⟩ := List.mem_map.mp rqMatch
    rw [GeneralVersionedRootWrites312.materialize_target row]
    exact outputs actual p.packet.site registered out reported
  · exact owned actual stored (where_target p eq localEq)

theorem expression_sources {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (registered : p.packet.site ∈ s.core.erased.current.sites)
    (rows : GeneralNominalCenteredHeadMatSchemas.Schema)
    (generated : rows.equations ⊆ GeneralVersionedJointWrites312.equations p) :
    ∀ n ∈ GeneralNominalVersionedExpressionFrame236.schemaSources p rows, Envelope s n := by
  intro n member
  obtain ⟨eq,found,foot⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp foot with rfl|read
  · exact emitted_target actual stored registered eq (generated found)
  · obtain ⟨entry,_,rfl⟩ := List.mem_map.mp read
    exact owned actual stored (variable_read p entry.1 entry.2)

theorem stored_sources {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (stored : p ∈ s.plans) :
    ∀ n ∈ sources p, Envelope s n := by
  have pRecorded : p.packet ∈ s.core.erased.current.packets := by
    rw [(GeneralNominalVersionedMixedChoiceHistory236.reachable actual).2]
    exact List.mem_map.mpr ⟨p,stored,rfl⟩
  have recorded := ((GeneralNominalVersionedMixedChoiceHistory236.reachable actual).1 _ pRecorded).2.1
  have input : p.input ∈ s.core.sites := (GeneralVersionedSiteOrigins312.reached actual).choose_spec.input p stored
  obtain ⟨effect,eff,h⟩ := GeneralVersionedSiteOrigins312.stored_effect actual stored
  have visible : p.packet.declaration ∈ p.packet.registry.declarations := by
    rw [← h]
    exact effect.frame.registry_eq ▸ effect.frame.visible
  intro n member
  simp only [sources,List.mem_append] at member
  rcases member with (((((head|site)|cap)|schemaReads)|emitted)|children)
  · exact owned actual stored (head_owned p.packet visible n head)
  · exact registered actual p.input input n site
  · obtain ⟨name,_,inside⟩ := List.mem_flatMap.mp cap
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl|rfl|rfl
    · exact owned actual stored (input_endpoints p.packet name).1
    · exact owned actual stored (input_endpoints p.packet name).2
    · exact owned actual stored (binder_origin p name)
  · exact schema actual stored input n schemaReads
  · exact expression_sources actual stored recorded _
      (fun _ h => GeneralVersionedJointWrites312.emitted_in p h) n emitted
  · obtain ⟨clause,_,foot⟩ := List.mem_flatMap.mp children
    rcases List.mem_append.mp foot with site|eq
    · exact owned actual stored (child_footprint p clause.val _ n site)
    · exact expression_sources actual stored recorded _
        (fun _ present => GeneralVersionedJointWrites312.child_in p clause.val clause.property _ present) n eq

end Yulang.GeneralVersionedOwnedPacketFrame314
