import Yulang.GeneralVersionedHighOrigins315

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
/-! Existing historical compiled packet rows and actual site centers do not
use the proposed endpoint namespaces. -/
namespace Yulang.GeneralVersionedHighPacket315
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedOwnerEnvelope314 (Envelope registered owned outputs)
open GeneralVersionedOwnedCoordinates314 (Owned variable_read where_target child_footprint input_endpoints output)
open GeneralNominalCenteredFrame179 (siteSources)
open GeneralNominalCenteredEmptyFrame179 (rawSiteSources)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalVersionedFrame231 (binder capture)
open GeneralVersionedHighOrigins315
open GeneralVersionedTraceDomain313 (seed)
open GeneralNominalIdentities (Origin source source_above_seed)
open GeneralVersionedUnseenOwnerCenters313 (binder_origin)
open GeneralNominalVersionedPacketFrame236 (sources headSources captureSources childSources privateSources)
open GeneralVersionedHeadFromSharing313 (origins)
open GeneralNominalVersionedInstall232

theorem registered {s : State roles} (actual : Reachable registry root s) {key : Origin} (tag : 9 < key.2.2.1) (site : Site roles)
    (recorded : site ∈ s.core.sites) :
    ∀ n ∈ siteSources site, Absent s key n := by
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
    have small : n ≤ seed s := by
      rw [seedEq]
      rcases within with rfl|rfl|rfl
      · exact formation.below_seed _ (formation.linked.1 i).1
      · exact formation.below_seed _ (formation.linked.1 i).2
      · exact formation.below_seed _ (formation.linked.1 i).1
    exact fun eq => Nat.not_lt_of_ge (eq ▸ small) (source_above_seed _ _)
  · obtain ⟨clause,_,sig,rfl⟩ := GeneralVersionedSiteOrigins312.emitted_origin born
    exact fun n h => child actual stored tag clause sig n h

theorem registered_raw {s : State roles} (actual : Reachable registry root s)
    {key : Origin} (tag : 9 < key.2.2.1) (site : GeneralNominalDemandMerging.Site roles) (recorded : site ∈ s.core.erased.current.sites) :
    ∀ n ∈ rawSiteSources site, Absent s key n := by
  obtain ⟨center,found,rfl⟩ := GeneralVersionedCurrentFrame312.raw_observed actual site recorded
  exact fun n member => registered actual tag center found n (GeneralVersionedOwnerEnvelope314.raw_site_subset center member)

theorem outputs_ne {s : State roles} {k : Origin} (actual : Reachable registry root s)
    (tag : 9 < k.2.2.1)
    (site : GeneralNominalDemandMerging.Site roles) (registered : site ∈ s.core.erased.current.sites)
    (rq : GeneralSourceState.Output) (listed : rq ∈ site.occurrence.demand.outputs) :
    rq.target ≠ source (seed s) k := by
  obtain ⟨center,found,rfl⟩ := GeneralVersionedCurrentFrame312.raw_observed actual site registered
  have target : rq.target ∈ GeneralNominalVersionedMixedAdministrative236.support s :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨center.observed,List.mem_map.mpr ⟨center,found,rfl⟩,
      List.mem_map.mpr ⟨rq,listed,rfl⟩⟩)
  intro hit
  rw [hit] at target
  rcases GeneralVersionedTraceDomain313.reached actual _ target with small|⟨p,stored,reserved⟩
  · exact Nat.not_lt_of_ge small (source_above_seed _ _)
  · have same : p.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
    rw [← same] at reserved
    have bound := GeneralVersionedInstallDomain313.reserve_purpose p.packet reserved
    omega

theorem packet_head {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (tag : 9 < k.2.2.1) (visible : p.packet.declaration ∈ p.packet.registry.declarations) :
    ∀ n ∈ headSources p.packet, n ≠ source (seed s) k := by
  intro n found hit
  rcases List.mem_append.mp found with privatePart|report
  · have rawPrivate := GeneralNominalSemanticRawFrame236.contained _ privatePart
    let pack := p.packet
    have openPool (id : Nat) (item : id ∈ GeneralNominalState.sources (GeneralNominalVersionedPlans231.privateState pack)) :
        id ∈ GeneralVersionedInstallDomain313.pool pack := by
      apply GeneralNominalAllocationSupport.extend_sources _ [] _
        ?_ (by intro _ no; cases no) ?_ item
      · refine GeneralNominalAllocationSupport.extend_sources pack.context.state (GeneralVersionedInstallDomain313.reserve pack) _ (fun _ h => List.mem_append_left _ h)
          (fun _ h => List.mem_append_right _ h) ?_
        intro atom present
        rcases List.mem_append.mp present with cross|merges
        · exact GeneralNominalAllocationSupport.cross_sources (GeneralVersionedInstallDomain313.extension_endpoints pack) atom cross
        · exact GeneralVersionedInstallDomain313.merge_atom pack visible atom merges
      · exact fun atom member => GeneralNominalAllocationSupport.checks_sources _ _
          (fun _ m => List.mem_append_left _ m) atom member
    rcases List.mem_append.mp (openPool n rawPrivate) with raw|reserved
    · exact historical_absent actual stored tag raw hit
    · have same : p.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
      rw [hit,← same] at reserved
      have bound := GeneralVersionedInstallDomain313.reserve_purpose p.packet reserved
      omega
  · exact historical_absent actual stored tag
      (GeneralNominalSemanticRawFrame236.contained _ (GeneralNominalSemanticRawFrame236.report_sources_subset p.packet.context p.packet.declaration p.packet.bounds report)) hit

theorem variable_read_explains {s : State roles} {p : Plan roles} {k : Origin} (actual : Reachable registry root s)
    (stored : p ∈ s.plans) (tag : 9 < k.2.2.1)
    (mode : GeneralNominalMaterialization.Mode) (name : Nat) :
    Absent s k (GeneralNominalVersionedExpressionFrame236.variableSource p mode name) := by
  unfold GeneralNominalVersionedExpressionFrame236.variableSource
  split
  · exact binder_absent actual stored tag _
  · cases mode
    · exact (input_ne actual stored tag name).1
    · exact (input_ne actual stored tag name).2
    · exact binder_absent actual stored tag _

theorem roots {s : State roles} {p : Plan roles} (actual : Reachable registry root s)
    {key : Origin} (tag : 9 < key.2.2.1) (input : p.input ∈ s.core.sites) :
    ∀ n ∈ origins p, Absent s key n := by
  apply GeneralVersionedSchemaOrigins313.centers p (Absent s key) (fun same => by have above := source_above_seed (seed s) key; omega)
  intro i
  exact registered actual tag p.input input _
    (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩)

theorem schema {s : State roles} {p : Plan roles} (actual : Reachable registry root s)
    {key : Origin} (tag : 9 < key.2.2.1) (stored : p ∈ s.plans) (input : p.input ∈ s.core.sites) :
    ∀ n ∈ GeneralNominalVersionedHeadFrame236.schemaSources p p.headSchema, Absent s key n := by
  intro n member
  rcases List.mem_append.mp member with test|vars
  · exact roots actual tag input n (List.mem_append_left _ test)
  · obtain ⟨use,found,inside⟩ := List.mem_flatMap.mp vars
    have mode := GeneralNominalHeadSchemaNames186.head_actual p use found
    simp only [GeneralNominalVersionedHeadFrame236.variableSources,mode,ite_true,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl|rfl
    · exact roots actual tag input _ (List.mem_append_right _ (List.mem_map.mpr ⟨use,found,rfl⟩))
    · exact binder_absent actual stored tag use.name

theorem emitted_target {s : State roles} {p : Plan roles} (actual : Reachable registry root s)
    {key : Origin} (tag : 9 < key.2.2.1) (stored : p ∈ s.plans) (registered : p.packet.site ∈ s.core.erased.current.sites)
    (eq : GeneralNominalCenteredHeadMatSchemas.Equation)
    (member : eq ∈ GeneralVersionedJointWrites312.equations p) :
    Absent s key eq.target := by
  rw [GeneralVersionedRootWrites312.separates] at member
  rcases List.mem_append.mp member with rootEq|localEq
  · obtain ⟨rq,visible,row⟩ := GeneralVersionedRootWrites312.from_request rootEq
    obtain ⟨out,reported,rqMatch⟩ := List.mem_flatMap.mp visible
    obtain ⟨rule,_,rfl⟩ := List.mem_map.mp rqMatch
    rw [GeneralVersionedRootWrites312.materialize_target row]
    exact outputs_ne actual tag p.packet.site registered out reported
  · rcases GeneralVersionedComputedRows313.classifies p eq localEq with taut|cell|computed
    · obtain ⟨entry,_,same⟩ := List.mem_map.mp (GeneralVersionedFirstInternal313.taut_reads p eq taut)
      rw [← same]
      exact variable_read_explains actual stored tag entry.1 entry.2
    · obtain ⟨c,_,pos,kind,_,_,_,validKind,hit,_⟩ := cell
      rw [hit]
      have same : p.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
      intro he
      unfold GeneralVersionedCompoundRows313.address at he
      change source p.packet.context.state.seed _ = _ at he
      rw [same] at he
      exact distinct (by change kind ≠ key.2.2.1; omega) _ he
    · obtain ⟨_,_,rule,_,_,_,hit,_⟩ := computed
      rw [hit]
      have same : p.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
      intro he
      unfold GeneralVersionedCompoundRows313.address at he
      change source p.packet.context.state.seed _ = _ at he
      rw [same] at he
      exact distinct (by change (5 : Nat) ≠ key.2.2.1; omega) _ he

theorem expression_sources {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) {key : Origin} (tag : 9 < key.2.2.1) (stored : p ∈ s.plans)
    (registered : p.packet.site ∈ s.core.erased.current.sites)
    (rows : GeneralNominalCenteredHeadMatSchemas.Schema)
    (generated : rows.equations ⊆ GeneralVersionedJointWrites312.equations p) :
    ∀ n ∈ GeneralNominalVersionedExpressionFrame236.schemaSources p rows, Absent s key n := by
  intro n member
  obtain ⟨eq,found,foot⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp foot with rfl|read
  · exact emitted_target actual tag stored registered eq (generated found)
  · obtain ⟨entry,_,rfl⟩ := List.mem_map.mp read
    exact variable_read_explains actual stored tag entry.1 entry.2

theorem stored_sources {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) {key : Origin} (tag : 9 < key.2.2.1) (stored : p ∈ s.plans) :
    ∀ n ∈ sources p, Absent s key n := by
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
  · exact packet_head actual stored tag visible n head
  · exact registered actual tag p.input input n site
  · obtain ⟨name,_,inside⟩ := List.mem_flatMap.mp cap
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl|rfl|rfl
    · exact (input_ne actual stored tag name).1
    · exact (input_ne actual stored tag name).2
    · exact binder_absent actual stored tag name
  · exact schema actual tag stored input n schemaReads
  · exact expression_sources actual tag stored recorded _
      (fun _ h => GeneralVersionedJointWrites312.emitted_in p h) n emitted
  · obtain ⟨clause,_,foot⟩ := List.mem_flatMap.mp children
    rcases List.mem_append.mp foot with site|eq
    · exact child actual stored tag clause.val _ n site
    · exact expression_sources actual tag stored recorded _
        (fun _ present => GeneralVersionedJointWrites312.child_in p clause.val clause.property _ present) n eq

end Yulang.GeneralVersionedHighPacket315
