import Yulang.GeneralVersionedAggregateOrigins314
import Yulang.GeneralVersionedPrivatePacket314

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
/-! Every semantic read in a stored versioned packet has an actual source
or owner. The proof examines the generated rows, not a notional public view. -/
namespace Yulang.GeneralVersionedAggregatePacket314
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
open GeneralVersionedAggregateOrigins314
open GeneralVersionedPrivateOrigins314 (distinct)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedFrame231 (frame emittedCenter childSite)
open GeneralNominalAllocation (origin)
open GeneralVersionedTraceDomain313 (raw)
open GeneralVersionedTraceDomain313 (seed)
open GeneralNominalIdentities (Origin source source_above_seed)
open GeneralVersionedUnseenOwnerCenters313 (binder_origin)
open GeneralNominalVersionedPacketFrame236 (sources headSources captureSources childSources privateSources)
open GeneralVersionedHeadFromSharing313 (origins)
open GeneralNominalVersionedInstall232

theorem child {s : State roles} {p : Plan roles} {k : Origin}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (target : Declared registry k) (clause : Clause) (sig : clause.Signature roles) :
    ∀ n ∈ siteSources (childSite p clause sig), RawIf s k n := by
  have actualSeed : p.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
  have interval (i : Fin (roles clause.role).arity) :
      RawIf s k ((childSite p clause sig).occurrence.demand.arguments i).1 ∧
      RawIf s k ((childSite p clause sig).occurrence.demand.arguments i).2 := by
    change let pat := clause.arguments[i.val]'(by rw [sig.1]; exact i.isLt)
      let bounds := GeneralDeclarationDemands.inputInterval (capture p.packet)
        (((frame p.packet).allocation p.packet.declaration.id clause).arguments i) pat
      RawIf s k bounds.1 ∧ RawIf s k bounds.2
    dsimp only
    unfold GeneralDeclarationDemands.inputInterval
    split
    · exact input checked actual stored target _
    · constructor
      · apply wrong_kind (p := p) (j := origin p.packet.site.occurrence.identity p.packet.declaration.id 3 clause.id i.val) actualSeed
        have mode := target.mode
        change (3 : Nat) ≠ k.2.2.1
        omega
      · apply wrong_kind (p := p) (j := origin p.packet.site.occurrence.identity p.packet.declaration.id 4 clause.id i.val) actualSeed
        have mode := target.mode
        change (4 : Nat) ≠ k.2.2.1
        omega
  intro n h hit
  obtain ⟨row,present,within⟩ := List.mem_flatten.mp h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at within
  rcases within with rfl|rfl|rfl
  · exact (interval i).1 hit
  · exact (interval i).2 hit
  · change emittedCenter p clause.id i.val (clause.arguments[i.val]'(by rw [sig.1]; exact i.isLt)) = _ at hit
    unfold emittedCenter at hit
    split at hit
    · exact binder_raw actual stored target.mode _ hit
    · erw [actualSeed] at hit
      have mode := target.mode
      exact False.elim (distinct (by change (9 : Nat) ≠ k.2.2.1; omega) _ hit)

theorem registered {s : State roles} (checked : (boundary roles).Checked registry) (actual : Reachable registry root s) {key : Origin} (target : Declared registry key) (site : Site roles)
    (recorded : site ∈ s.core.sites) :
    ∀ n ∈ siteSources site, RawIf s key n := by
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
    exact fun eq => False.elim (Nat.not_lt_of_ge (eq ▸ small) (source_above_seed _ _))
  · obtain ⟨clause,_,sig,rfl⟩ := GeneralVersionedSiteOrigins312.emitted_origin born
    exact fun n h => child checked actual stored target clause sig n h

theorem registered_raw {s : State roles} (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    {key : Origin} (target : Declared registry key) (site : GeneralNominalDemandMerging.Site roles) (recorded : site ∈ s.core.erased.current.sites) :
    ∀ n ∈ rawSiteSources site, RawIf s key n := by
  obtain ⟨center,found,rfl⟩ := GeneralVersionedCurrentFrame312.raw_observed actual site recorded
  exact fun n member => registered checked actual target center found n (GeneralVersionedOwnerEnvelope314.raw_site_subset center member)

theorem outputs_raw {s : State roles} {k : Origin} (actual : Reachable registry root s)
    (site : GeneralNominalDemandMerging.Site roles) (registered : site ∈ s.core.erased.current.sites)
    (rq : GeneralSourceState.Output) (listed : rq ∈ site.occurrence.demand.outputs) :
    RawIf s k rq.target := by
  obtain ⟨center,found,rfl⟩ := GeneralVersionedCurrentFrame312.raw_observed actual site registered
  have target : rq.target ∈ GeneralNominalVersionedMixedAdministrative236.support s :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨center.observed,List.mem_map.mpr ⟨center,found,rfl⟩,
      List.mem_map.mpr ⟨rq,listed,rfl⟩⟩)
  rcases GeneralVersionedTraceDomain313.reached actual _ target with low|⟨p,stored,reserved⟩
  · exact small low
  · exact install_reserve actual stored reserved

theorem packet_head_raw {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (stored : p ∈ s.plans)
    (visible : p.packet.declaration ∈ p.packet.registry.declarations) :
    ∀ n ∈ headSources p.packet, RawIf s k n := by
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
    · exact historical actual stored raw hit
    · exact install_reserve actual stored reserved hit
  · exact historical actual stored
      (GeneralNominalSemanticRawFrame236.contained _ (GeneralNominalSemanticRawFrame236.report_sources_subset p.packet.context p.packet.declaration p.packet.bounds report)) hit

theorem variable_read_explains {s : State roles} {p : Plan roles} {k : Origin} (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (stored : p ∈ s.plans) (target : Declared registry k)
    (mode : GeneralNominalMaterialization.Mode) (name : Nat) :
    RawIf s k (GeneralNominalVersionedExpressionFrame236.variableSource p mode name) := by
  unfold GeneralNominalVersionedExpressionFrame236.variableSource
  split
  · exact binder_raw actual stored target.mode _
  · cases mode
    · exact (input checked actual stored target name).1
    · exact (input checked actual stored target name).2
    · exact binder_raw actual stored target.mode _

theorem roots {s : State roles} {p : Plan roles} (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    {key : Origin} (target : Declared registry key) (input : p.input ∈ s.core.sites) :
    ∀ n ∈ origins p, RawIf s key n := by
  apply GeneralVersionedSchemaOrigins313.centers p (RawIf s key) (small (Nat.zero_le _))
  intro i
  exact registered checked actual target p.input input _
    (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩)

theorem schema {s : State roles} {p : Plan roles} (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    {key : Origin} (target : Declared registry key) (stored : p ∈ s.plans) (input : p.input ∈ s.core.sites) :
    ∀ n ∈ GeneralNominalVersionedHeadFrame236.schemaSources p p.headSchema, RawIf s key n := by
  intro n member
  rcases List.mem_append.mp member with test|vars
  · exact roots checked actual target input n (List.mem_append_left _ test)
  · obtain ⟨use,found,inside⟩ := List.mem_flatMap.mp vars
    have mode := GeneralNominalHeadSchemaNames186.head_actual p use found
    simp only [GeneralNominalVersionedHeadFrame236.variableSources,mode,ite_true,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl|rfl
    · exact roots checked actual target input _ (List.mem_append_right _ (List.mem_map.mpr ⟨use,found,rfl⟩))
    · exact binder_raw actual stored target.mode use.name

theorem emitted_target {s : State roles} {p : Plan roles} (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    {key : Origin} (target : Declared registry key) (stored : p ∈ s.plans) (registered : p.packet.site ∈ s.core.erased.current.sites)
    (eq : GeneralNominalCenteredHeadMatSchemas.Equation)
    (member : eq ∈ GeneralVersionedJointWrites312.equations p) :
    RawIf s key eq.target := by
  rw [GeneralVersionedRootWrites312.separates] at member
  rcases List.mem_append.mp member with rootEq|localEq
  · obtain ⟨rq,visible,row⟩ := GeneralVersionedRootWrites312.from_request rootEq
    obtain ⟨out,reported,rqMatch⟩ := List.mem_flatMap.mp visible
    obtain ⟨rule,_,rfl⟩ := List.mem_map.mp rqMatch
    rw [GeneralVersionedRootWrites312.materialize_target row]
    exact outputs_raw actual p.packet.site registered out reported
  · rcases GeneralVersionedComputedRows313.classifies p eq localEq with taut|cell|computed
    · obtain ⟨entry,_,same⟩ := List.mem_map.mp (GeneralVersionedFirstInternal313.taut_reads p eq taut)
      rw [← same]
      exact variable_read_explains checked actual stored target entry.1 entry.2
    · obtain ⟨c,_,pos,kind,_,_,_,validKind,hit,_⟩ := cell
      rw [hit]
      have same : p.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
      intro he
      unfold GeneralVersionedCompoundRows313.address at he
      change source p.packet.context.state.seed _ = _ at he
      rw [same] at he
      have mode := target.mode
      exact False.elim (distinct (by change kind ≠ key.2.2.1; omega) _ he)
    · obtain ⟨_,_,rule,_,_,_,hit,_⟩ := computed
      rw [hit]
      have same : p.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual p stored
      intro he
      unfold GeneralVersionedCompoundRows313.address at he
      change source p.packet.context.state.seed _ = _ at he
      rw [same] at he
      have mode := target.mode
      exact False.elim (distinct (by change (5 : Nat) ≠ key.2.2.1; omega) _ he)

theorem expression_sources {s : State roles} {p : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s) {key : Origin} (target : Declared registry key) (stored : p ∈ s.plans)
    (registered : p.packet.site ∈ s.core.erased.current.sites)
    (rows : GeneralNominalCenteredHeadMatSchemas.Schema)
    (generated : rows.equations ⊆ GeneralVersionedJointWrites312.equations p) :
    ∀ n ∈ GeneralNominalVersionedExpressionFrame236.schemaSources p rows, RawIf s key n := by
  intro n member
  obtain ⟨eq,found,foot⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp foot with rfl|read
  · exact emitted_target checked actual target stored registered eq (generated found)
  · obtain ⟨entry,_,rfl⟩ := List.mem_map.mp read
    exact variable_read_explains checked actual stored target entry.1 entry.2

theorem stored_sources {s : State roles} {p : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s) {key : Origin} (target : Declared registry key) (stored : p ∈ s.plans) :
    ∀ n ∈ sources p, RawIf s key n := by
  have pRecorded : p.packet ∈ s.core.erased.current.packets := by
    rw [(GeneralNominalVersionedMixedChoiceHistory236.reachable actual).2]
    exact List.mem_map.mpr ⟨p,stored,rfl⟩
  have recorded := ((GeneralNominalVersionedMixedChoiceHistory236.reachable actual).1 _ pRecorded).2.1
  have center : p.input ∈ s.core.sites := (GeneralVersionedSiteOrigins312.reached actual).choose_spec.input p stored
  obtain ⟨effect,eff,h⟩ := GeneralVersionedSiteOrigins312.stored_effect actual stored
  have visible : p.packet.declaration ∈ p.packet.registry.declarations := by
    rw [← h]
    exact effect.frame.registry_eq ▸ effect.frame.visible
  intro n member
  simp only [sources,List.mem_append] at member
  rcases member with (((((head|site)|cap)|schemaReads)|emitted)|children)
  · exact packet_head_raw actual stored visible n head
  · exact registered checked actual target p.input center n site
  · obtain ⟨name,_,inside⟩ := List.mem_flatMap.mp cap
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl|rfl|rfl
    · exact (input checked actual stored target name).1
    · exact (input checked actual stored target name).2
    · exact binder_raw actual stored target.mode name
  · exact schema checked actual target stored center n schemaReads
  · exact expression_sources checked actual target stored recorded _
      (fun _ h => GeneralVersionedJointWrites312.emitted_in p h) n emitted
  · obtain ⟨clause,_,foot⟩ := List.mem_flatMap.mp children
    rcases List.mem_append.mp foot with site|eq
    · exact child checked actual stored target clause.val _ n site
    · exact expression_sources checked actual target stored recorded _
        (fun _ present => GeneralVersionedJointWrites312.child_in p clause.val clause.property _ present) n eq

end Yulang.GeneralVersionedAggregatePacket314
