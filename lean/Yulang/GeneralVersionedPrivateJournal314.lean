import Yulang.GeneralVersionedPrivateClass314
import Yulang.GeneralVersionedBinderReuse312
import Yulang.GeneralVersionedObservedEssential313

set_option backward.isDefEq.respectTransparency false
/-! Full mixed Models on genuine source histories never read a private
coordinate belonging to a never-installed numerical owner. This includes
historical packet equations, live class bodies, and current observations. -/
namespace Yulang.GeneralVersionedPrivateJournal314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralVersionedPrivateOrigins314 (Explains Witness raw_absent)
open GeneralVersionedPrivatePacket314 (registered registered_raw)
open GeneralNominalIdentities (Origin source source_identity source_above_seed)
open GeneralVersionedTraceDomain313 (seed raw context)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralDictionaryDefaultJournalSupport213 (journalSources)
open GeneralNominalVersionedTraceSiteSupport237 (Covered)
open GeneralVersionedTraceDomain313 (seed)
open GeneralVersionedEssentialSupport313 (Inert Essential)

theorem legacy {s : State roles} {k : Origin} (actual : Reachable registry root s) (tag : k.2.2.1 = 8) :
    ∀ n ∈ journalSources s.legacy, Explains s k n := by
  obtain ⟨emptyPlan,emptyEffect⟩ := GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty actual
  intro n member
  simp only [journalSources,List.mem_append] at member
  rcases member with (((((raw|base)|rawSite)|site)|past)|effect)
  · exact fun eq => False.elim (raw_absent actual tag (eq ▸ GeneralDictionaryDefaultRawSupport213.subset _ raw))
  · exact fun eq => False.elim (raw_absent actual tag (eq ▸ GeneralVersionedOwnerEnvelope314.initial_source_subset actual
      (GeneralDictionaryDefaultRawSupport213.subset _ base)))
  · obtain ⟨site,present,inside⟩ := List.mem_flatMap.mp rawSite
    exact registered_raw actual tag site present n inside
  · obtain ⟨site,present,inside⟩ := List.mem_flatMap.mp site
    exact registered actual tag site present n inside
  · rw [show s.legacy.core.plans = [] from emptyPlan] at past
    cases past
  · rw [emptyEffect] at effect
    cases effect

theorem all {s : State roles} {k : Origin} (actual : Reachable registry root s) (tag : k.2.2.1 = 8) :
    ∀ n ∈ sources s, Explains s k n := by
  intro n member
  rcases List.mem_append.mp member with first|last
  · rcases List.mem_append.mp first with old|stored
    · exact legacy actual tag n old
    · obtain ⟨p,history,within⟩ := List.mem_flatMap.mp stored
      exact GeneralVersionedPrivatePacket314.stored_sources actual tag history n within
  · obtain ⟨e,history,within⟩ := List.mem_flatMap.mp last
    exact GeneralVersionedPrivateClass314.effect_frame actual tag history n within


open GeneralVersionedBinderTargets312 (actualName)
open GeneralNominalVersionedFrame231 (binder)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalAllocation (origin)
open GeneralVersionedHistoryEvidence310 (Compiled)

theorem prospective_head_absent {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (tag : k.2.2.1 = 8)
    (aligned : p.packet.context = context s)
    (visible : p.packet.declaration ∈ p.packet.registry.declarations) :
    source (seed s) k ∉ GeneralNominalVersionedResidualFrame237.headSources p.packet := by
  intro member
  rcases List.mem_append.mp member with atoms|report
  · rcases List.mem_append.mp (GeneralVersionedInstallDomain313.head_sources p.packet visible atoms) with current|reserve
    · rw [aligned] at current
      exact raw_absent actual tag current
    · have same : p.packet.context.state.seed = seed s := congrArg (fun c => c.state.seed) aligned
      rw [← same] at reserve
      have bound := GeneralVersionedInstallDomain313.reserve_purpose p.packet reserve
      omega
  · have current := GeneralVersionedRawReportDomain313.raw_membership p.packet report
    rw [aligned] at current
    exact raw_absent actual tag current

theorem prospective {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (tag : k.2.2.1 = 8)
    (frame : Frame (Compiled registry) s.core focus key p) :
    ∀ n ∈ GeneralVersionedAliasHeadWrites312.pool p (sources s), Explains s k n := by
  have visible : p.packet.declaration ∈ p.packet.registry.declarations := frame.registry_eq ▸ frame.visible
  have origins : ∀ n ∈ GeneralVersionedHeadFromSharing313.origins p, Explains s k n := by
    apply GeneralVersionedSchemaOrigins313.centers p (Explains s k)
    · exact fun same => False.elim (by have above := source_above_seed (seed s) k; omega)
    · intro i
      exact registered actual tag p.input frame.center_recorded _
        (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩)
  intro n member
  simp only [GeneralVersionedAliasHeadWrites312.pool,List.mem_append] at member
  rcases member with (((journal|head)|tests)|vars)
  · exact all actual tag n journal
  · exact fun eq => False.elim (prospective_head_absent actual tag frame.context_eq visible (eq ▸ head))
  · exact origins n (List.mem_append_left _ tests)
  · exact origins n (List.mem_append_right _ vars)

theorem matching {s : State roles} {p q : Plan roles} {a b : Nat}
    (actual : Reachable registry root s) (stored : q ∈ s.plans)
    (aligned : p.packet.context = context s)
    (same : actualName p a = actualName q b) :
    p.packet.site.occurrence.identity = q.packet.site.occurrence.identity ∧
    p.packet.declaration.id = q.packet.declaration.id ∧ a = b := by
  let first := origin p.packet.site.occurrence.identity p.packet.declaration.id 8 a 0
  let last := origin q.packet.site.occurrence.identity q.packet.declaration.id 8 b 0
  change source p.packet.context.state.seed first = source q.packet.context.state.seed last at same
  have old : q.packet.context.state.seed = seed s := GeneralNominalVersionedMixedSeedLedger237.reachable actual q stored
  rw [aligned,old] at same
  have matching := (source_identity (seed s) first last).mp same
  exact ⟨congrArg Prod.fst matching,
    congrArg (fun k : Origin => k.2.1) matching,congrArg (fun k : Origin => k.2.2.2.1) matching⟩

theorem owned {s : State roles} {p : Plan roles}
    (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (frame : Frame (Compiled registry) s.core focus key p) :
    GeneralVersionedBinderReuse312.Owned s p (sources s) := by
  intro use seen _ guarded
  let k := origin p.packet.site.occurrence.identity p.packet.declaration.id 8 use.name 0
  have id : actualName p use.name = source (seed s) k := by
    change source p.packet.context.state.seed k = _
    rw [frame.context_eq]
  obtain ⟨q,stored,name,fromActual,bound⟩ := prospective actual (k := k) rfl frame _ guarded id
  obtain ⟨owner,rule,rfl⟩ := matching actual stored frame.context_eq (id.trans fromActual.symm)
  have compile := GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked
  have qVisible : q.packet.declaration ∈ (Compiled registry).declarations := by
    have recorded : q.packet ∈ s.core.erased.current.packets := by
      rw [(GeneralNominalVersionedMixedChoiceHistory236.reachable actual).2]
      exact List.mem_map.mpr ⟨q,stored,rfl⟩
    exact GeneralNominalVersionedMixedChoiceHistory236.visible actual recorded
  have decl := GeneralDictionaryEmissionPlans.declaration_key_unique _ compile.2 _ _ frame.visible qVisible rule
  exact ⟨q,stored,owner.symm,decl.symm,(GeneralNominalVersionedFrame231.binder_eq q use.name).symm.trans (bound.trans id.symm)⟩

end Yulang.GeneralVersionedPrivateJournal314
