import Yulang.GeneralVersionedOwnedClassFrame314
import Yulang.GeneralVersionedObservedEssential313

set_option backward.isDefEq.respectTransparency false
/-! Full mixed Models on genuine source histories never read a private
coordinate belonging to a never-installed numerical owner. This includes
historical packet equations, live class bodies, and current observations. -/
namespace Yulang.GeneralVersionedHistoricalSupport314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralVersionedOwnerEnvelope314 (Envelope raw_or_outputs current registered registered_raw)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralDictionaryDefaultJournalSupport213 (journalSources)
open GeneralNominalVersionedTraceSiteSupport237 (Covered)
open GeneralVersionedTraceDomain313 (seed)
open GeneralVersionedEssentialSupport313 (Inert Essential)

theorem legacy {s : State roles} (actual : Reachable registry root s) :
    ∀ n ∈ journalSources s.legacy, Envelope s n := by
  obtain ⟨emptyPlan,emptyEffect⟩ := GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty actual
  intro n member
  simp only [journalSources,List.mem_append] at member
  rcases member with (((((raw|base)|rawSite)|site)|past)|effect)
  · exact current actual (GeneralDictionaryDefaultRawSupport213.subset _ raw)
  · exact current actual (GeneralVersionedOwnerEnvelope314.initial_source_subset actual
      (GeneralDictionaryDefaultRawSupport213.subset _ base))
  · obtain ⟨site,present,inside⟩ := List.mem_flatMap.mp rawSite
    exact registered_raw actual site present n inside
  · obtain ⟨site,present,inside⟩ := List.mem_flatMap.mp site
    exact registered actual site present n inside
  · rw [show s.legacy.core.plans = [] from emptyPlan] at past
    cases past
  · rw [emptyEffect] at effect
    cases effect

theorem all {s : State roles} (actual : Reachable registry root s) :
    ∀ n ∈ sources s, Envelope s n := by
  intro n member
  rcases List.mem_append.mp member with first|last
  · rcases List.mem_append.mp first with old|stored
    · exact legacy actual n old
    · obtain ⟨p,history,within⟩ := List.mem_flatMap.mp stored
      exact GeneralVersionedOwnedPacketFrame314.stored_sources actual history n within
  · obtain ⟨e,history,within⟩ := List.mem_flatMap.mp last
    exact GeneralVersionedOwnedClassFrame314.effect_frame actual history n within

theorem absent {s : State roles} {key : GeneralNominalIdentities.Origin}
    (actual : Reachable registry root s)
    (unseen : ∀ p ∈ s.plans, p.packet.site.occurrence.identity ≠ key.1) :
    GeneralNominalIdentities.source (seed s) key ∉ sources s :=
  fun member => GeneralVersionedOwnerEnvelope314.never unseen (all actual _ member)

theorem inert {s : State roles} {key : GeneralNominalIdentities.Origin}
    (actual : Reachable registry root s)
    (unseen : ∀ p ∈ s.plans, p.packet.site.occurrence.identity ≠ key.1) :
    Inert s (GeneralNominalIdentities.source (seed s) key) :=
  GeneralVersionedEssentialSupport313.outside (GeneralNominalVersionedModelSupport237.current s) (absent actual unseen)

theorem package {s : State roles} (actual : Reachable registry root s) :
    Support s (sources s) ∧ Covered s (sources s) ∧ ∀ n ∈ sources s, Envelope s n :=
  ⟨GeneralNominalVersionedModelSupport237.current s,
    GeneralNominalVersionedTraceSiteSupport237.current s,all actual⟩

end Yulang.GeneralVersionedHistoricalSupport314
