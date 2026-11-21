import Yulang.GeneralVersionedAggregateClass314
import Yulang.GeneralVersionedReservedVersion314
import Yulang.GeneralVersionedObservedEssential313

set_option backward.isDefEq.respectTransparency false
/-! Full mixed Models on genuine source histories never read a private
coordinate belonging to a never-installed numerical owner. This includes
historical packet equations, live class bodies, and current observations. -/
namespace Yulang.GeneralVersionedAggregateJournal314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralVersionedAggregateOrigins314 (Declared RawIf small)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedAggregatePacket314 (registered registered_raw)
open GeneralNominalIdentities (Origin source source_identity source_above_seed)
open GeneralVersionedTraceDomain313 (seed raw context)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralDictionaryDefaultJournalSupport213 (journalSources)
open GeneralNominalVersionedTraceSiteSupport237 (Covered)
open GeneralVersionedTraceDomain313 (seed)
open GeneralVersionedEssentialSupport313 (Inert Essential)

theorem legacy {s : State roles} {k : Origin} (checked : (boundary roles).Checked registry) (actual : Reachable registry root s) (target : Declared registry k) :
    ∀ n ∈ journalSources s.legacy, RawIf s k n := by
  obtain ⟨emptyPlan,emptyEffect⟩ := GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty actual
  intro n member
  simp only [journalSources,List.mem_append] at member
  rcases member with (((((raw|base)|rawSite)|site)|past)|effect)
  · exact fun eq => eq ▸ GeneralDictionaryDefaultRawSupport213.subset _ raw
  · exact fun eq => eq ▸ GeneralVersionedOwnerEnvelope314.initial_source_subset actual
      (GeneralDictionaryDefaultRawSupport213.subset _ base)
  · obtain ⟨site,present,inside⟩ := List.mem_flatMap.mp rawSite
    exact registered_raw checked actual target site present n inside
  · obtain ⟨site,present,inside⟩ := List.mem_flatMap.mp site
    exact registered checked actual target site present n inside
  · rw [show s.legacy.core.plans = [] from emptyPlan] at past
    cases past
  · rw [emptyEffect] at effect
    cases effect

theorem all {s : State roles} {k : Origin} (checked : (boundary roles).Checked registry) (actual : Reachable registry root s) (target : Declared registry k) :
    ∀ n ∈ sources s, RawIf s k n := by
  intro n member
  rcases List.mem_append.mp member with first|last
  · rcases List.mem_append.mp first with old|stored
    · exact legacy checked actual target n old
    · obtain ⟨p,history,within⟩ := List.mem_flatMap.mp stored
      exact GeneralVersionedAggregatePacket314.stored_sources checked actual target history n within
  · obtain ⟨e,history,within⟩ := List.mem_flatMap.mp last
    exact GeneralVersionedAggregateClass314.effect_frame checked actual target history n within


open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralNominalVersionedAggregateRealization236 (member_iff)
open GeneralVersionedEssentialAggregates313 (Historical)

theorem entry {s : State roles} {p : Packet roles}
    (aligned : p.context = context s)
    (visible : p.declaration ∈ (Compiled registry).declarations)
    (row : GeneralNominalFiniteEquationRealization236.Entry) (listed : row ∈ packetEntries p) :
    ∃ k : Origin, Declared registry k ∧ source (seed s) k = row.1 := by
  obtain ⟨name,named,_,lo|hi⟩ := (member_iff ..).mp listed
  · refine ⟨GeneralNominalAggregateVersion231.key p.site.occurrence.identity p.declaration.id 0 name p.bindings,
      ⟨.inl rfl, p.declaration,visible,rfl,named⟩,?_⟩
    rw [lo]
    exact (congrArg (fun ctx => source ctx.state.seed _) aligned).symm
  · refine ⟨GeneralNominalAggregateVersion231.key p.site.occurrence.identity p.declaration.id 1 name p.bindings,
      ⟨.inr rfl, p.declaration,visible,rfl,named⟩,?_⟩
    rw [hi]
    exact (congrArg (fun ctx => source ctx.state.seed _) aligned).symm

theorem journal_subset {s : State roles} {p : Packet roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (aligned : p.context = context s)
    (visible : p.declaration ∈ (Compiled registry).declarations)
    (row : GeneralNominalFiniteEquationRealization236.Entry) (listed : row ∈ packetEntries p)
    (used : row.1 ∈ sources s) :
    row.1 ∈ raw s := by
  obtain ⟨k,known,address⟩ := entry aligned visible row listed
  exact address ▸ all checked actual known row.1 used address.symm

theorem full_support {s : State roles} {p : Packet roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (aligned : p.context = context s)
    (visible : p.declaration ∈ (Compiled registry).declarations)
    (keyConsistent : ∀ prev ∈ s.plans, prev.packet.site.occurrence.identity = p.site.occurrence.identity →
      prev.packet.declaration.id = p.declaration.id) :
    IdCovered (GeneralVersionedSemanticPeer312.protectedPool p (sources s)) s p := by
  intro row listed found
  apply GeneralVersionedReservedVersion314.raw_history checked actual aligned keyConsistent row listed
  rcases List.mem_append.mp found with journal|report
  · exact journal_subset checked actual aligned visible row listed journal
  · have rawRead := GeneralVersionedRawReportDomain313.raw_membership p report
    rw [aligned] at rawRead
    exact rawRead

end Yulang.GeneralVersionedAggregateJournal314
