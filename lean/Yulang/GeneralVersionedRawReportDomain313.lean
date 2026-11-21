import Yulang.GeneralVersionedTraceDomain313
import Yulang.GeneralVersionedEssentialAggregates313

set_option backward.isDefEq.respectTransparency false
/-! Prospective raw inspections read only actual base source slots, not
arbitrary raw ordinary mentions or bare reserved names. -/
namespace Yulang.GeneralVersionedRawReportDomain313
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedJournal232 (State)
open GeneralVersionedSemanticPeer312 (reportPool)
open GeneralNominalReportSupport237 (sources endpoints captureSources)
open GeneralNominalInspectionSupport237 (slot_member report_roots)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalVersionedMixedAdministrative236 (support)
open GeneralVersionedTraceDomain313 (seed context no_owner raw)
open GeneralNominalIdentities (Origin source)
open GeneralNominalVersionedTraceSupport237 (Reachable)

theorem reads_slots (p : Packet roles) : reportPool p ⊆ GeneralNominalInspectionSupport237.sources p.context.state := by
  intro n h
  have roots := report_roots p.context p.declaration p.bounds
  simp only [reportPool,sources,List.mem_append] at h
  rcases h with ((anchors|tests)|captures)|checked
  · obtain ⟨a,member,inside⟩ := List.mem_flatMap.mp anchors
    rcases List.mem_cons.mp inside with eq|inside
    · rw [eq]
      exact roots.1 a member
    · rcases List.mem_cons.mp inside with eq|inside
      · rw [eq]; exact slot_member _ a.2.1
      · rw [List.mem_singleton.mp inside]; exact slot_member _ a.2.2
  · obtain ⟨t,member,rfl⟩ := List.mem_map.mp tests
    exact roots.2.1 t member
  · obtain ⟨c,member,inside⟩ := List.mem_flatMap.mp captures
    rcases List.mem_append.mp inside with pair|origins
    · rcases List.mem_cons.mp pair with eq|inside
      · rw [eq]; exact slot_member _ c.bounds.1
      · rw [List.mem_singleton.mp inside]; exact slot_member _ c.bounds.2
    · obtain ⟨origin,seen,rfl⟩ := List.mem_map.mp origins
      exact roots.2.2 c member origin (Option.mem_toList.mp seen)
  · obtain ⟨bounds,_,inside⟩ := List.mem_flatMap.mp checked
    rcases List.mem_cons.mp inside with eq|inside
    · rw [eq]; exact slot_member _ bounds.1
    · rw [List.mem_singleton.mp inside]; exact slot_member _ bounds.2

theorem raw_membership (p : Packet roles) : reportPool p ⊆ GeneralNominalState.sources p.context.state := by
  intro n h
  obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp (reads_slots p h)
  exact GeneralNominalAllocationSupport.slot_source _ slot

theorem unread {s : State roles} {p : Packet roles} {k : Origin}
    (actual : Reachable registry root s) (current : p.context = context s)
    (freshOwner : ∀ past ∈ s.plans, past.packet.site.occurrence.identity ≠ k.1) :
    source (seed s) k ∉ reportPool p := by
  intro found
  have domain := raw_membership p found
  rw [current] at domain
  exact no_owner actual freshOwner (List.mem_append_left _ domain)

end Yulang.GeneralVersionedRawReportDomain313
