import Yulang.GeneralVersionedReachableTests314
import Yulang.GeneralVersionedSemanticEntryChoice313

set_option backward.isDefEq.respectTransparency false
/-! A new numerical owner can install in the presence of arbitrary foreign
history. Its earlier alias peer need not have used the same read bounds or
have been a replay. Freshness here follows from the actual historical models. -/
namespace Yulang.GeneralVersionedNewOwnerHead314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSaturationState (Packet Alias)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralNominalVersionedDiagnostic232 (HeadEquations)
open GeneralVersionedUnseenBinder313 (Unseen protected_iff)
open GeneralVersionedTraceDomain313 (seed context)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralNominalIdentities (Origin source)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedSemanticPeer312 (reportPool protectedPool)
open GeneralVersionedHeadFromSharing313 (origins supportWithOrigins Equations)

def UnseenPacket (s : State roles) (p : Packet roles) : Prop :=
  ∀ prior ∈ s.plans, prior.packet.site.occurrence.identity ≠ p.site.occurrence.identity

theorem entry_address {p : Packet roles} {entry : GeneralNominalFiniteEquationRealization236.Entry}
    (found : entry ∈ packetEntries p) :
    ∃ key : Origin, key.1 = p.site.occurrence.identity ∧
      source p.context.state.seed key = entry.1 ∧ key.2.2.2.2 ≠ 0 := by
  obtain ⟨name,_,_,lo|hi⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp found
  · rw [lo]
    exact ⟨_,rfl,rfl,Nat.succ_ne_zero _⟩
  · rw [hi]
    exact ⟨_,rfl,rfl,Nat.succ_ne_zero _⟩

theorem entry_unprotected {s : State roles} {p : Packet roles}
    (actual : Reachable registry root s) (current : p.context = context s)
    (unseen : UnseenPacket s p) (entry) (found : entry ∈ packetEntries p) :
    entry.1 ∉ protectedPool p (sources s) := by
  obtain ⟨key,owner,target,_⟩ := entry_address found
  have id : source (seed s) key = entry.1 := by rw [current] at target; exact target
  have no : ∀ prior ∈ s.plans, prior.packet.site.occurrence.identity ≠ key.1 := by
    rw [owner]; exact unseen
  intro active
  rcases List.mem_append.mp active with inJournal|report
  · exact GeneralVersionedHistoricalSupport314.absent actual no (id.symm ▸ inJournal)
  · exact GeneralVersionedRawReportDomain313.unread actual current no (id.symm ▸ report)

theorem coverage {s : State roles} {p : Packet roles}
    (actual : Reachable registry root s) (current : p.context = context s)
    (unseen : UnseenPacket s p) :
    GeneralVersionedSemanticPeer312.Sufficient s p := by
  exact ⟨sources s,GeneralNominalVersionedModelSupport237.current s,
    fun entry found hit => False.elim (entry_unprotected actual current unseen entry found hit)⟩

theorem aggregate {s : State roles} {p : Plan roles} (actual : Reachable registry root s)
    (frame : Frame compiled s.core focus key p)
    (unseen : Unseen s p) (m : Assignment) : Equations p (sources s) m := by
  intro entry found joined
  apply False.elim
  rcases List.mem_append.mp joined with inside|report
  · rcases List.mem_append.mp inside with journal|origin
    · exact entry_unprotected actual frame.context_eq unseen entry found (List.mem_append_left _ journal)
    · obtain ⟨k,owner,target,_⟩ := entry_address found
      have id : source (seed s) k = entry.1 := by rw [frame.context_eq] at target; exact target
      have no : ∀ prior ∈ s.plans, prior.packet.site.occurrence.identity ≠ k.1 := by rw [owner]; exact unseen
      exact GeneralVersionedUnseenOwnerCenters313.head_origins_unowned actual no frame.center_recorded
        (id.symm ▸ origin)
  · exact entry_unprotected actual frame.context_eq unseen entry found (List.mem_append_right _ report)

theorem binder_outside {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (frame : Frame compiled s.core focus key p)
    (unseen : Unseen s p) (name : Nat) :
    GeneralVersionedBinderTargets312.actualName p name ∉ GeneralVersionedAliasHeadWrites312.pool p (sources s) := by
  intro found
  have old := (protected_iff actual frame unseen (sources s) name).mp found
  let key := GeneralNominalAllocation.origin p.packet.site.occurrence.identity p.packet.declaration.id 8 name 0
  have id : GeneralVersionedBinderTargets312.actualName p name = source (seed s) key := by
    change source p.packet.context.state.seed key = _; rw [frame.context_eq]
  exact GeneralVersionedHistoricalSupport314.absent (key := key) actual unseen (id ▸ old)

theorem head {s : State roles} {p : Plan roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (picked : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key p)
    (unseen : Unseen s p)
    (inhabited : ∃ m, Models s m) : ∃ m, Models s m ∧ HeadEquations p m := by
  apply GeneralVersionedHeadFromSharing313.selected_head checked actual picked frame inhabited
    (GeneralNominalVersionedModelSupport237.current s)
  intro m valid sharing
  refine ⟨GeneralVersionedReachableTests314.tests actual frame m valid,aggregate actual frame unseen m,?_⟩
  intro _ use present eq protectedBinder
  exact False.elim (binder_outside actual frame unseen use.name protectedBinder)

theorem choice {s : State roles} {p : Packet roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (picked : Local registry s p.site.occurrence (.selected p.declaration.id kids))
    (unseen : UnseenPacket s p)
    (inhabited : ∃ m, Models s m) :
    GeneralNominalCycleSteps.ChoiceCompatible s.core.erased.current p := by
  apply GeneralVersionedSemanticPeer312.choice checked actual picked inhabited
  intro prior stored alias actualCheck bounds located
  exact coverage actual rfl unseen

end Yulang.GeneralVersionedNewOwnerHead314
