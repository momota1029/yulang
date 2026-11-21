import Yulang.GeneralVersionedHistoricalHead314

set_option backward.isDefEq.respectTransparency false
/-! The exact current class-body footprint does not add an unrecorded
aggregate write. A body observes recorded input centers, raw point binders
or captured private/output coordinates in different namespaces. -/
namespace Yulang.GeneralVersionedAggregateClassNow314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralVersionedAggregateOrigins314 (Declared RawIf binder_of_domain)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralDictionaryDefault214ActualBodyFrame (bodySources classSources)
open GeneralNominalIdentities (Origin source)
open GeneralVersionedTraceDomain313 (seed raw)

theorem reads {s : State roles} {p : Plan roles} {k : Origin}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (targetKey : Declared registry k) (frame : Frame (Compiled registry) s.core focus key p)
    (target : Nat) (allowed : RawIf s k target)
    (body : GeneralDictionaryAssociatedProvenance.Body) :
    ∀ n ∈ bodySources p target body, RawIf s k n := by
  intro n member
  cases body with
  | explicit eq =>
    rcases List.mem_cons.mp member with rfl|later
    · exact allowed
    · obtain ⟨name,_,rfl⟩ := List.mem_map.mp later
      rw [← GeneralNominalVersionedFrame231.binder_eq]
      exact binder_of_domain (congrArg (fun c => c.state.seed) frame.context_eq)
        (by rw [frame.context_eq]; exact fun _ h => h) targetKey.mode name
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
        exact GeneralVersionedAggregateClass314.default_origin checked actual targetKey frame.center_recorded index
    · cases member

theorem current {s : State roles} {p : Plan roles} {k : Origin}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (targetKey : Declared registry k) (frame : Frame (Compiled registry) s.core focus key p) :
    ∀ n ∈ classSources s.core p.packet.site.occurrence p, RawIf s k n := by
  intro n listed
  obtain ⟨rq,found,within⟩ := List.mem_flatMap.mp listed
  obtain ⟨site,registered,_,requested⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp found
  have domain := GeneralVersionedAggregatePacket314.outputs_raw (k := k) actual site registered rq requested
  rcases List.mem_cons.mp within with rfl|source
  · exact domain
  · obtain ⟨body,_,read⟩ := List.mem_flatMap.mp source
    exact reads checked actual targetKey frame rq.target domain body _ read

theorem ledger {s : State roles} {p : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key p) (valid : Models s m) :
    IdCovered (GeneralNominalVersionedSupportedCompletion237.pool (sources s) s p) s p.packet := by
  intro row listed used
  have exactHistory := GeneralVersionedHistoricalHead314.ledger checked actual selected frame valid
  simp only [GeneralNominalVersionedSupportedCompletion237.pool,List.mem_append] at used
  rcases used with (journal|report)|classUsed
  · exact exactHistory row listed (List.mem_append_left _ journal)
  · exact exactHistory row listed (List.mem_append_right _ report)
  · obtain ⟨k,declared,address⟩ := GeneralVersionedAggregateJournal314.entry frame.context_eq frame.visible row listed
    have rawSeen : row.1 ∈ raw s := address ▸ current checked actual declared frame row.1 classUsed address.symm
    apply GeneralVersionedReservedVersion314.raw_history checked actual frame.context_eq _ row listed rawSeen
    intro prev stored sameOwner
    exact congrArg Declaration.id (GeneralVersionedHistoricalHead314.declaration checked actual selected frame valid stored sameOwner)

end Yulang.GeneralVersionedAggregateClassNow314
