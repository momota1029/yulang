import Yulang.GeneralVersionedProspectiveNames314

set_option backward.isDefEq.respectTransparency false
/-! The exact prospective journal, head, class, and right-hand-side read
footprint omits every compound write of a never-installed owner. -/
namespace Yulang.GeneralVersionedProspectiveFootprint314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedOwnerEnvelope314 (Envelope current outputs)
open GeneralVersionedProspectiveNames314 (Read Actual ReadTag raw_read actual_binder rhs_reads weaken)
open GeneralVersionedTraceDomain313 (context seed)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralVersionedNewOwnerHead314 (entry_address entry_unprotected)
open GeneralVersionedUnseenBinder313 (Unseen)
open GeneralDictionaryDefault214ActualBodyFrame (bodySources classSources)
open GeneralVersionedJointWrites312 (protect inputNames)
open GeneralVersionedHeadFromSharing313 (origins)
open GeneralNominalIdentities (source source_identity)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)

theorem head_atom {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (aligned : p.packet.context = context s)
    (atom : PresenceNormalForm.Atom Nat) (member : atom ∈ GeneralNominalVersionedInstallation231.atoms p.packet) :
    ∀ n ∈ GeneralNominalState.atomSources atom, Read s p n := by
  have old : ∀ n ∈ GeneralNominalState.sources p.packet.context.state, Read s p n :=
    fun _ h => .inl (raw_read actual aligned h)
  have available := GeneralNominalAllocationSupport.report_endpoints p.packet.context.state (GeneralNominalPacketSupport.report p.packet)
  rcases List.mem_append.mp member with computed|checks
  · rcases List.mem_append.mp computed with cross|merge
    · exact fun _ h => old _ (GeneralNominalAllocationSupport.cross_sources available atom cross h)
    · rw [GeneralNominalVersionedAggregateEntries236.atoms_eq] at merge
      obtain ⟨entry,existsEntry,which⟩ := List.mem_flatMap.mp merge
      have atomDisj : ∀ n ∈ GeneralNominalState.atomSources atom, n = entry.1 ∨ n ∈ GeneralNominalState.typeSources entry.2 := by
        intro n h
        have found := GeneralNominalAllocationSupport.equation_sources entry.1 entry.2
          (pool := entry.1 :: GeneralNominalState.typeSources entry.2)
          (by simp) (fun _ h => List.mem_cons_of_mem _ h) atom which h
        exact List.mem_cons.mp found
      obtain ⟨name,_,_,lower|upper⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp existsEntry
      · intro n h
        rcases atomDisj n h with same|rhs
        · rw [same,lower]; exact .inr ⟨_,.inl rfl,rfl⟩
        · rw [lower] at rhs
          exact old _ (GeneralNominalAllocationSupport.lower_sources _
            (GeneralNominalAllocationSupport.occurrences_endpoints available name) rhs)
      · intro n h
        rcases atomDisj n h with same|rhs
        · rw [same,upper]; exact .inr ⟨_,.inr (.inl rfl),rfl⟩
        · rw [upper] at rhs
          exact old _ (GeneralNominalAllocationSupport.upper_sources _
            (GeneralNominalAllocationSupport.occurrences_endpoints available name) rhs)
  · exact fun _ h => old _ (GeneralNominalAllocationSupport.checks_sources _ _ (fun _ hx => hx) atom checks h)

theorem head_read {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (aligned : p.packet.context = context s) :
    ∀ n ∈ GeneralNominalVersionedResidualFrame237.headSources p.packet, Read s p n := by
  intro n found
  rcases List.mem_append.mp found with a|b
  · obtain ⟨atom,ha,inner⟩ := List.mem_flatMap.mp a
    exact head_atom actual aligned atom ha n inner
  · exact .inl (raw_read actual aligned (GeneralVersionedRawReportDomain313.raw_membership _ b))

theorem body_reads {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (aligned : p.packet.context = context s)
    (registered : p.input ∈ s.core.sites) (target : Nat) (valid : Envelope s target)
    (body : GeneralDictionaryAssociatedProvenance.Body) :
    ∀ n ∈ bodySources p target body, Actual s p n := by
  intro n member
  cases body with
  | explicit eq =>
    rcases List.mem_cons.mp member with rfl|rest
    · exact .inl valid
    · obtain ⟨name,_,rfl⟩ := List.mem_map.mp rest
      rw [← GeneralNominalVersionedFrame231.binder_eq]
      exact actual_binder actual aligned name
  | default role name term =>
    change n ∈ GeneralDictionaryDefaultModeSupport213.schemaSources
      (GeneralDictionaryDefaultTotalFrame212.bodyResolve p (.default role name term))
      (GeneralNominalCenteredHeadMatEffects.bodySchema p target (.default role name term)) at member
    unfold GeneralNominalCenteredHeadMatEffects.bodySchema at member
    split at member
    · obtain ⟨eq,he,read⟩ := List.mem_flatMap.mp member
      cases List.mem_singleton.mp he
      rcases List.mem_cons.mp read with rfl|r
      · exact .inl valid
      · rw [GeneralDictionaryDefaultModeSupport213.actual_reads] at r
        obtain ⟨index,_,rfl⟩ := List.mem_map.mp r
        exact .inl (GeneralVersionedOwnedClassFrame314.default_origin actual registered index)
    · cases member

theorem classes {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s)
    (frame : Frame compiled s.core focus key p) :
    ∀ n ∈ classSources s.core p.packet.site.occurrence p, Actual s p n := by
  intro n found
  obtain ⟨rq,whereRq,within⟩ := List.mem_flatMap.mp found
  obtain ⟨site,registered,_,requested⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp whereRq
  have mentioned := outputs actual site registered rq requested
  rcases List.mem_cons.mp within with rfl|body
  · exact .inl mentioned
  · obtain ⟨b,_,read⟩ := List.mem_flatMap.mp body
    exact body_reads actual frame.context_eq frame.center_recorded rq.target mentioned b _ read

theorem schema_reads {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (frame : Frame compiled s.core focus key p) :
    ∀ n ∈ GeneralNominalVersionedHeadFrame236.schemaSources p p.headSchema, Read s p n := by
  intro n h
  rcases List.mem_append.mp h with test|use
  · exact .inl (GeneralVersionedOwnedPacketFrame314.roots actual frame.center_recorded _
      (List.mem_append_left _ test))
  · obtain ⟨u,here,member⟩ := List.mem_flatMap.mp use
    have m := GeneralNominalHeadSchemaNames186.head_actual p u here
    simp only [GeneralNominalVersionedHeadFrame236.variableSources,m,ite_true,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact .inl (GeneralVersionedOwnedPacketFrame314.roots actual frame.center_recorded _
        (List.mem_append_right _ (List.mem_map.mpr ⟨u,here,rfl⟩)))
    · exact weaken (actual_binder actual frame.context_eq _)

theorem all {s : State roles} {e : Effect roles}
    (actual : Reachable registry root s) (frame : Frame compiled s.core focus key e.plan) :
    ∀ n ∈ protect s e (sources s), Read s e.plan n := by
  intro n h
  simp only [protect,List.mem_append] at h
  rcases h with ((((history|head)|schema)|live)|rhs)
  · exact .inl (GeneralVersionedHistoricalSupport314.all actual n history)
  · exact head_read actual frame.context_eq n head
  · exact schema_reads actual frame n schema
  · exact weaken (classes actual frame n live)
  · obtain ⟨row,_,inRow⟩ := List.mem_flatMap.mp rhs
    obtain ⟨entry,_,rfl⟩ := List.mem_map.mp inRow
    exact rhs_reads actual frame.context_eq entry.1 entry.2

theorem aggregate_class_free {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (frame : Frame compiled s.core focus key p)
    (unseen : Unseen s p) :
    IdCovered (GeneralNominalVersionedSupportedCompletion237.pool (sources s) s p) s p.packet := by
  intro entry found active
  apply False.elim
  rcases List.mem_append.mp active with old|live
  · exact entry_unprotected actual frame.context_eq unseen entry found old
  · have a := classes actual frame entry.1 live
    obtain ⟨k,owner,target,version⟩ := entry_address found
    rcases a with envelope|⟨key,tag,legacy,same⟩
    · have no : ∀ p ∈ s.plans, p.packet.site.occurrence.identity ≠ k.1 := by rw [owner]; exact unseen
      rw [← target,frame.context_eq] at envelope
      exact GeneralVersionedOwnerEnvelope314.never no envelope
    · have exactKey := (source_identity p.packet.context.state.seed _ _).mp (target.trans same.symm)
      exact version (exactKey.symm ▸ legacy)

end Yulang.GeneralVersionedProspectiveFootprint314
