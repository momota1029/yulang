import Yulang.GeneralVersionedPrivateWriteNames313

set_option backward.isDefEq.respectTransparency false
/-! Exact protected footprint and automatic ledger coverage before any
installation. Class requests are the real alias-class requests, not omitted
from the protected set, and default bodies read actual root centers. -/
namespace Yulang.GeneralVersionedFirstFootprint313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedTraceDomain313 (seed)
open GeneralVersionedBeforeFirstInstall313 (source_small source_slot_clean center_small)
open GeneralVersionedFirstHead313 (names raw_small origins_small)
open GeneralVersionedPrivateWriteNames313
open GeneralDictionaryDefault214ActualBodyFrame (bodySources classSources)
open GeneralNominalVersionedTraceSiteSupport237 (Covered)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralVersionedJointWrites312 (equations inputNames protect)

theorem center_get_small {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame compiled s.core focus key p) (n : Nat) :
    (List.ofFn p.input.center)[n]?.getD 0 ≤ seed s := by
  by_cases within : n < (roles p.input.occurrence.demand.role).arity
  · simpa only [List.getElem?_ofFn,within,↓reduceDIte,Option.getD_some] using center_small actual empty frame.center_recorded ⟨n,within⟩
  · simp [within]

theorem requests_small {s : State roles} (actual : Reachable registry root s) (empty : s.plans = [])
    {rq : GeneralSourceState.Output} (member : rq ∈ GeneralNominalCenteredHeadOutputs.requests s.core focus) :
    rq.target ≤ seed s := by
  obtain ⟨raw,hr,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  obtain ⟨site,hs,same⟩ := GeneralVersionedCurrentFrame312.raw_observed actual raw hr
  have found : rq.target ∈ GeneralNominalAdministrativeProgress.outputs (s.core.sites.map Site.observed) := by
    refine List.mem_flatMap.mpr ⟨site.observed,List.mem_map.mpr ⟨site,hs,rfl⟩,?_⟩
    exact List.mem_map.mpr ⟨rq,same ▸ within,rfl⟩
  exact source_slot_clean actual empty (List.mem_append_right _ found)

theorem body_reads {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p) (target : Nat) (small : target ≤ seed s)
    (body : GeneralDictionaryAssociatedProvenance.Body) :
    ∀ n ∈ bodySources p target body, ActualSafe p n := by
  intro n member
  cases body with
  | explicit eq =>
    rcases List.mem_cons.mp member with rfl|rest
    · exact .inl (by rw [frame.context_eq]; exact small)
    · obtain ⟨name,_,rfl⟩ := List.mem_map.mp rest
      rw [← GeneralNominalVersionedFrame231.binder_eq]
      exact actual_binder actual empty frame name
  | default role name term =>
    change n ∈ GeneralDictionaryDefaultModeSupport213.schemaSources
      (GeneralDictionaryDefaultTotalFrame212.bodyResolve p (.default role name term))
      (GeneralNominalCenteredHeadMatEffects.bodySchema p target (.default role name term)) at member
    unfold GeneralNominalCenteredHeadMatEffects.bodySchema at member
    split at member
    · rename_i expr translated
      obtain ⟨eq,he,source⟩ := List.mem_flatMap.mp member
      cases List.mem_singleton.mp he
      rcases List.mem_cons.mp source with rfl|read
      · exact .inl (by rw [frame.context_eq]; exact small)
      · rw [GeneralDictionaryDefaultModeSupport213.actual_reads] at read
        obtain ⟨index,_,rfl⟩ := List.mem_map.mp read
        exact .inl (by rw [frame.context_eq]; exact center_get_small actual empty frame index)
    · cases member

theorem classes {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p) :
    ∀ n ∈ classSources s.core p.packet.site.occurrence p, ActualSafe p n := by
  intro n found
  obtain ⟨rq,hr,within⟩ := List.mem_flatMap.mp found
  have small := requests_small actual empty hr
  rcases List.mem_cons.mp within with rfl|body
  · exact .inl (by rw [frame.context_eq]; exact small)
  · obtain ⟨choice,_,source⟩ := List.mem_flatMap.mp body
    exact body_reads actual empty frame rq.target small choice _ source

theorem schema_reads {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p) :
    ∀ n ∈ GeneralNominalVersionedHeadFrame236.schemaSources p p.headSchema, Safe p n := by
  intro n h
  rcases List.mem_append.mp h with test|use
  · exact transfer_small frame (origins_small actual empty frame _ (List.mem_append_left _ test))
  · obtain ⟨u,here,member⟩ := List.mem_flatMap.mp use
    have m := GeneralNominalHeadSchemaNames186.head_actual p u here
    simp only [GeneralNominalVersionedHeadFrame236.variableSources,m,ite_true,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · have within : GeneralNominalCenteredModelExtension.originSource u.origin ∈
          p.headSchema.variables.map (fun v => GeneralNominalCenteredModelExtension.originSource v.origin) :=
        List.mem_map.mpr ⟨u,here,rfl⟩
      exact transfer_small frame (origins_small actual empty frame _ (List.mem_append_right _ within))
    · exact binder_name actual empty frame _

theorem protected_names {s : State roles} {e : Effect roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key e.plan) :
    ∀ n ∈ protect s e (names s), Safe e.plan n := by
  intro n h
  simp only [protect,List.mem_append] at h
  rcases h with ((((a|b)|c)|d)|f)
  · exact transfer_small frame (source_small actual a)
  · exact head_read actual empty frame _ b
  · exact schema_reads actual empty frame _ c
  · exact actual_to_safe (classes actual empty frame _ d)
  · obtain ⟨eq,he,inEq⟩ := List.mem_flatMap.mp f
    obtain ⟨input,here,rfl⟩ := List.mem_map.mp inEq
    exact rhs_read actual empty frame _ _

theorem class_aggregate_free {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p) :
    IdCovered (GeneralNominalVersionedSupportedCompletion237.pool (names s) s p) s p.packet := by
  intro entry member supported
  have seedEq : p.packet.context.state.seed = seed s :=
    congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) frame.context_eq
  obtain ⟨name,_,_,which⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp member
  have excluded (kind : Nat) (nonLegacy : entry.1 = GeneralNominalAggregateVersion231.slot
      p.packet.context.state.seed p.packet.site.occurrence.identity p.packet.declaration.id kind name p.packet.bindings) : False := by
    simp only [GeneralNominalVersionedSupportedCompletion237.pool,List.mem_append] at supported
    rcases supported with (base|report)|live
    · have small := source_small actual base
      rw [nonLegacy,← seedEq] at small
      exact Nat.not_lt_of_ge small (GeneralNominalAggregateVersion231.above_seed ..)
    · have small := raw_small actual empty frame (GeneralVersionedRawReportDomain313.raw_membership _ report)
      rw [nonLegacy,← seedEq] at small
      exact Nat.not_lt_of_ge small (GeneralNominalAggregateVersion231.above_seed ..)
    · have a := classes actual empty frame entry.1 live
      rw [nonLegacy] at a
      exact aggregate_not_actual p kind name a
  exact False.elim (which.elim (fun eq => excluded 0 (congrArg Prod.fst eq))
    (fun eq => excluded 1 (congrArg Prod.fst eq)))

end Yulang.GeneralVersionedFirstFootprint313
