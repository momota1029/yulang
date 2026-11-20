import Yulang.GeneralDeferredLadderFrames302

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralDeferredLadderOnlyInstall302
open GeneralDeferredLadderReport302 (context list_as_int)
open GeneralObservedLadderRoute301
open GeneralDeferredLadderLedger302
open GeneralObservedLadderReport301 (point exact_at)
open GeneralDeferredLadderPlan302 (compiled)
open GeneralDeferredLadderAdvance302 (run advance phase_step)
open GeneralDeferredLadderFrames302 (replay replay_frame replay_held replay_children)
open GeneralDeferredLadderStage302 (current_requests raw_is)
open GeneralDeferredLadderEnabled302 (effect)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedCandidates231 (Prepared)
open GeneralNominalVersionedMixedKernel234 (Installable Committed)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalSaturationState (Generated)
open GeneralNominalCenters (Plan)
open GeneralDeclarationExamples (roles display)
open GeneralNominalExamples (intDisplay displayRoot registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)

theorem raw_hit (p : Phase n k) (s : GeneralNominalDemandMerging.Site roles)
    (member : s ∈ p.state.core.erased.current.sites) : ∃ i ≤ k, s.occurrence = focus n i := by
  rw [p.raw_eq] at member
  obtain ⟨center,seen,rfl⟩ := List.mem_map.mp member
  obtain ⟨i,low,rfl⟩ := (sites_exact ..).mp seen
  exact ⟨i,low,rfl⟩

theorem generated (p : Phase n k) {o : Occurrence roles}
    (seen : Generated p.state.core.erased.current displayRoot o) : ∃ i ≤ k, o = focus n i := by
  induction seen with
  | root => exact ⟨0,Nat.zero_le _,rfl⟩
  | child _ edge _ =>
    rw [p.edges_eq] at edge
    obtain ⟨i,low,known⟩ := (edge_exact ..).mp edge
    exact ⟨i+1,by omega,(Prod.mk.inj known).2⟩
  | alias _ _ recorded _ _ => exact raw_hit p _ recorded

theorem recorded (p : Phase n k) {o : Occurrence roles}
    (seen : Generated p.state.core.erased.current displayRoot o) :
    ∃ s ∈ p.state.core.erased.current.sites, s.occurrence = o := by
  obtain ⟨i,low,rfl⟩ := generated p seen
  refine ⟨(site n i).observed,?_,rfl⟩
  rw [p.raw_eq]
  exact List.mem_map.mpr ⟨site n i,(sites_exact ..).mpr ⟨i,low,rfl⟩,rfl⟩

theorem wrong_int_at (p : Phase n k) (i : Nat) (hi : i ≤ n) :
    ¬ Prepared compiled p.state.core.erased.current.context (focus n i) intDisplay := by
  rw [p.context_eq]
  rintro ⟨_,_,bs,matching,_,done,_⟩
  have loc : GeneralNominalRecursiveCandidates.arguments (env p) (focus n i) = some [point n i (by omega)] :=
    GeneralObservedLadderSelection301.located n i (invocation n i) (by omega)
  cases Option.some.inj (matching.symm.trans loc)
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,list_as_int n i hi] at done
  have empty := done.2.1
  cases empty

theorem inner_frame (p : Phase n k) (i : Nat) (hi : i ≤ n) {q exact : Plan roles} {key chosen}
    (candidate : Frame compiled p.state.core (focus n i) key q)
    (certified : Frame compiled p.state.core (focus n i) chosen exact)
    (right : exact.packet.declaration = display)
    (raw_eq : exact.packet.site = GeneralNominalDemandMerging.pointSite (focus n i))
    (center_eq : exact.input = site n i) :
    q = exact := by
  apply GeneralRebaseScopedFrame276.same_frame candidate certified
  · rcases GeneralRebaseCompiledDisplay277.compiled_members candidate.visible candidate.role_eq with wrong|valid
    · exact False.elim (wrong_int_at p i hi (wrong ▸ candidate.prepared))
    · exact valid.trans right.symm
  · exact (raw_is p _ candidate.raw_recorded candidate.occurrence_eq).trans raw_eq.symm
  · rw [center_eq]
    exact unique_row n k i _ (p.centers_eq ▸ candidate.center_recorded)
      (q.input_exact.trans candidate.occurrence_eq)

theorem past_committed (n k : Nat) (cap : k ≤ n+1) (i : Nat) (past : i < k) {q : Plan roles} {key}
    (candidate : Frame compiled (run n k cap).state.core (focus n i) key q) :
    Committed (run n k cap).state q := by
  let p := run n k cap
  have hi : i ≤ n := by omega
  have planEq := inner_frame p i hi candidate (replay_frame n k cap i past) rfl rfl rfl
  rw [planEq]
  constructor
  · intro m held
    exact ⟨replay_held p i hi m held,GeneralRebaseDisplayFrame276.classes_empty (current_requests p _) _ m⟩
  · intro child member
    rw [replay_children p i hi] at member
    cases List.mem_singleton.mp member
    change (_,_) ∈ p.state.core.erased.current.edges
    rw [p.edges_eq]
    exact (edge_exact ..).mpr ⟨i,past,rfl⟩

theorem not_prepared_at_leaf (p : Phase n (n+1)) (d : GeneralDeclarations.Declaration)
    (visible : d ∈ compiled.declarations) (role : d.role = (focus n (n+1)).demand.role) :
    ¬ Prepared compiled p.state.core.erased.current.context (focus n (n+1)) d := by
  rw [p.context_eq]
  rintro ⟨_,_,bs,matching,_,done,_⟩
  cases Option.some.inj (matching.symm.trans (GeneralDeferredLadderStage302.located p (Nat.le_refl _)))
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended] at done
  rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
  · rw [GeneralObservedLadderSemanticGap301.old_int_report] at done
    cases done.1
  · rw [GeneralObservedLadderSemanticGap301.old_list_report] at done
    cases done.1

theorem endpoint_pending (p : Phase n (n+1)) :
    GeneralNominalState.RootPending p.state.core.erased.current.context.state (focus n (n+1)).demand := by
  exact ⟨(0 : Fin 1),GeneralDeferredLadderRefresh302.unknown p⟩

theorem same_effect (a b : Effect roles) (reg : a.registry = b.registry)
    (ctx : a.snapshot = b.snapshot) (plan : a.plan = b.plan) : a = b := by
  cases a
  cases b
  cases reg
  cases ctx
  cases plan
  rfl

theorem candidate_exact (n k : Nat) (cap : k ≤ n+1) (e : Effect roles)
    (enabled : Installable compiled (run n k cap).state e)
    (seen : Generated (run n k cap).state.core.erased.current displayRoot e.plan.packet.site.occurrence)
    (novel : ¬ Committed (run n k cap).state e.plan) :
    ∃ hi : k ≤ n, e = effect (run n k cap) hi := by
  let p := run n k cap
  obtain ⟨i,low,location⟩ := generated p seen
  have f := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,location] at f
  by_cases earlier : i < k
  · exact False.elim (novel (past_committed n k cap i earlier f))
  have eq : i = k := by omega
  subst i
  by_cases inner : k ≤ n
  · refine ⟨inner,same_effect e (effect p inner) enabled.registry_eq enabled.snapshot_eq ?_⟩
    exact inner_frame p k inner f (GeneralDeferredLadderStage302.frame p inner) rfl rfl rfl
  have endOf : k = n+1 := by omega
  subst k
  exact False.elim (not_prepared_at_leaf (run n (n+1) cap) _ f.visible f.role_eq f.prepared)

end Yulang.GeneralDeferredLadderOnlyInstall302
