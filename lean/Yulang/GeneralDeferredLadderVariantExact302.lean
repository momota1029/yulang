import Yulang.GeneralDeferredLadderAfterVariants302

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralDeferredLadderVariantExact302
open GeneralDeferredLadderAfterVariants302 (OwnedPhase step)
open GeneralDeferredLadderExact302 (RawStep)
open GeneralObservedLadderEvidence301 (replay replay_prepared replay_held replay_children)
open GeneralObservedLadderStage301 (current_requests)
open GeneralObservedLadderRoute301
open GeneralObservedLadderLedger301 (stagePlan)
open GeneralObservedLadderOnlyInstall301 (inner_frame raw_hit recorded generated leaf_committed same_effect)
open GeneralObservedLadderNoAdmin301 (headless equality_closed point_closed)
open GeneralNominalVersionedMixedTerminalStable234 (no_refresh)
open GeneralNominalVersionedEvidence231 (Frame Instance)
open GeneralNominalVersionedMixedKernel234 (Step Installable Committed)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralObservedLadderPlan301 (compiled)
open GeneralNominalCenters (Plan)
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (displayRoot)

theorem frame (p : OwnedPhase n k) (i : Nat) (before : i < k) (hi : i ≤ n) :
    Frame compiled p.state.core (focus n i) 1 (replay p.toPhase i hi) := by
  refine ⟨rfl,p.context_eq.symm,rfl,rfl,?_,?_,List.mem_cons_of_mem _ (List.mem_cons_self ..),rfl,?_,?_⟩
  · change GeneralNominalDemandMerging.pointSite (focus n i) ∈ p.state.core.erased.current.sites
    rw [p.raw_eq,← observed n i]
    exact List.mem_map.mpr ⟨site n i,(sites_exact ..).mpr ⟨i,Nat.le_of_lt before,rfl⟩,rfl⟩
  · change site n i ∈ p.state.core.sites
    rw [p.centers_eq]
    exact (sites_exact ..).mpr ⟨i,Nat.le_of_lt before,rfl⟩
  · exact GeneralObservedLadderSelection301.located n i (invocation n i) (by omega)
  · rw [p.context_eq]
    exact replay_prepared p.toPhase i hi (p.all_owned i before)

theorem past_committed (p : OwnedPhase n k) (i : Nat) (past : i < k) (hi : i ≤ n)
    {q : Plan roles} {key} (given : Frame compiled p.state.core (focus n i) key q) :
    Committed p.state q := by
  have planEq := inner_frame p.toPhase i hi given (frame p i past hi) rfl rfl rfl
  rw [planEq]
  constructor
  · intro m held
    exact ⟨replay_held p.toPhase i hi m held,
      GeneralRebaseDisplayFrame276.classes_empty (current_requests p.toPhase _) _ m⟩
  · intro child member
    rw [replay_children p.toPhase i hi] at member
    cases List.mem_singleton.mp member
    change (_,_) ∈ p.state.core.erased.current.edges
    rw [p.edges_eq]
    exact (edge_exact ..).mpr ⟨i,past,rfl⟩

theorem candidate_exact (p : OwnedPhase n k) (cap : k ≤ n+1) (e : Effect roles)
    (enabled : Installable compiled p.state e)
    (seen : GeneralNominalSaturationState.Generated p.state.core.erased.current displayRoot
      e.plan.packet.site.occurrence)
    (novel : ¬ Committed p.state e.plan) :
    ∃ hi : k ≤ n, e = GeneralObservedLadderEnabled301.effect p.toPhase hi := by
  obtain ⟨i,low,location⟩ := generated p.toPhase seen
  have f := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,location] at f
  by_cases earlier : i < k
  · exact False.elim (novel (past_committed p i earlier (by omega) f))
  have eq : i = k := by omega
  subst i
  by_cases inner : k ≤ n
  · refine ⟨inner,same_effect e (GeneralObservedLadderEnabled301.effect p.toPhase inner)
      enabled.registry_eq enabled.snapshot_eq ?_⟩
    exact inner_frame p.toPhase k inner f (GeneralObservedLadderStage301.frame p.toPhase inner) rfl rfl rfl
  have endOf : k = n+1 := by omega
  subst k
  exact False.elim (novel (leaf_committed p.toPhase f))

theorem only_step (p : OwnedPhase n k) (cap : k ≤ n+1) (s : State roles) (raw : RawStep p.state s) :
    ∃ hi : k ≤ n, s = (step p hi).state := by
  change Step compiled displayRoot p.state s at raw
  obtain ⟨focus,generated,action⟩ := raw
  cases action with
  | administrative action =>
    cases action with
    | enqueue _ absent =>
      obtain ⟨row,seen,loc⟩ := recorded p.toPhase generated
      exact False.elim (absent row seen loc)
    | refresh ctx certificate id tracked unknown known =>
      exact False.elim (no_refresh (headless p.toPhase) certificate tracked unknown known)
    | equate a b first last same novel =>
      exact False.elim (novel (equality_closed p.toPhase a b first last same))
    | reobserve rev _ improves =>
      exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision (point_closed p.toPhase) rev improves)
  | refresh _ ctx certificate id tracked unknown known =>
    exact False.elim (no_refresh (headless p.toPhase) certificate tracked unknown known)
  | install e enabled novel =>
    obtain ⟨hi,equal⟩ := candidate_exact p cap e enabled generated novel
    cases equal
    exact ⟨hi,rfl⟩
  | merge a b first last same novel =>
    rw [p.centers_eq] at first last
    obtain ⟨i,ai,rfl⟩ := (sites_exact ..).mp first
    obtain ⟨j,bj,rfl⟩ := (sites_exact ..).mp last
    have eq : i = j := GeneralObservedLadderEnabled301.separates p.toPhase (by omega) (by omega) same
    cases eq
    exact False.elim (novel (.refl _))

theorem exact_step (p : OwnedPhase n k) (cap : k ≤ n+1) (s : State roles) :
    RawStep p.state s ↔ ∃ hi : k ≤ n, s = (step p hi).state :=
  ⟨only_step p cap s,by rintro ⟨hi,rfl⟩; exact GeneralObservedLadderEnabled301.actual p.toPhase hi⟩

theorem halted (p : OwnedPhase n (n+1)) (s : State roles) : ¬ RawStep p.state s := by
  intro raw
  obtain ⟨bad,_⟩ := only_step p (Nat.le_refl _) s raw
  omega

theorem accessible (p : OwnedPhase n k) (cap : k ≤ n+1) : Acc (fun last first => RawStep first last) p.state := by
  have countdown (gas : Nat) : ∀ i (q : OwnedPhase n i), i ≤ n+1 → n+1-i ≤ gas →
      Acc (fun last first => RawStep first last) q.state := by
    induction gas with
    | zero =>
      intro i q fit done
      have terminal : i = n+1 := by omega
      subst i
      exact Acc.intro _ (fun next impossible => False.elim (halted q next impossible))
    | succ gas ih =>
      intro i q fit remain
      constructor
      intro s next
      obtain ⟨hi,rfl⟩ := only_step q fit s next
      exact ih (i+1) (step q hi) (by omega) (by omega)
  exact countdown (n+1-k) k p cap (Nat.le_refl _)

end Yulang.GeneralDeferredLadderVariantExact302
