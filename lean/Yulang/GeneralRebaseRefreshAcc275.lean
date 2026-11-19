import Yulang.GeneralRebaseRefreshFrame275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27500
set_option maxHeartbeats 9000000
namespace Yulang.GeneralRebaseRefreshAcc275
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralDictionaryVersionedSecondInstall233 (installed plan effect)
open GeneralDictionaryVersionedPointStage233 (point allocated reserved ordinary)
open GeneralDictionaryJournalRefinement228Reobserve (exactCopy)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedKernel234 (Committed Installable Step Stable)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalCenters (Plan)
open GeneralRebaseRetarget275 (Observed retarget)
open GeneralRebaseRefreshFrame275 (LocatedFrame)
open GeneralRebaseRefreshClosure275 (Gates step_partition)
open GeneralRebaseRefreshRank275 (Hop Path rank rank_drop)
open GeneralNominalRecursiveInspection

def Kept (state : State roles) : Prop :=
 ∃ candidate : Plan roles, LocatedFrame state candidate ∧ Observed candidate ∧ Committed state candidate

theorem initial_observed : Observed (GeneralNominalVersionedInstallation231.replayPlan plan) := by
 unfold Observed
 change GeneralNominalRefinementTrace197.ObservedMany
   installed.core.erased.current.context.state
   (GeneralNominalInspection.queries
     (GeneralDictionaryOptionalCurrent229.currentContext allocated reserved ordinary).state
     GeneralDictionaryJournalRefinement228Source.interpretation declaration)
   [((0 : Fin 5),(0 : Fin 5))]
 rw [GeneralDictionaryOptionalCurrent229.query]
 exact .cons (.point (descriptor := exactCopy) rfl rfl rfl (.cons .variables (.cons .variables .nil))) .nil

theorem kept_initial : Kept installed :=
 ⟨_,GeneralRebaseRefreshFrame275.of_frame GeneralDictionaryVersionedSecondSelected233.frame,initial_observed,
   GeneralNominalVersionedCommitted232.replay_committed point effect⟩

theorem no_install {s : State roles} (gates : Gates s) (kept : Kept s) (effect : Effect roles)
 (available : Installable registry s effect) (rooted : effect.plan.packet.site.occurrence = root) :
 Committed s effect.plan := by
 obtain ⟨p,location,_,committed⟩ := kept
 have frame := effect.frame
 rw [available.registry_eq,available.snapshot_eq,rooted] at frame
 rw [GeneralRebaseRefreshFrame275.same_plan gates (GeneralRebaseRefreshFrame275.of_frame frame) location]
 exact committed

theorem keep_next {state : State roles} (kept : Kept state)
 (ctx : GeneralNominalCandidates.Context) (cert : Refresh state ctx) :
 Kept (refresh state ctx) := by
 obtain ⟨p,location,seen,committed⟩ := kept
 let ref := GeneralRebaseRefreshFrame275.refinement location cert
 have interp := GeneralRebaseRefreshFrame275.interpretation location cert
 have empty : p.packet.declaration.requirements = [] := by rw [location.declaration_eq]
 refine ⟨retarget p ref,GeneralRebaseRefreshFrame275.moved location cert,
   GeneralRebaseRetarget275.observed p ref interp seen,?_,?_⟩
 · intro m valid
   have before := (refresh_models cert).mp valid
   have full := committed.1 m before
   refine ⟨GeneralRebaseRetarget275.holds_leaf p ref interp seen empty m valid.1.1 full.1,?_⟩
   have transfer := GeneralNominalVersionedFrameTransport232.class_effects_iff (before := (refresh state ctx).core)
      (after := state.core) (fun _ => GeneralNominalVersionedRefresh232.refresh_requests state ctx)
      (plan := p) (model := m) (root := p.packet.site.occurrence)
   apply GeneralRebaseRetargetEffects275.class_effects p ref interp (refresh state ctx).core seen m
   exact transfer.mpr full.2
 · intro child member
   rw [GeneralRebaseRetarget275.children_leaf p ref empty] at member
   cases member

theorem hop_invariant {s t : State roles} (p : Gates s ∧ Kept s) (hop : Hop s t) :
 Gates t ∧ Kept t := by
 cases hop with
 | step ctx cert _ _ _ _ => exact ⟨GeneralRebaseRefreshClosure275.gates_next p.1 ctx cert,keep_next p.2 ctx cert⟩

theorem exact_hop {s t : State roles} (p : Gates s ∧ Kept s) :
 Step registry root s t ↔ Hop s t := by
 constructor
 · intro step
   rcases step_partition p.1 step with real | ⟨candidate,enabled,rooted,novel,_⟩
   · exact real
   · exact False.elim (novel (no_install p.1 p.2 candidate enabled rooted))
 · exact GeneralRebaseRefreshRank275.step

theorem accessible {s : State roles} (p : Gates s ∧ Kept s) :
 Acc (fun after before => Step registry root before after) s := by
 have bounded := (measure rank).wf.apply s
 induction bounded with
 | intro s _ ih =>
   constructor
   intro target step
   have hop := (exact_hop p).mp step
   exact ih target (rank_drop p.1.anchor hop) (hop_invariant p hop)

theorem actual_230_acc : Acc (fun after before => Step registry root before after) installed :=
 accessible ⟨GeneralRebaseRefreshClosure275.gates_initial,kept_initial⟩

inductive ActualPath : State roles → State roles → Nat → Prop
 | empty (s : State roles) : ActualPath s s 0
 | more {s t u : State roles} {n : Nat} : ActualPath s t n → Step registry root t u → ActualPath s u (n+1)

theorem actual_path {s t : State roles} {n : Nat} (p : Gates s ∧ Kept s) (path : ActualPath s t n) :
 (Gates t ∧ Kept t) ∧ Path s t n := by
 induction path with
 | empty => exact ⟨p,.empty _⟩
 | more _ op ih =>
   have hop := (exact_hop ih.1).mp op
   exact ⟨hop_invariant ih.1 hop,.more ih.2 hop⟩

theorem actual_bound {final : State roles} {n : Nat} (path : ActualPath installed final n) : n ≤ 3 :=
 GeneralRebaseRefreshRank275.at_most_three
   (actual_path ⟨GeneralRebaseRefreshClosure275.gates_initial,kept_initial⟩ path).2

end Yulang.GeneralRebaseRefreshAcc275
