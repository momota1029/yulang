import Yulang.GeneralDeferredLadderEarlyInstall303

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralDeferredLadderEarlyExact303
open GeneralDeferredLadderLedger302 (Phase)
open GeneralDeferredLadderEarlyInstall303 (effect actual current_requests)
open GeneralDeferredLadderRetargetFrames302 (raw_recorded center_recorded list_held)
open GeneralDeferredLadderRetargetData302 (listPlan argument_exact wrong_int)
open GeneralDeferredLadderExact302 (RawStep Promotion)
open GeneralObservedLadderRoute301 (focus site edge_exact unique_row)
open GeneralObservedLadderPlan301 (compiled)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (Effect State)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedMixedKernel234 (Installable Committed)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalRecursiveCandidates (Context)
open GeneralNominalVersionedCandidates231 (Prepared)
open GeneralDeclarationExamples (roles display)
open GeneralNominalExamples (intDisplay)

theorem not_int (p : Phase n k) (i : Nat) (hi : i ≤ n) (ctx : Context)
    (cert : Refresh p.state ctx) : ¬ Prepared compiled ctx (focus n i) intDisplay := by
  rintro ⟨_,_,bounds,loc,_,report,_⟩
  cases Option.some.inj (loc.symm.trans (argument_exact p ctx cert i (by omega)))
  exact wrong_int p ctx cert i hi report.2.1

theorem any_list_frame_eq (p : Phase n k) (i : Nat) (hi : i ≤ n) (atPhase : i ≤ k)
    (ctx : Context) (cert : Refresh p.state ctx) {q : GeneralNominalCenters.Plan roles} {key : Nat}
    (given : Frame compiled (refresh p.state ctx).core (focus n i) key q) :
    q = listPlan p ctx cert i hi := by
  have decl : q.packet.declaration = display := by
    rcases GeneralRebaseCompiledDisplay277.compiled_members given.visible given.role_eq with wrong|right
    · exact False.elim (not_int p i hi ctx cert (wrong ▸ given.prepared))
    · exact right
  have retained : Prepared compiled ctx (focus n i) display := by
    have ready := given.prepared
    change Prepared compiled ctx (focus n i) q.packet.declaration at ready
    rwa [decl] at ready
  have exactFrame : Frame compiled (refresh p.state ctx).core (focus n i) 1 (listPlan p ctx cert i hi) :=
    ⟨rfl,rfl,rfl,rfl,raw_recorded p ctx i atPhase,center_recorded p ctx i atPhase,
      List.mem_cons_of_mem _ (List.mem_cons_self ..),rfl,argument_exact p ctx cert i (by omega),
      retained⟩
  refine GeneralRebaseScopedFrame276.same_frame given exactFrame decl ?_ ?_
  · exact GeneralDeferredLadderStage302.raw_is p _ given.raw_recorded given.occurrence_eq
  · exact unique_row n k i q.input (p.centers_eq ▸ given.center_recorded)
      (q.input_exact.trans given.occurrence_eq)

theorem prior_committed (p : Phase n k) (i : Nat) (hi : i ≤ n) (past : i < k)
    (ctx : Context) (cert : Refresh p.state ctx) {q : GeneralNominalCenters.Plan roles} {key : Nat}
    (given : Frame compiled (refresh p.state ctx).core (focus n i) key q) :
    Committed (refresh p.state ctx) q := by
  rw [any_list_frame_eq p i hi (by omega) ctx cert given]
  constructor
  · intro m valid
    exact ⟨list_held p ctx cert i hi m valid,
      GeneralRebaseDisplayFrame276.classes_empty (current_requests p ctx _) _ m⟩
  · intro child member
    have children : GeneralNominalVersionedFrame231.children (listPlan p ctx cert i hi).packet =
        [focus n (i+1)] :=
      (GeneralDeferredLadderTransport302.children_eq
        (GeneralDeferredLadderRetargetData302.list_same p ctx cert i hi)).symm.trans
        (GeneralObservedLadderEvidence301.replay_children (GeneralObservedLadderEvidence301.final n) i hi)
    rw [children] at member
    cases List.mem_singleton.mp member
    change (_,_) ∈ p.state.core.erased.current.edges
    rw [p.edges_eq]
    exact (edge_exact ..).mpr ⟨i,past,rfl⟩


theorem after_only_install (p : Phase n k) (cap : k ≤ n+1) (ctx : Context)
    (cert : Refresh p.state ctx) (known : GeneralNominalState.Known ctx.state (n+1))
    (t : State roles) (raw : RawStep (refresh p.state ctx) t) :
    ∃ e, Installable compiled (refresh p.state ctx) e ∧ ¬ Committed (refresh p.state ctx) e.plan ∧
      GeneralNominalSaturationState.Generated (refresh p.state ctx).core.erased.current
        GeneralNominalExamples.displayRoot e.plan.packet.site.occurrence ∧
      t = install (refresh p.state ctx) e := by
  change GeneralNominalVersionedMixedKernel234.Step compiled GeneralNominalExamples.displayRoot
    (refresh p.state ctx) t at raw
  obtain ⟨o,generated,action⟩ := raw
  let hs := GeneralDeferredLadderAfterPromotion302.headless p ctx cert known
  cases action with
  | administrative action =>
    cases action with
    | enqueue _ absent =>
      obtain ⟨row,recorded,eq⟩ := GeneralDeferredLadderOnlyInstall302.recorded p (GeneralDeferredLadderAfterPromotion302.reverse_generated p ctx generated)
      exact False.elim (absent row recorded eq)
    | refresh target c id tracked unknown known =>
      exact False.elim (GeneralNominalVersionedMixedTerminalStable234.no_refresh hs c tracked unknown known)
    | equate a b first last equal novel =>
      exact False.elim (novel (GeneralDeferredLadderAfterPromotion302.equality_closed p ctx cert a b first last equal))
    | reobserve rev _ improves =>
      exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision
        (GeneralDeferredLadderAfterPromotion302.point_closed p ctx cert known) rev improves)
  | refresh _ target c id tracked unknown known =>
    exact False.elim (GeneralNominalVersionedMixedTerminalStable234.no_refresh hs c tracked unknown known)
  | install e held fresh =>
    exact ⟨e,held,fresh,generated,rfl⟩
  | merge a b first last same novel =>
    change a ∈ p.state.core.sites at first
    change b ∈ p.state.core.sites at last
    rw [p.centers_eq] at first last
    obtain ⟨i,ai,rfl⟩ := (GeneralObservedLadderRoute301.sites_exact ..).mp first
    obtain ⟨j,bj,rfl⟩ := (GeneralObservedLadderRoute301.sites_exact ..).mp last
    have eqModels : GeneralNominalVersionedJournal232.Models (refresh p.state ctx) =
        GeneralNominalVersionedJournal232.Models p.state :=
      funext fun m => propext (GeneralNominalVersionedMixedObservations233.refresh_models cert)
    rw [eqModels] at same
    have indexes := GeneralDeferredLadderNoAdmin302.separates p (by omega) (by omega) same
    cases indexes
    exact False.elim (novel (.refl _))

theorem exact_next (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx)
    (known : GeneralNominalState.Known ctx.state (n+1)) (s : State roles) :
    RawStep (refresh p.state ctx) s ↔ s = install (refresh p.state ctx) (effect p hi ctx cert) := by
  constructor
  · intro raw
    obtain ⟨e,enabled,novel,generated,rfl⟩ := after_only_install p (by omega) ctx cert known s raw
    obtain ⟨i,low,location⟩ := GeneralDeferredLadderOnlyInstall302.generated p
      (GeneralDeferredLadderAfterPromotion302.reverse_generated p ctx generated)
    have f := e.frame
    rw [enabled.registry_eq,enabled.snapshot_eq,location] at f
    by_cases before : i < k
    · exact False.elim (novel (prior_committed p i (by omega) before ctx cert f))
    have eq : i = k := by omega
    subst i
    have same := GeneralDeferredLadderOnlyInstall302.same_effect e (effect p hi ctx cert)
      enabled.registry_eq enabled.snapshot_eq (any_list_frame_eq p k hi (Nat.le_refl _) ctx cert f)
    rw [same]
  · rintro rfl
    exact actual p hi ctx cert known

end Yulang.GeneralDeferredLadderEarlyExact303
