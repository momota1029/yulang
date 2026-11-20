import Yulang.GeneralRebaseRowRefreshClosed288
import Yulang.GeneralRebaseNonleafTransport276

/-! Transport the actual parent and child packets through any certified
refresh of the guarded state using the existing generic transport theorem. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralRebaseRowRefreshPackets288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child plan center sole_child)
open GeneralRebaseRowParentFrame287 (after effect after_model at_role)
open GeneralRebaseRowParentEvidence287 (raw_sites centers roles_distinct)
open GeneralRebaseRowLedger288 (supplemented models_eq)
open GeneralRebaseRowLedgerFirst288 (committed_forward)
open GeneralRebaseRowClosure287 (edges)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedKernel234 (Committed)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralRebaseRetarget275 (Observed)
open GeneralRebaseNonleafCommitted276 (result)
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence)

theorem root_frame : Frame (registry true) supplemented.core root 0 (replayPlan (plan true)) :=
  GeneralRebaseRowParentEvidence287.replay_frame true _ (after_model true Common.rowEmpty)

theorem child_frame : Frame (registry true) supplemented.core (child true) 1 GeneralRebaseRowWholeChild287.plan :=
  GeneralRebaseRowWholeChild287.child_frame

theorem parent_observed : Observed (replayPlan (plan true)) := by
  unfold Observed
  rw [show GeneralNominalInspection.queries (replayPlan (plan true)).packet.context.state
    (replayPlan (plan true)).packet.context.interpretation (replayPlan (plan true)).packet.declaration =
    [.nominal 0 [.variables [0]]] from GeneralRebaseRowParentPacket287.query]
  exact .cons (.point (descriptor := outer) rfl rfl rfl (.cons .variables .nil)) .nil

theorem child_observed : Observed GeneralRebaseRowWholeChild287.plan := by
  unfold Observed
  rw [show GeneralNominalInspection.queries _ _ _ = [.variables [0]] from GeneralRebaseRowWholeChild287.query]
  exact .cons .variables .nil

theorem root_committed : Committed supplemented (replayPlan (plan true)) :=
  committed_forward (GeneralNominalVersionedCommitted232.replay_committed before (effect true))

theorem child_committed : Committed supplemented GeneralRebaseRowWholeChild287.plan :=
  committed_forward GeneralRebaseRowWholeChild287.already_committed

variable {context : GeneralNominalCandidates.Context}

theorem nonempty_models (cert : Refresh supplemented context) :
    Models (refresh supplemented context) (model Common.rowEmpty) :=
  (refresh_models cert).mpr ((models_eq _).mpr (after_model true Common.rowEmpty))

theorem root_transported (cert : Refresh supplemented context) :
    Frame (registry true) (refresh supplemented context).core root 0 (result root_frame cert) :=
  GeneralRebaseNonleafPrepared276.frame root_frame cert parent_observed root_committed _ (nonempty_models cert)

theorem child_transported (cert : Refresh supplemented context) :
    Frame (registry true) (refresh supplemented context).core (child true) 1 (result child_frame cert) :=
  GeneralRebaseNonleafPrepared276.frame child_frame cert child_observed child_committed _ (nonempty_models cert)

theorem scope {focus : Occurrence roles}
    (generated : Generated (refresh supplemented context).core.erased.current root focus) :
    focus = root ∨ focus = child true := by
  induction generated with
  | root => exact .inl rfl
  | child _ member _ =>
    change _ ∈ (after true).core.erased.current.edges at member
    rw [edges true] at member
    exact .inr (congrArg Prod.snd (List.mem_singleton.mp member))
  | alias _ _ present _ _ =>
    change _ ∈ (after true).core.erased.current.sites at present
    rw [raw_sites true] at present
    rcases List.mem_cons.mp present with e | e
    · cases e
      exact .inl rfl
    · cases List.mem_singleton.mp e
      exact .inr rfl

theorem distinct : root ≠ child true :=
  fun same => roles_distinct true (congrArg (fun o : Occurrence roles => o.demand.role) same)

theorem unique_site {a b : GeneralNominalDemandMerging.Site roles}
    (first : a ∈ (refresh supplemented context).core.erased.current.sites)
    (second : b ∈ (refresh supplemented context).core.erased.current.sites)
    (same : a.occurrence = b.occurrence) : a = b := by
  change a ∈ (after true).core.erased.current.sites at first
  change b ∈ (after true).core.erased.current.sites at second
  rw [raw_sites true] at first second
  simp only [List.mem_cons,List.not_mem_nil,or_false] at first second
  rcases first with rfl|rfl <;> rcases second with rfl|rfl
  · rfl
  · exact (distinct same).elim
  · exact (distinct same.symm).elim
  · rfl

theorem unique_center {a b : GeneralNominalCenters.Site roles}
    (first : a ∈ (refresh supplemented context).core.sites)
    (second : b ∈ (refresh supplemented context).core.sites)
    (same : a.occurrence = b.occurrence) : a = b := by
  change a ∈ (after true).core.sites at first
  change b ∈ (after true).core.sites at second
  rw [centers true] at first second
  simp only [List.mem_cons,List.not_mem_nil,or_false] at first second
  rcases first with rfl|rfl <;> rcases second with rfl|rfl
  · rfl
  · exact (distinct same).elim
  · exact (distinct same.symm).elim
  · rfl

theorem same_plan {focus : Occurrence roles} {p q : Plan roles} {key other : Nat}
    (first : Frame (registry true) (refresh supplemented context).core focus key p)
    (second : Frame (registry true) (refresh supplemented context).core focus other q)
    (d : p.packet.declaration = q.packet.declaration) : p = q :=
  GeneralRebaseScopedFrame276.same_frame first second d
    (unique_site first.raw_recorded second.raw_recorded (first.occurrence_eq.trans second.occurrence_eq.symm))
    (unique_center first.center_recorded second.center_recorded
      ((p.input_exact.trans first.occurrence_eq).trans (q.input_exact.trans second.occurrence_eq).symm))

theorem prepared_is_committed (cert : Refresh supplemented context) {focus : Occurrence roles}
    {p : Plan roles} {key : Nat}
    (visible : focus = root ∨ focus = child true)
    (frame : Frame (registry true) (refresh supplemented context).core focus key p) :
    Committed (refresh supplemented context) p := by
  rcases visible with rfl | rfl
  · have eq := at_role true _ frame.visible frame.role_eq
    have same := same_plan frame (root_transported cert) eq
    rw [same]
    exact GeneralRebaseNonleafCommitted276.committed root_frame cert parent_observed root_committed
  · have eq := GeneralRebaseRowLocal287.child_at_role true _ frame.visible frame.role_eq
    have same := same_plan frame (child_transported cert) eq
    rw [same]
    exact GeneralRebaseNonleafCommitted276.committed child_frame cert child_observed child_committed

end Yulang.GeneralRebaseRowRefreshPackets288
