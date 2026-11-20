import Yulang.GeneralRebaseReceiptStampedExport289

/-! The actual no-live-request guard is inherited by the final typed
stamp, including replays after a real alias merge. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29200
set_option maxHeartbeats 19000000
namespace Yulang.GeneralRebaseReceiptStampedEffects289
open GeneralRebaseReceiptTypedStamp289 (Stamp capture)
open GeneralRebaseReceiptStampMachine289 (Phase erase Valid step)
open GeneralRebaseReceiptAnchorProduct289 (strictTick)
open GeneralRebaseReceiptExactLink289 (boundedDecision anchoredWire anchors)
open GeneralRebaseReceiptCatalogue289 (boundedWire guarded)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralRebaseReceiptWire289 (Offer)
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)

theorem strict_passes_bounded {r : Registry} {s : State roles} {up down : Occurrence roles} {ask : Offer}
    (bound : boundedDecision r s up down ask = .ready) : guarded r s down ask = .ready := by
  have anchored := GeneralRebaseReceiptExactLink289.accept_has_actual_anchor bound
  have yes := (GeneralRebaseReceiptExactLink289.anchors_exact ..).mpr anchored
  unfold boundedDecision anchoredWire at bound
  unfold guarded
  cases prior : boundedWire r s down with
  | none => simp [prior,yes] at bound
  | some w => simpa [prior,yes] using bound

theorem stamp_sent_implies_base (now saved : Stamp) (baseTick : GeneralRebaseReceiptMachine289.Phase →
    Option GeneralRebaseReceiptMachine289.Phase) (p : Phase)
    (took : step now baseTick p = some (.sent saved)) :
    baseTick (erase p) = some (.published saved.offer) := by
  have maps : step now baseTick p = (baseTick (erase p)).map (GeneralRebaseReceiptStampMachine289.lift now) := by
    cases p with
    | scan | stopped | sent => rfl
    | held previous =>
      by_cases assent : previous = now
      · exact ite_eq_left assent
      · rw [GeneralRebaseReceiptStampMachine289.stale_exact _ _ _ assent] at took
        cases took
  rw [maps] at took
  have projection := congrArg (Option.map erase) took
  cases query : baseTick (erase p) with
  | none => simp [query] at projection
  | some q =>
    rw [query] at took
    have lifted : GeneralRebaseReceiptStampMachine289.lift now q = .sent saved := Option.some.inj took
    have erased := congrArg erase lifted
    rw [GeneralRebaseReceiptStampMachine289.erase_lift] at erased
    exact congrArg some erased

theorem strict_sent_implies_bounded_read {r : Registry} {s : State roles}
    {up down : Occurrence roles} {ask : Offer} {p : Phase} {saved : Stamp}
    (took : step (capture s.core.erased.current.context.state up down ask)
      (strictTick r s up down ask) p = some (.sent saved)) : guarded r s down ask = .ready := by
  have base := stamp_sent_implies_base _ _ _ _ took
  unfold strictTick at base
  cases prior : anchoredWire r s up down ask with
  | none =>
    rw [prior] at base
    cases p <;> cases base
  | some w =>
    rw [prior] at base
    have pass := (GeneralRebaseReceiptMachine289.published_exact w ask saved.offer (erase p)).mp base
    apply strict_passes_bounded (up := up)
    unfold boundedDecision
    rw [prior]
    exact pass.2.2

theorem no_typed_replay_with_live_request {r : Registry} {s : State roles}
    {up down : Occurrence roles} {ask : Offer} (p : Phase) (saved : Stamp)
    (out : GeneralSourceState.Output) (live : out ∈ requests s.core down) :
    step (capture s.core.erased.current.context.state up down ask)
      (strictTick r s up down ask) p ≠ some (.sent saved) :=
  fun result => GeneralRebaseReceiptLiveEffects289.actual_request_excludes_guard out live
    (strict_sent_implies_bounded_read result)

theorem actual_alias_excludes_typed_replay (r : Registry) (ask : Offer) (p : Phase) (saved : Stamp) :
    let s := GeneralRebaseMergeRegression264.merged
    let up := GeneralNominalCenteredHeadAllocMergeSource.root
    let down := GeneralNominalCenteredHeadAllocMergeInstall.aSite.occurrence
    step (capture s.core.erased.current.context.state up down ask)
      (strictTick r s up down ask) p ≠ some (.sent saved) :=
  no_typed_replay_with_live_request p saved GeneralRebaseMergeRegression264.last
    GeneralRebaseMergeRegression264.last_present

end Yulang.GeneralRebaseReceiptStampedEffects289
