import Yulang.GeneralRebaseReceiptStampedEffects289

/-! Exact cost pairs transfer through the typed stamp erasure without
counting a sidecar action as an underlying raw step. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 20000000
namespace Yulang.GeneralRebaseReceiptStampedCounts289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseReceiptStampedProduct289
open GeneralRebaseReceiptStampMachine289 (Phase erase lift Valid)
open GeneralRebaseReceiptScopedTrace289 (finalPhase)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State)

inductive Trace (choice : Bool) : Config → Nat → Nat → Prop
  | start : Trace choice initial 0 0
  | raw (s t : State roles) (p : Phase) :
    Trace choice ⟨s,p⟩ r a → Step (registry choice) root s t → Trace choice ⟨t,.scan⟩ (r+1) a
  | side (s : State roles) (p q : Phase) :
    Trace choice ⟨s,p⟩ r a → runPhase choice s p = some q → Trace choice ⟨s,q⟩ r (a+1)

theorem path {choice : Bool} {s : Config} {r a : Nat} (trace : Trace choice s r a) :
    B4Target.Steps (Next choice) initial s := by
  induction trace with
  | start => exact .refl
  | raw s t p _ old ih => exact .tail ih (.raw s t p old)
  | side s p q _ move ih => exact .tail ih (.side s p q move)

theorem erase_counts {choice : Bool} {s : Config} {r a : Nat} (trace : Trace choice s r a) :
    GeneralRebaseReceiptCounted289.Trace choice (project s) r a := by
  induction trace with
  | start => exact .start
  | raw s t p _ old ih => exact .raw s t (erase p) ih old
  | side s p q past move ih =>
    have valid := (project_path choice (path past)).1
    have actual := GeneralRebaseReceiptRawProduct289.erase_path choice (GeneralRebaseReceiptCounted289.path_erases ih)
    change B4Target.Steps (Step (registry choice) root) GeneralRebaseReceiptRawProduct289.initial.raw s at actual
    have projected := GeneralRebaseReceiptStampMachine289.erases_tick (currentStamp choice s)
      (GeneralRebaseReceiptAnchorProduct289.aux choice s) p valid
    change (runPhase choice s p).map erase = _ at projected
    rw [move,GeneralRebaseReceiptAnchorProduct289.agrees_raw choice actual] at projected
    exact .side s (erase p) (erase q) ih projected.symm

theorem preserve_counts {choice : Bool} {s : GeneralRebaseReceiptRawProduct289.Config} {r a : Nat}
    (trace : GeneralRebaseReceiptCounted289.Trace choice s r a) :
    Trace choice (decorate choice s) r a := by
  induction trace with
  | start => exact .start
  | raw s t p _ old ih => exact .raw _ _ _ ih old
  | side s p q past move ih =>
    have old := GeneralRebaseReceiptCounted289.path_erases past
    have valid := decorate_valid choice ((GeneralRebaseReceiptAnchorProduct289.paths_iff choice _).mpr old)
    have actual := GeneralRebaseReceiptRawProduct289.erase_path choice old
    refine .side _ _ _ ih ?_
    change Valid (currentStamp choice s) (lift (currentStamp choice s) p) at valid
    change runPhase choice s (lift (currentStamp choice s) p) = some (lift (currentStamp choice s) q)
    unfold runPhase
    rw [GeneralRebaseReceiptStampMachine289.stable_tick _ _ _ valid,
      GeneralRebaseReceiptStampMachine289.erase_lift,
      GeneralRebaseReceiptAnchorProduct289.agrees_raw choice actual,move]
    rfl

theorem exact_terminal_counts (choice : Bool) (r a : Nat) :
    (∃ x, Trace choice x r a ∧ ∀ t, ¬ Next choice x t) ↔
      r = 1 ∧ ∃ early ≤ 1, a = early + (if choice then 2 else 1) := by
  constructor
  · rintro ⟨s,trace,halt⟩
    have endAt := (GeneralRebaseReceiptStampedExport289.exact_terminal choice s).mp ⟨path trace,halt⟩
    have counts := erase_counts trace
    rw [endAt,GeneralRebaseReceiptStampedExport289.finish,project_decorate] at counts
    exact GeneralRebaseReceiptCounted289.final_counts choice r a counts
  · rintro ⟨rfl,early,bound,rfl⟩
    have old := GeneralRebaseReceiptCounted289.every_final_count choice early bound
    exact ⟨_,preserve_counts old,
      ((GeneralRebaseReceiptStampedExport289.exact_terminal choice _).mpr rfl).2⟩

end Yulang.GeneralRebaseReceiptStampedCounts289
