import Yulang.GeneralRebaseReceiptStampedCounts289

/-! Executable replay on normalized wire data agrees with the strict
typed product at both actual installed journal endpoints. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 20000000
namespace Yulang.GeneralRebaseReceiptCheckedReplay289
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseReceiptFixture289 (request expectedWire wire_exact)
open GeneralRebaseReceiptStampMachine289 (Phase step erase)
open GeneralRebaseReceiptStampFixtures289 (normalizedStamp same_extracted_stamp wrongRow describe)
open GeneralRebaseReceiptStampedProduct289 (runPhase)
open GeneralRebaseReceiptMachine289 (tick)
open GeneralRebaseReceiptCompile289 (Mark actualMark observe concrete_compile)
open GeneralRebaseRowChildSource287 (root)

def installedTick (choice : Bool) (p : Phase) : Option Phase :=
  step (normalizedStamp choice) (tick (expectedWire choice) (request choice)) p

theorem installed_tick_exact (choice : Bool) (p : Phase) :
    runPhase choice (after choice) p = installedTick choice p := by
  unfold runPhase installedTick
  rw [same_extracted_stamp]
  have path : GeneralRebaseReceiptWitness289.ActualPath choice (after choice) :=
    .tail .refl (GeneralRebaseRowParentStep287.actual_step choice)
  have same : GeneralRebaseReceiptAnchorProduct289.aux choice (after choice) =
      tick (expectedWire choice) (request choice) := by
    funext phase
    rw [GeneralRebaseReceiptAnchorProduct289.agrees_raw choice path,wire_exact]
  rw [same]

def replay (choice : Bool) : List String × Option Mark :=
  let check := installedTick choice .scan
  let publish := check.bind (installedTick choice)
  ([describe check,describe publish],publish.bind (fun p => observe root (erase p)))

theorem positive_replay : replay true = (["receipt","published"],some actualMark) := by
  decide +kernel

theorem pending_replay : replay false = (["inspection-pending","none"],none) := by
  decide +kernel

theorem actual_stale_row :
    runPhase true (after true) (.held wrongRow) = some (.stopped .stale) := by
  rw [installed_tick_exact]
  exact GeneralRebaseReceiptStampFixtures289.wrong_row_stale

theorem replay_agrees (choice : Bool) :
    let tickActual := runPhase choice (after choice)
    let check := tickActual .scan
    let publish := check.bind tickActual
    replay choice = ([describe check,describe publish],publish.bind (fun p => observe root (erase p))) := by
  have eq : installedTick choice = runPhase choice (after choice) :=
    funext (fun p => (installed_tick_exact choice p).symm)
  unfold replay
  rw [eq]

theorem observes_exact (choice : Bool) {s : GeneralRebaseReceiptStampedProduct289.Config}
    (path : B4Target.Steps (GeneralRebaseReceiptStampedProduct289.Next choice)
      GeneralRebaseReceiptStampedProduct289.initial s) (value : Mark) :
    observe root (erase s.phase) = some value ↔
      choice = true ∧ s = GeneralRebaseReceiptStampedExport289.finish choice ∧ value = actualMark := by
  have anchored := (GeneralRebaseReceiptStampedProduct289.project_path choice path)
  have old := (GeneralRebaseReceiptAnchorProduct289.paths_iff choice _).mp anchored.2
  have released := GeneralRebaseReceiptPoint289.release_exact choice old value
  constructor
  · intro pub
    obtain ⟨yes,raw,phase,rfl⟩ := released.mp pub
    have structural : GeneralRebaseReceiptStampedProduct289.project s =
      ⟨after choice,GeneralRebaseReceiptScopedTrace289.finalPhase choice⟩ := by
      subst choice
      cases s with
      | mk ss pp =>
        change ss = after true at raw
        change erase pp = .published (request true) at phase
        unfold GeneralRebaseReceiptStampedProduct289.project
        rw [raw,phase]
        rfl
    refine ⟨yes,?_,rfl⟩
    unfold GeneralRebaseReceiptStampedExport289.finish
    rw [← structural,GeneralRebaseReceiptStampedProduct289.decorate_project _ _ anchored.1]
  · rintro ⟨rfl,final,rfl⟩
    rw [final]
    change observe root (GeneralRebaseReceiptStampMachine289.erase
      (GeneralRebaseReceiptStampMachine289.lift _ (GeneralRebaseReceiptScopedTrace289.finalPhase true))) = some actualMark
    rw [GeneralRebaseReceiptStampMachine289.erase_lift]
    exact concrete_compile true

end Yulang.GeneralRebaseReceiptCheckedReplay289
