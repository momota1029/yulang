import Yulang.GeneralDeclarativeWitnessWholeSound361

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessAuthorityTruthCut361
open GeneralDeclarativeWitnessNativeInstall360 (World Fits atTarget interpreted NativeViews)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessNativeRelease360
  (ReleaseAuthority ExactRelease checkExactRelease version_needs_current_authority checked_exact_written_value)
open GeneralNominalCommonBridge (Assignment)

def withoutOwner (w : World) (intended : Write) : World :=
  {w with board := {w.board with active := w.board.active.filter (fun x => decide (x ≠ intended.address.owner))}}

theorem cannot_be_active (w : World) (intended : Write) :
    intended.address.owner ∉ (withoutOwner w intended).board.active := by
  intro issued
  exact (of_decide_eq_true (List.mem_filter.mp issued).2) rfl

theorem removing_authority_keeps_actual_reads (w : World) (intended : Write) (m : Assignment) (v : NativeViews) :
    (Fits (withoutOwner w intended) m v ↔ Fits w m v) ∧
    atTarget (withoutOwner w intended).board intended.address.target =
      atTarget w.board intended.address.target := ⟨Iff.rfl,rfl⟩

theorem reading_the_value_cannot_recover_current_release {w : World} {gate : ReleaseAuthority} {row : Write}
    (present : ExactRelease w.board gate row) (m : Assignment) (v : NativeViews) (fit : Fits w m v) :
    Fits (withoutOwner w row) m v ∧
    v row.address.target = some (row.code.eval m) ∧
    (atTarget (withoutOwner w row).board row.address.target = some row) ∧
    row.address ∈ gate.grants ∧ checkExactRelease (withoutOwner w row).board gate row = none := by
  have disabled := version_needs_current_authority (gate := gate) (cannot_be_active w row)
  have noRun : checkExactRelease (withoutOwner w row).board gate row = none := by
    unfold checkExactRelease
    simp [disabled]
  have found : atTarget (withoutOwner w row).board row.address.target = some row := by
    change atTarget w.board row.address.target = some row
    exact present.released.located.trans (congrArg some present.same)
  exact ⟨fit,checked_exact_written_value present m v fit,found,
    present.released.granted,noRun⟩

end Yulang.GeneralDeclarativeWitnessAuthorityTruthCut361
