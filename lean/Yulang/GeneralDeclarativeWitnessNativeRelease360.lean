import Yulang.GeneralDeclarativeWitnessNativeInstall360

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNativeRelease360
open GeneralDeclarativeWitnessNativeInstall360 (Board World Fits NativeViews atTarget interpreted)
open GeneralDeclarativeWitnessNativeValue360 (Address Write)
open GeneralDeclarativeWitnessTypedRelease354 (position)
open GeneralNominalCommonBridge (Assignment)

structure ReleaseAuthority where
  grants : List Address

structure Released (board : Board) (authority : ReleaseAuthority) (asked : Address) where
  stored : Write
  located : atTarget board asked.target = some stored
  identifies : stored.address = asked
  active : asked.owner ∈ board.active
  unique : (board.active.map position).Nodup
  granted : asked ∈ authority.grants

def openWrite (board : Board) (authority : ReleaseAuthority) (asked : Address) :
    Option (Released board authority asked) :=
  match actual : atTarget board asked.target with
  | none => none
  | some row =>
    if id : row.address = asked then
      if permitted : (asked.owner ∈ board.active ∧ (board.active.map position).Nodup) ∧
          asked ∈ authority.grants then
        some ⟨row,actual,id,permitted.1.1,permitted.1.2,permitted.2⟩
      else none
    else none

/-- A positive release uses the actual installed row at the exact target.
The grant cannot create a current row and current installation alone
is not a grant. No typed value is read from the ordinary target slot. -/
theorem release_current_value {w : World} {gate asked} (r : Released w.board gate asked)
    (m : Assignment) (views : NativeViews) (fit : Fits w m views) :
    views asked.target = some (r.stored.code.eval m) := by
  have eq := fit.2 asked.target
  unfold interpreted at eq
  rw [r.located] at eq
  exact eq

theorem not_installed_not_released {board gate addr}
    (noWrite : atTarget board addr.target = none) : openWrite board gate addr = none := by
  unfold openWrite
  split
  · rfl
  · rename_i row located
    rw [noWrite] at located
    cases located

theorem version_needs_current_authority {board gate addr}
    (old : addr.owner ∉ board.active) : openWrite board gate addr = none := by
  unfold openWrite
  split
  · rfl
  · split <;> simp [old]

theorem not_granted_not_released {board authority addr}
    (noPermit : addr ∉ authority.grants) : openWrite board authority addr = none := by
  unfold openWrite
  split
  · rfl
  · split <;> simp [noPermit]

structure ExactRelease (board : Board) (gate : ReleaseAuthority) (intended : Write) where
  released : Released board gate intended.address
  same : released.stored = intended

def checkExactRelease (board : Board) (gate : ReleaseAuthority) (intended : Write) :
    Option (ExactRelease board gate intended) := do
  let r ← openWrite board gate intended.address
  if exact : r.stored = intended then some ⟨r,exact⟩ else none

theorem checked_exact_written_value {w : World} {gate intended}
    (opened : ExactRelease w.board gate intended) (m : Assignment) (views : NativeViews)
    (fit : Fits w m views) : views intended.address.target = some (intended.code.eval m) := by
  simpa only [opened.same] using release_current_value opened.released m views fit

end Yulang.GeneralDeclarativeWitnessNativeRelease360
