import Yulang.GeneralDeclarativeWitnessActualWhereConflict363

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 82000
set_option maxHeartbeats 95000000
namespace Yulang.GeneralDeclarativeWitnessCurrentAuthority363
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run authority address)
open GeneralDeclarativeWitnessNativeRelease360
  (ReleaseAuthority ExactRelease checkExactRelease not_granted_not_released checked_exact_written_value)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews interpreted)
open GeneralDeclarativeWitnessSelectedNonpointChild363 (Complete close)
open GeneralDeclarativeWitnessSelectedSourceMeaning363
  (Local Meaning rootQuery every_actual_selected_dictionary_same_model)
open GeneralDeclarativeWitnessOrderedDictionary363 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify)

structure Grant {contra : Bool} (x : Ordered contra) (gate : ReleaseAuthority) where
  low : ExactRelease x.after.final.board gate x.before.native.write
  mid : ExactRelease x.after.final.board gate x.center.native.write
  high : ExactRelease x.after.final.board gate x.after.native.write

def openCurrent {contra} (x : Ordered contra) (gate : ReleaseAuthority) : Option (Grant x gate) := do
  let low ← checkExactRelease x.after.final.board gate x.before.native.write
  let mid ← checkExactRelease x.after.final.board gate x.center.native.write
  let high ← checkExactRelease x.after.final.board gate x.after.native.write
  pure ⟨low,mid,high⟩

structure Scoped {contra : Bool} (x : Ordered contra) (gate : ReleaseAuthority) where
  permitted : Grant x gate
  closed : Complete x

def authorizedClose {contra} (x : Ordered contra) (gate : ReleaseAuthority) : Option (Scoped x gate) := do
  let now ← openCurrent x gate
  let closed ← close x
  pure ⟨now,closed⟩

theorem scoped_dictionary_sound {contra} {x : Ordered contra} {gate : ReleaseAuthority}
    (present : Scoped x gate) (made : run contra = some x)
    (m : Assignment) (v : NativeViews) (fit : Fits present.closed.child.world m v)
    {d dict} (selected : Classify (Local present.closed) d (.selected dict)) :
    Evidence (Meaning present.closed m v) d dict ∧
      x.center.native.write.address ∈ gate.grants ∧
      v x.center.native.write.address.target = some (x.center.native.write.code.eval m) := by
  have prior := (GeneralDeclarativeWitnessSelectedNonpointChild363.returned_model_has_prior_author_and_child_state
    present.closed.child m v fit).2
  exact ⟨every_actual_selected_dictionary_same_model present.closed made m v fit selected,
    present.permitted.mid.released.granted,
    checked_exact_written_value (w := x.after.final) present.permitted.mid m v prior⟩

def noMid : ReleaseAuthority := ⟨[address 0,address 2]⟩

/-- Change only the grant set, not the installed values, model, exact
ordinary equations, declarations, or scope of the actual compiling code. -/
def check {contra} (x : Ordered contra) : Bool :=
  (authorizedClose x authority).isSome &&
  (checkExactRelease x.after.final.board noMid x.before.native.write).isSome &&
  (checkExactRelease x.after.final.board noMid x.center.native.write).isNone &&
  (checkExactRelease x.after.final.board noMid x.after.native.write).isSome &&
  (close x).isSome && (authorizedClose x noMid).isNone

theorem removing_only_current_center_permission_changes_certificate (contra : Bool) :
    ((run contra).map check).getD false = true := by cases contra <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessCurrentAuthority363
