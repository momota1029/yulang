import Yulang.GeneralDeclarativeI65I74ExistingForwardedAddress467
import Yulang.GeneralDeclarativeWitnessInheritedModeFixture357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 59000
set_option maxHeartbeats 57000000
namespace Yulang.GeneralDeclarativeI65.I72.ExistingForwardedAddress467.Actual
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeI65.I72.NativeProducer465
open GeneralDeclarativeWitnessReleasedForward360 (originalBody)
open GeneralDeclarativeWitnessSequentialNative360 (sequence)
open GeneralDeclarativeWitnessSequentialReceiver361 (receive exact_run_is_inhabited model)
open GeneralDeclarativeWitnessNativePortTransport361 (transport wrongOperand)
open GeneralDeclarativeWitnessNativeDirectSource361 (actualWire)
open GeneralDeclarativeWitnessNativePipeline360 (authority authorizedAddress)
open GeneralDeclarativeWitnessNativeInstall360 (atTarget)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)

private def observation (changed : Bool) : Option (List Bool) := do
  let parent ← originalBody false
  let stage ← sequence parent
  let received ← receive stage
  let witness ← transport stage authority (if changed then wrongOperand else actualWire)
  let actual := originalOfWrite parent.typed.write
  let world := received.world
  let core : GeneralDeclarativeI65.State := ⟨⟨parent.env,world.ordinary,[]⟩,table,[actual],[]⟩
  let active : CheckedPhase core := ⟨world,rfl,authority⟩
  let place := received.span
  pure [decide (place.lower = 116 ∧ place.center = 101 ∧ place.upper = 117),
    decide (parent.typed.write.address = authorizedAddress),
    decide (atTarget world.board 101 = some parent.typed.write),
    (atTarget world.board 116).isNone,(atTarget world.board 117).isNone,
    received.body.fixed.isEmpty,
    checkPhaseOrigin active parent.typed.write 101 0,
    checkPhaseOrigin active parent.typed.write 116 0,
    checkPhaseOrigin active parent.typed.write 117 0,
    checkPhaseOrigin active parent.typed.write 101 1,
    decide (witness.stated.seed.center = parent.typed.write.address.target)]

theorem real_reception_preserves_the_old_grant_without_issuing_fresh_window_coordinates :
    observation false = some [true,true,true,true,true,true,true,false,false,false,true] ∧
      observation true = none := by
  constructor <;> decide +kernel

theorem the_concrete_compiler_receiver_phase_has_a_fitting_assignment_and_actual_address :
    ∃ (parent : GeneralDeclarativeWitnessNestedInstall360.Run false)
      (stage : GeneralDeclarativeWitnessSequentialNative360.Sequence parent)
      (received : GeneralDeclarativeWitnessSequentialReceiver361.Received stage),
      originalBody false = some parent ∧ sequence parent = some stage ∧ receive stage = some received ∧
      GeneralDeclarativeWitnessNativeInstall360.Fits received.world (model false .int)
        (GeneralDeclarativeWitnessNativeInstall360.interpreted received.world.board (model false .int)) ∧
      received.span.center = parent.typed.write.address.target ∧ received.body.fixed = [] := by
  obtain ⟨parent,stage,rec,root,sent,ran,_,_,_,_,fitted⟩ := exact_run_is_inhabited false
  exact ⟨parent,stage,rec,root,sent,ran,fitted false .int,rec.center.trans stage.readsNative,rec.noWrites⟩

/-- info: (some [true, true, true, true, true, true, true, false, false, false, true], none) -/
#guard_msgs in
#eval (observation false,observation true)

#print axioms real_reception_preserves_the_old_grant_without_issuing_fresh_window_coordinates
#print axioms the_concrete_compiler_receiver_phase_has_a_fitting_assignment_and_actual_address
end Yulang.GeneralDeclarativeI65.I72.ExistingForwardedAddress467.Actual
