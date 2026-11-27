import Yulang.GeneralDeclarativeI65I74PreparedBoundRetraction467
import Yulang.GeneralDeclarativeI65I74ReceivedPhaseReplay467
import Yulang.GeneralDeclarativeWitnessInheritedModeFixture357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 58000
set_option maxHeartbeats 45000000
namespace Yulang.GeneralDeclarativeI65.I72.PreparedBoundRetraction467.Actual
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeI65.I72.CheckedPreparedRetraction467
open GeneralDeclarativeI65.I72.CheckedPreparationObservations467
open GeneralDeclarativeI65.I72.ReceivedPhaseReplay467
open GeneralDeclarativeWitnessReleasedForward360 (originalBody)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence sequence appended)
open GeneralDeclarativeWitnessSequentialReceiver361 (receive)
open GeneralDeclarativeWitnessNativeDirectSource361 (actualWire)
open GeneralDeclarativeWitnessNativePipeline360 (authority)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessNativeInstall360 (atTarget)
open GeneralDeclarativeWitnessBound349 (Path)

private def mapCode : List (Nat × Nat) := [(116,112),(117,113)]

private def checkReceipts {negative} {r : GeneralDeclarativeWitnessNestedInstall360.Run negative}
    (first : Sequence r) (later : GeneralDeclarativeWitnessSequentialReceiver361.Received first) : List Bool :=
  let old := first.final.ordinary
  let latest := later.world.ordinary
  let baseIndex := old.normal.ordinary.length - appended.length
  let proofs : List Path := [.refl 101,.refl 101,.refl 112,.refl 112,.refl 113,.refl 113,
    .constraint (baseIndex+2),.constraint (baseIndex+5)]
  let wrong : List Path := [.refl 101,.refl 101,.refl 112,.refl 112,.refl 113,.refl 113,
    .constraint (baseIndex+3),.constraint (baseIndex+5)]
  let row := originalOfWrite r.typed.write
  let ledger : SuppliedReceiverLedger := ⟨latest,[],table,[row],[]⟩
  let oldLedger := {ledger with ordinary := old}
  [checkProjectedPreparation old latest mapCode 101 proofs,
    checkProjectedPreparation old latest mapCode 112 proofs,
    checkProjectedPreparation old latest mapCode 116 proofs,
    checkProjectedPreparation old latest mapCode 101 wrong,
    checkProjectedPreparation old latest mapCode 101 (proofs.take 7),
    checkOrdinaryObservationRetraction old latest mapCode 101,
    checkForwardedInActualReceiver first ledger authority actualWire 0,
    checkForwardedInActualReceiver first oldLedger authority actualWire 0,
    (atTarget later.world.board 116).isNone,
    decide (atTarget later.world.board 101 = some r.typed.write)]

private def actual : Option (List Bool) := do
  let parent ← originalBody false
  let first ← sequence parent
  let next ← receive first
  pure (checkReceipts first next)

theorem authentic_receiver_uses_proved_old_bounds_without_identifying_the_two_snapshots :
    actual = some [true,true,false,false,false,false,true,false,true,true] := by
  decide +kernel

/-- info: some [true, true, false, false, false, false, true, false, true, true] -/
#guard_msgs in
#eval actual

#print axioms authentic_receiver_uses_proved_old_bounds_without_identifying_the_two_snapshots
end Yulang.GeneralDeclarativeI65.I72.PreparedBoundRetraction467.Actual
