import Yulang.GeneralDeclarativeI65I74ReceivedPhaseReplay467
import Yulang.GeneralDeclarativeWitnessInheritedModeFixture357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 59000
set_option maxHeartbeats 57000000
namespace Yulang.GeneralDeclarativeI65.I72.ReceivedPhaseReplay467.Actual
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessReleasedForward360 (originalBody)
open GeneralDeclarativeWitnessSequentialNative360 (sequence)
open GeneralDeclarativeWitnessSequentialReceiver361 (receive)
open GeneralDeclarativeWitnessNativePortTransport361 (wrongDeclarationOrder wrongOperand)
open GeneralDeclarativeWitnessNativeDirectSource361 (actualWire)
open GeneralDeclarativeWitnessNativePipeline360 (authority)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeHead320 (Equation)

private def comparison : Option (List Bool) := do
  let parent ← originalBody false
  let sent ← sequence parent
  let actual ← receive sent
  let origin := originalOfWrite parent.typed.write
  let good : SuppliedReceiverLedger := ⟨actual.world.ordinary,[],table,[origin],[]⟩
  let old : SuppliedReceiverLedger := {good with ordinary := sent.final.ordinary}
  let reflexive : Equation := ⟨710,.variable 710⟩
  let relabeled : SuppliedReceiverLedger :=
    {good with ordinary := {good.ordinary with equations := good.ordinary.equations ++ [reflexive]}}
  let missing : SuppliedReceiverLedger := {good with origins := []}
  let differentOrigin : Origin := {origin with issuer := [7,0]}
  let differentIssuer : SuppliedReceiverLedger := {good with origins := [differentOrigin]}
  pure [checkForwardedInActualReceiver sent good authority actualWire 0,
    checkForwardedInActualReceiver sent old authority actualWire 0,
    checkForwardedInActualReceiver sent relabeled authority actualWire 0,
    checkForwardedInActualReceiver sent missing authority actualWire 0,
    checkForwardedInActualReceiver sent differentIssuer authority actualWire 0,
    checkForwardedInActualReceiver sent good ⟨[]⟩ actualWire 0,
    checkForwardedInActualReceiver sent good authority actualWire 1,
    checkForwardedInActualReceiver sent good authority wrongDeclarationOrder 0,
    checkForwardedInActualReceiver sent good authority wrongOperand 0]

theorem actual_reader_preserves_original_output_and_rejects_wrong_phase_and_source :
    comparison = some [true,false,false,false,false,false,false,false,false] := by
  decide +kernel

/-- info: some [true, false, false, false, false, false, false, false, false] -/
#guard_msgs in
#eval comparison

#print axioms actual_reader_preserves_original_output_and_rejects_wrong_phase_and_source
end Yulang.GeneralDeclarativeI65.I72.ReceivedPhaseReplay467.Actual
