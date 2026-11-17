import Yulang.GeneralNominalRebaseRawView243
import Yulang.GeneralNominalRebaseViewSubst243
import Yulang.GeneralNominalRebaseLiveView243
import Yulang.GeneralNominalRebaseOriginView243
import Yulang.GeneralNominalRebaseEffectView243
import Yulang.GeneralNominalRebaseActivation243
import Yulang.GeneralDictionaryRebaseActivation230243
import Yulang.GeneralNominalRebaseActivationCheck243
import Yulang.GeneralNominalRebaseActivationFresh243
import Yulang.GeneralNominalRebaseStablePool243
import Yulang.GeneralNominalRebaseInlineSupport243
import Yulang.GeneralNominalRebaseSourceSteps243
import Yulang.GeneralNominalRebaseEndpointProducer243
import Yulang.GeneralNominalRebaseViewSupport243
import Yulang.GeneralNominalRebaseViewActivation243
import Yulang.GeneralNominalRebaseProjectionView243
import Yulang.GeneralNominalRebaseSchemaView243
import Yulang.GeneralNominalRebasePacketView243
import Yulang.GeneralNominalRebaseEvidenceView243
import Yulang.GeneralDictionaryRebaseViewActivation230243
import Yulang.GeneralNominalRebaseOriginActivation243
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalRebaseRawView243, `Yulang.GeneralNominalRebaseViewSubst243, `Yulang.GeneralNominalRebaseLiveView243, `Yulang.GeneralNominalRebaseOriginView243, `Yulang.GeneralNominalRebaseEffectView243, `Yulang.GeneralNominalRebaseActivation243, `Yulang.GeneralDictionaryRebaseActivation230243, `Yulang.GeneralNominalRebaseActivationCheck243, `Yulang.GeneralNominalRebaseActivationFresh243, `Yulang.GeneralNominalRebaseStablePool243, `Yulang.GeneralNominalRebaseInlineSupport243, `Yulang.GeneralNominalRebaseSourceSteps243, `Yulang.GeneralNominalRebaseEndpointProducer243, `Yulang.GeneralNominalRebaseViewSupport243, `Yulang.GeneralNominalRebaseViewActivation243, `Yulang.GeneralNominalRebaseProjectionView243, `Yulang.GeneralNominalRebaseSchemaView243, `Yulang.GeneralNominalRebasePacketView243, `Yulang.GeneralNominalRebaseEvidenceView243, `Yulang.GeneralDictionaryRebaseViewActivation230243, `Yulang.GeneralNominalRebaseOriginActivation243]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE243-THIRD-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE243-THIRD-FAIL: no constants checked"
  logInfo m!"CYCLE243-THIRD-PASS: {checked} constants in {modules.size} modules"
