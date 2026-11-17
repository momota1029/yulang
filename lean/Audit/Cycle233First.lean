import Yulang.GeneralDictionaryVersionedBothModel233
import Yulang.GeneralDictionaryVersionedBothPacket233
import Yulang.GeneralDictionaryVersionedBothStage233
import Yulang.GeneralDictionaryVersionedInitialFrame233
import Yulang.GeneralDictionaryVersionedInitialModel233
import Yulang.GeneralDictionaryVersionedInitialPacket233
import Yulang.GeneralDictionaryVersionedInitialStep233
import Yulang.GeneralDictionaryVersionedInitialTransport233
import Yulang.GeneralDictionaryVersionedPoint233
import Yulang.GeneralDictionaryVersionedPointFrame233
import Yulang.GeneralDictionaryVersionedPointFresh233
import Yulang.GeneralDictionaryVersionedPointSafety233
import Yulang.GeneralDictionaryVersionedPointStage233
import Yulang.GeneralDictionaryVersionedReobserve233
import Yulang.GeneralDictionaryVersionedSecondInstall233
import Yulang.GeneralDictionaryVersionedSecondStep233
import Yulang.GeneralDictionaryVersionedVariant233
import Yulang.GeneralNominalVersionedInstalledEvidence233
import Yulang.GeneralNominalVersionedInstalledEvidenceAt233
import Yulang.GeneralNominalVersionedTerminalStable233
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryVersionedBothModel233,`Yulang.GeneralDictionaryVersionedBothPacket233,`Yulang.GeneralDictionaryVersionedBothStage233,`Yulang.GeneralDictionaryVersionedInitialFrame233,`Yulang.GeneralDictionaryVersionedInitialModel233,`Yulang.GeneralDictionaryVersionedInitialPacket233,`Yulang.GeneralDictionaryVersionedInitialStep233,`Yulang.GeneralDictionaryVersionedInitialTransport233,`Yulang.GeneralDictionaryVersionedPoint233,`Yulang.GeneralDictionaryVersionedPointFrame233,`Yulang.GeneralDictionaryVersionedPointFresh233,`Yulang.GeneralDictionaryVersionedPointSafety233,`Yulang.GeneralDictionaryVersionedPointStage233,`Yulang.GeneralDictionaryVersionedReobserve233,`Yulang.GeneralDictionaryVersionedSecondInstall233,`Yulang.GeneralDictionaryVersionedSecondStep233,`Yulang.GeneralDictionaryVersionedVariant233,`Yulang.GeneralNominalVersionedInstalledEvidence233,`Yulang.GeneralNominalVersionedInstalledEvidenceAt233,`Yulang.GeneralNominalVersionedTerminalStable233]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE233-FIRST-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE233-FIRST-FAIL: no constants checked"
  logInfo m!"CYCLE233-FIRST-PASS: {checked} constants in {modules.size} modules"
