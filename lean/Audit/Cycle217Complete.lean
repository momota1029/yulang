import Yulang.GeneralDictionaryCurrentAgreement217
import Yulang.GeneralDictionaryCurrentChosen217
import Yulang.GeneralDictionaryCurrentHeadEquations217
import Yulang.GeneralDictionaryLooseGround217
import Yulang.GeneralDictionaryLooseVariant217
import Yulang.GeneralDictionaryObservationPersistence217
import Yulang.GeneralDictionaryPointObservation217
import Yulang.GeneralDictionarySharingObstruction217
import Yulang.GeneralDictionaryTopLevelSharing217
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryCurrentAgreement217, `Yulang.GeneralDictionaryCurrentChosen217, `Yulang.GeneralDictionaryCurrentHeadEquations217, `Yulang.GeneralDictionaryLooseGround217, `Yulang.GeneralDictionaryLooseVariant217, `Yulang.GeneralDictionaryObservationPersistence217, `Yulang.GeneralDictionaryPointObservation217, `Yulang.GeneralDictionarySharingObstruction217, `Yulang.GeneralDictionaryTopLevelSharing217]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if modules.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE217-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE217-GATE-FAIL: no constants checked"
  logInfo m!"CYCLE217-GATE-PASS: {checked} constants in {modules.size} modules"
