import Yulang.GeneralDictionaryEffectProvenance227
import Yulang.GeneralDictionaryPointCaptureSupport227
import Yulang.GeneralDictionaryBinderProvenance227
import Yulang.GeneralDictionaryHeadFootprint227
import Yulang.GeneralDictionaryFirstPacketTail227
import Yulang.GeneralDictionaryCaptureDichotomy227
import Yulang.GeneralDictionaryFootprintRegression227
import Yulang.GeneralDictionaryV8Footprint227
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryEffectProvenance227,`Yulang.GeneralDictionaryPointCaptureSupport227,`Yulang.GeneralDictionaryBinderProvenance227,`Yulang.GeneralDictionaryHeadFootprint227,`Yulang.GeneralDictionaryFirstPacketTail227,`Yulang.GeneralDictionaryCaptureDichotomy227,`Yulang.GeneralDictionaryFootprintRegression227,`Yulang.GeneralDictionaryV8Footprint227]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE227-FINAL-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE227-FINAL-FAIL: no constants checked"
  logInfo m!"CYCLE227-FINAL-PASS: {checked} constants in {modules.size} modules"
