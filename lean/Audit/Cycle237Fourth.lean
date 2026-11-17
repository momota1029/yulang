import Yulang.GeneralDictionaryVersionLoopNext237
import Yulang.GeneralDictionaryVersionLoopSource237
import Yulang.GeneralDictionaryVersionLoopPacket237
import Yulang.GeneralDictionaryVersionLoopFrame237
import Yulang.GeneralDictionaryVersionLoopFull237
import Yulang.GeneralDictionaryVersionLoopRefreshBase237
import Yulang.GeneralDictionaryVersionLoopRefresh237
import Yulang.GeneralDictionaryVersionLoopRetarget237
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryVersionLoopSource237, `Yulang.GeneralDictionaryVersionLoopPacket237, `Yulang.GeneralDictionaryVersionLoopFrame237, `Yulang.GeneralDictionaryVersionLoopFull237, `Yulang.GeneralDictionaryVersionLoopRefreshBase237, `Yulang.GeneralDictionaryVersionLoopRefresh237, `Yulang.GeneralDictionaryVersionLoopRetarget237, `Yulang.GeneralDictionaryVersionLoopNext237]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE237-FOURTH-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE237-FOURTH-FAIL: no constants checked"
  logInfo m!"CYCLE237-FOURTH-PASS: {checked} constants in {modules.size} modules"
