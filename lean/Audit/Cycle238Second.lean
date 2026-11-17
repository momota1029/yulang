import Yulang.GeneralDictionaryCompoundSource238
import Yulang.GeneralDictionaryCompoundPacket238
import Yulang.GeneralDictionaryCompoundModel238
import Yulang.GeneralDictionaryCompoundTotal238
import Yulang.GeneralDictionaryCompoundVersionedModel238
import Yulang.GeneralDictionaryCompoundVersionedPacket238
import Yulang.GeneralDictionaryCompoundFrame238
import Yulang.GeneralDictionaryCompoundStep238
import Yulang.GeneralDictionaryCompoundCurrent238
import Yulang.GeneralDictionaryCompoundPoint238
import Yulang.GeneralDictionaryCompoundObstruction238
import Yulang.GeneralDictionaryVersionLoopSecondPacket238
import Yulang.GeneralDictionaryVersionLoopSecondFull238
import Yulang.GeneralDictionaryVersionLoopSecondFrame238
import Yulang.GeneralDictionaryVersionLoopSecondSafety238
import Yulang.GeneralDictionaryVersionLoopSecondInstall238
import Yulang.GeneralDictionaryVersionLoopSecondNovel238
import Yulang.GeneralDictionaryVersionLoopSecondStep238
import Yulang.GeneralDictionaryVersionLoopNames238
import Yulang.GeneralNominalOriginCongruence238
import Yulang.GeneralNominalProjectionCongruence238
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryCompoundSource238, `Yulang.GeneralDictionaryCompoundPacket238, `Yulang.GeneralDictionaryCompoundModel238, `Yulang.GeneralDictionaryCompoundTotal238, `Yulang.GeneralDictionaryCompoundVersionedModel238, `Yulang.GeneralDictionaryCompoundVersionedPacket238, `Yulang.GeneralDictionaryCompoundFrame238, `Yulang.GeneralDictionaryCompoundStep238, `Yulang.GeneralDictionaryCompoundCurrent238, `Yulang.GeneralDictionaryCompoundPoint238, `Yulang.GeneralDictionaryCompoundObstruction238, `Yulang.GeneralDictionaryVersionLoopSecondPacket238, `Yulang.GeneralDictionaryVersionLoopSecondFull238, `Yulang.GeneralDictionaryVersionLoopSecondFrame238, `Yulang.GeneralDictionaryVersionLoopSecondSafety238, `Yulang.GeneralDictionaryVersionLoopSecondInstall238, `Yulang.GeneralDictionaryVersionLoopSecondNovel238, `Yulang.GeneralDictionaryVersionLoopSecondStep238, `Yulang.GeneralDictionaryVersionLoopNames238, `Yulang.GeneralNominalOriginCongruence238, `Yulang.GeneralNominalProjectionCongruence238]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE238-SECOND-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE238-SECOND-FAIL: no constants checked"
  logInfo m!"CYCLE238-SECOND-PASS: {checked} constants in {modules.size} modules"
