import Yulang.GeneralDictionaryPointCompound240
import Yulang.GeneralDictionaryPointGap206240
import Yulang.GeneralDictionaryPointGround218240
import Yulang.GeneralDictionaryPointOptional240
import Yulang.GeneralDictionaryPointReobserve240
import Yulang.GeneralDictionaryPointRevisions240
import Yulang.GeneralDictionaryVersionLoopBlocked240
import Yulang.GeneralNominalPointBoundary240
import Yulang.GeneralNominalPointEqualityTrace240
import Yulang.GeneralNominalPointErasure240
import Yulang.GeneralNominalPointKernel240
import Yulang.GeneralNominalPointRecord240
import Yulang.GeneralNominalPointRecordSteps240
import Yulang.GeneralNominalPointRevision240
import Yulang.GeneralNominalPointSourceBoundary240
import Yulang.GeneralNominalPointTransport240
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryPointCompound240, `Yulang.GeneralDictionaryPointGap206240, `Yulang.GeneralDictionaryPointGround218240, `Yulang.GeneralDictionaryPointOptional240, `Yulang.GeneralDictionaryPointReobserve240, `Yulang.GeneralDictionaryPointRevisions240, `Yulang.GeneralDictionaryVersionLoopBlocked240, `Yulang.GeneralNominalPointBoundary240, `Yulang.GeneralNominalPointEqualityTrace240, `Yulang.GeneralNominalPointErasure240, `Yulang.GeneralNominalPointKernel240, `Yulang.GeneralNominalPointRecord240, `Yulang.GeneralNominalPointRecordSteps240, `Yulang.GeneralNominalPointRevision240, `Yulang.GeneralNominalPointSourceBoundary240, `Yulang.GeneralNominalPointTransport240]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE240-FIRST-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE240-FIRST-FAIL: no constants checked"
  logInfo m!"CYCLE240-FIRST-PASS: {checked} constants in {modules.size} modules"
