import Yulang.GeneralNominalAssignmentCongruence238
import Yulang.GeneralNominalAcyclicNormalization238
import Yulang.GeneralNominalRawCongruence238
import Yulang.GeneralNominalVersionedHistoryNormalization238
import Yulang.GeneralDictionaryVersionLoopFresh238
import Yulang.GeneralDictionaryVersionLoopInitial238
import Yulang.GeneralDictionaryVersionLoopCycles238
import Yulang.GeneralDictionaryVersionLoopSafety238
import Yulang.GeneralDictionaryVersionLoopInstall238
import Yulang.GeneralDictionaryVersionLoopPrefix238
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalAssignmentCongruence238, `Yulang.GeneralNominalAcyclicNormalization238, `Yulang.GeneralNominalRawCongruence238, `Yulang.GeneralNominalVersionedHistoryNormalization238, `Yulang.GeneralDictionaryVersionLoopFresh238, `Yulang.GeneralDictionaryVersionLoopInitial238, `Yulang.GeneralDictionaryVersionLoopCycles238, `Yulang.GeneralDictionaryVersionLoopSafety238, `Yulang.GeneralDictionaryVersionLoopInstall238, `Yulang.GeneralDictionaryVersionLoopPrefix238]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE238-FIRST-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE238-FIRST-FAIL: no constants checked"
  logInfo m!"CYCLE238-FIRST-PASS: {checked} constants in {modules.size} modules"
