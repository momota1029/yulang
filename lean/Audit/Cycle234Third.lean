import Yulang.GeneralDictionaryMixedConflict199234
import Yulang.GeneralDictionaryMixedDefault202234
import Yulang.GeneralDictionaryMixedGap206Evidence234
import Yulang.GeneralDictionaryMixedGap206Frame234
import Yulang.GeneralDictionaryMixedGap206Selected234
import Yulang.GeneralDictionaryMixedGap206Stable234
import Yulang.GeneralDictionaryMixedJoin204234
import Yulang.GeneralNominalVersionedMixedStableTransfer234
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryMixedConflict199234,`Yulang.GeneralDictionaryMixedDefault202234,`Yulang.GeneralDictionaryMixedGap206Evidence234,`Yulang.GeneralDictionaryMixedGap206Frame234,`Yulang.GeneralDictionaryMixedGap206Selected234,`Yulang.GeneralDictionaryMixedGap206Stable234,`Yulang.GeneralDictionaryMixedJoin204234,`Yulang.GeneralNominalVersionedMixedStableTransfer234]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE234-THIRD-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE234-THIRD-FAIL: no constants checked"
  logInfo m!"CYCLE234-THIRD-PASS: {checked} constants in {modules.size} modules"
