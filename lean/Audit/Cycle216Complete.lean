import Yulang.GeneralDictionaryMergeSlots216
import Yulang.GeneralDictionaryMergeCompletion216
import Yulang.GeneralDictionaryLiveSupport216
import Yulang.GeneralDictionaryInitialMerge216
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryMergeSlots216, `Yulang.GeneralDictionaryMergeCompletion216, `Yulang.GeneralDictionaryLiveSupport216, `Yulang.GeneralDictionaryInitialMerge216]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if modules.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE216-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE216-GATE-FAIL: no constants checked"
  logInfo m!"CYCLE216-GATE-PASS: {checked} constants in {modules.size} modules"
