import Yulang.GeneralDictionaryUpper230Base
import Yulang.GeneralDictionaryUpper230Snapshot
import Yulang.GeneralDictionaryUpper230Refresh
import Yulang.GeneralDictionaryUpper230Step
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryUpper230Base,`Yulang.GeneralDictionaryUpper230Snapshot,`Yulang.GeneralDictionaryUpper230Refresh,`Yulang.GeneralDictionaryUpper230Step]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE230-COMPLETION-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE230-COMPLETION-FAIL: no constants checked"
  logInfo m!"CYCLE230-COMPLETION-PASS: {checked} constants in {modules.size} modules"
