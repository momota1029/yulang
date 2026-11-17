import Yulang.GeneralDictionaryUpper230Regression
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryUpper230Equality,`Yulang.GeneralDictionaryUpper230Regression]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE230-FINAL-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE230-FINAL-FAIL: no constants checked"
  logInfo m!"CYCLE230-FINAL-PASS: {checked} constants in {modules.size} modules"
