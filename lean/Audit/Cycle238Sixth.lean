import Yulang.GeneralDictionaryVersionLoopFamilyHistory238
import Yulang.GeneralDictionaryVersionLoopFamilyTrusted238
import Yulang.GeneralDictionaryVersionLoopFamilyCache238
import Yulang.GeneralDictionaryVersionLoopFamilyRefresh238
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryVersionLoopFamilyHistory238, `Yulang.GeneralDictionaryVersionLoopFamilyTrusted238, `Yulang.GeneralDictionaryVersionLoopFamilyCache238, `Yulang.GeneralDictionaryVersionLoopFamilyRefresh238]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE238-SIXTH-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE238-SIXTH-FAIL: no constants checked"
  logInfo m!"CYCLE238-SIXTH-PASS: {checked} constants in {modules.size} modules"
