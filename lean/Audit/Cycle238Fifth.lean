import Yulang.GeneralDictionaryCompoundChildPending238
import Yulang.GeneralDictionaryCompoundVacuity238
import Yulang.GeneralDictionaryVersionLoopFamilyInstallation238
import Yulang.GeneralDictionaryVersionLoopFamilyExpose238
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryCompoundChildPending238, `Yulang.GeneralDictionaryCompoundVacuity238, `Yulang.GeneralDictionaryVersionLoopFamilyInstallation238, `Yulang.GeneralDictionaryVersionLoopFamilyExpose238]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE238-FIFTH-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE238-FIFTH-FAIL: no constants checked"
  logInfo m!"CYCLE238-FIFTH-PASS: {checked} constants in {modules.size} modules"
