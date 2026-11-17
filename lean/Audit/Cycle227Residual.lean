import Yulang.GeneralDictionaryEmittedFootprint227
import Yulang.GeneralDictionaryFirstResidual227
import Yulang.GeneralDictionaryV8Residual227
import Yulang.GeneralDictionaryCapturePatch227
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryEmittedFootprint227,`Yulang.GeneralDictionaryFirstResidual227,`Yulang.GeneralDictionaryV8Residual227,`Yulang.GeneralDictionaryCapturePatch227]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE227-RESIDUAL-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE227-RESIDUAL-FAIL: no constants checked"
  logInfo m!"CYCLE227-RESIDUAL-PASS: {checked} constants in {modules.size} modules"
