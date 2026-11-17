import Yulang.GeneralDictionaryMergeOwnership228
import Yulang.GeneralDictionarySiteFootprint228
import Yulang.GeneralDictionaryResidualOwnership228
import Yulang.GeneralDictionaryCapturedOwnership228
import Yulang.GeneralDictionaryFirstOwnership228
import Yulang.GeneralDictionaryFirstExtreme228
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryMergeOwnership228,`Yulang.GeneralDictionarySiteFootprint228,`Yulang.GeneralDictionaryResidualOwnership228,`Yulang.GeneralDictionaryCapturedOwnership228,`Yulang.GeneralDictionaryFirstOwnership228,`Yulang.GeneralDictionaryFirstExtreme228]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE228-OWNERSHIP-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE228-OWNERSHIP-FAIL: no constants checked"
  logInfo m!"CYCLE228-OWNERSHIP-PASS: {checked} constants in {modules.size} modules"
