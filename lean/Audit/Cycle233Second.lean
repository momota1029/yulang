import Yulang.GeneralDictionaryVersionedPointEvidenceAt233
import Yulang.GeneralDictionaryVersionedPointInstalledSelected233
import Yulang.GeneralDictionaryVersionedRegression233
import Yulang.GeneralDictionaryVersionedSecondEquality233
import Yulang.GeneralDictionaryVersionedSecondRaw233
import Yulang.GeneralDictionaryVersionedSecondRefresh233
import Yulang.GeneralDictionaryVersionedSecondSelected233
import Yulang.GeneralDictionaryVersionedSecondStable233
import Yulang.GeneralNominalVersionedGrowth233
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryVersionedPointEvidenceAt233,`Yulang.GeneralDictionaryVersionedPointInstalledSelected233,`Yulang.GeneralDictionaryVersionedRegression233,`Yulang.GeneralDictionaryVersionedSecondEquality233,`Yulang.GeneralDictionaryVersionedSecondRaw233,`Yulang.GeneralDictionaryVersionedSecondRefresh233,`Yulang.GeneralDictionaryVersionedSecondSelected233,`Yulang.GeneralDictionaryVersionedSecondStable233,`Yulang.GeneralNominalVersionedGrowth233]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE233-SECOND-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE233-SECOND-FAIL: no constants checked"
  logInfo m!"CYCLE233-SECOND-PASS: {checked} constants in {modules.size} modules"
