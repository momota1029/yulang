import Yulang.GeneralNominalAggregateVersion231
import Yulang.GeneralNominalVersionedAllocation231
import Yulang.GeneralNominalVersionedCapture231
import Yulang.GeneralDictionaryVersionedSupport231
import Yulang.GeneralDictionaryVersionedNames231
import Yulang.GeneralDictionaryVersionedMerge231
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalAggregateVersion231,`Yulang.GeneralNominalVersionedAllocation231,`Yulang.GeneralNominalVersionedCapture231,`Yulang.GeneralDictionaryVersionedSupport231,`Yulang.GeneralDictionaryVersionedNames231,`Yulang.GeneralDictionaryVersionedMerge231]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE231-ALLOCATION-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE231-ALLOCATION-FAIL: no constants checked"
  logInfo m!"CYCLE231-ALLOCATION-PASS: {checked} constants in {modules.size} modules"
