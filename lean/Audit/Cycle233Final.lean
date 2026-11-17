import Yulang.GeneralDictionaryVersionedGap206233
import Yulang.GeneralDictionaryVersionedGap206Install233
import Yulang.GeneralDictionaryVersionedGap206Safety233
import Yulang.GeneralDictionaryVersionedJoin204233
import Yulang.GeneralDictionaryVersionedJoin204Local233
import Yulang.GeneralDictionaryVersionedUpperBase233
import Yulang.GeneralDictionaryVersionedUpperRefresh233
import Yulang.GeneralDictionaryVersionedUpperSnapshot233
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryVersionedGap206233,`Yulang.GeneralDictionaryVersionedGap206Install233,`Yulang.GeneralDictionaryVersionedGap206Safety233,`Yulang.GeneralDictionaryVersionedJoin204233,`Yulang.GeneralDictionaryVersionedJoin204Local233,`Yulang.GeneralDictionaryVersionedUpperBase233,`Yulang.GeneralDictionaryVersionedUpperRefresh233,`Yulang.GeneralDictionaryVersionedUpperSnapshot233]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE233-FINAL-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE233-FINAL-FAIL: no constants checked"
  logInfo m!"CYCLE233-FINAL-PASS: {checked} constants in {modules.size} modules"
