import Yulang.GeneralDictionaryVersionedConflict199233
import Yulang.GeneralDictionaryVersionedConflict199Local233
import Yulang.GeneralDictionaryVersionedDefault202233
import Yulang.GeneralDictionaryVersionedDefault202Local233
import Yulang.GeneralNominalVersionedMixedCache233
import Yulang.GeneralNominalVersionedNameSeparation233
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryVersionedConflict199233,`Yulang.GeneralDictionaryVersionedConflict199Local233,`Yulang.GeneralDictionaryVersionedDefault202233,`Yulang.GeneralDictionaryVersionedDefault202Local233,`Yulang.GeneralNominalVersionedMixedCache233,`Yulang.GeneralNominalVersionedNameSeparation233]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE233-FOURTH-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE233-FOURTH-FAIL: no constants checked"
  logInfo m!"CYCLE233-FOURTH-PASS: {checked} constants in {modules.size} modules"
