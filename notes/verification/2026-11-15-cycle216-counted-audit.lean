import Yulang.GeneralDictionaryCountedRoot216
import Yulang.GeneralDictionaryRecordBracket216
import Yulang.GeneralDictionaryCountedBracket216
import Yulang.GeneralDictionaryCountedObservation216
import Yulang.GeneralDictionaryCountedInspection216
import Yulang.GeneralDictionaryCountedCandidate216
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryCountedRoot216,`Yulang.GeneralDictionaryRecordBracket216,`Yulang.GeneralDictionaryCountedBracket216,`Yulang.GeneralDictionaryCountedObservation216,`Yulang.GeneralDictionaryCountedInspection216,`Yulang.GeneralDictionaryCountedCandidate216]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if modules.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "COUNTED216-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "COUNTED216-FAIL: no constants checked"
  logInfo m!"COUNTED216-PASS: {checked} constants in {modules.size} modules"
