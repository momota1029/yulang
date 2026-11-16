import Yulang.GeneralDictionaryHistoricalBody227
import Yulang.GeneralDictionaryOriginClass227
import Yulang.GeneralDictionaryBodyProvenance227
import Yulang.GeneralDictionaryOriginJournal227
import Yulang.GeneralDictionarySemanticTrace227
import Yulang.GeneralDictionaryFootprintCenters227
import Yulang.GeneralDictionaryRequestSeparation227
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryHistoricalBody227,`Yulang.GeneralDictionaryOriginClass227,`Yulang.GeneralDictionaryBodyProvenance227,`Yulang.GeneralDictionaryOriginJournal227,`Yulang.GeneralDictionarySemanticTrace227,`Yulang.GeneralDictionaryFootprintCenters227,`Yulang.GeneralDictionaryRequestSeparation227]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE227-ORIGINS-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE227-ORIGINS-FAIL: no constants checked"
  logInfo m!"CYCLE227-ORIGINS-PASS: {checked} constants in {modules.size} modules"
