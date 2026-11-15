import Yulang.GeneralDictionaryDefaultEvidenceSplit212
import Yulang.GeneralDictionaryDefaultJournalFrame212
import Yulang.GeneralDictionaryDefaultModelGlue212
import Yulang.GeneralDictionaryDefaultPacketFrame212
import Yulang.GeneralDictionaryDefaultProvenance212
import Yulang.GeneralDictionaryDefaultTotalFrame212
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryDefaultEvidenceSplit212, `Yulang.GeneralDictionaryDefaultJournalFrame212, `Yulang.GeneralDictionaryDefaultModelGlue212, `Yulang.GeneralDictionaryDefaultPacketFrame212, `Yulang.GeneralDictionaryDefaultProvenance212, `Yulang.GeneralDictionaryDefaultTotalFrame212]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if modules.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE212-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE212-GATE-FAIL: no constants checked"
  logInfo m!"CYCLE212-GATE-PASS: {checked} constants in {modules.size} modules"
