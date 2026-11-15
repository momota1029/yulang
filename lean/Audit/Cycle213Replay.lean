import Yulang.GeneralDictionaryDefaultCollapseBinders213
import Yulang.GeneralDictionaryDefaultCollapseCertificate213
import Yulang.GeneralDictionaryDefaultCollapseFrame213
import Yulang.GeneralDictionaryDefaultCollapseReplay213
import Yulang.GeneralDictionaryDefaultSemanticBinders213
import Yulang.GeneralDictionaryDefaultSemanticTerminal213
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryDefaultCollapseBinders213, `Yulang.GeneralDictionaryDefaultCollapseCertificate213, `Yulang.GeneralDictionaryDefaultCollapseFrame213, `Yulang.GeneralDictionaryDefaultCollapseReplay213, `Yulang.GeneralDictionaryDefaultSemanticBinders213, `Yulang.GeneralDictionaryDefaultSemanticTerminal213]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if modules.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE213-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE213-GATE-FAIL: no constants checked"
  logInfo m!"CYCLE213-GATE-PASS: {checked} constants in {modules.size} modules"
