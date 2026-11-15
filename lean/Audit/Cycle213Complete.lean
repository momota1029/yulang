import Yulang.GeneralDictionaryDefaultModeEffects213
import Yulang.GeneralDictionaryDefaultModeSupport213
import Yulang.GeneralDictionaryDefaultRawSeparation213
import Yulang.GeneralDictionaryDefaultCollapseBinders213
import Yulang.GeneralDictionaryDefaultCollapseCertificate213
import Yulang.GeneralDictionaryDefaultCollapseFrame213
import Yulang.GeneralDictionaryDefaultCollapseReplay213
import Yulang.GeneralDictionaryDefaultHeadGap213
import Yulang.GeneralDictionaryDefaultJournalSupport213
import Yulang.GeneralDictionaryDefaultPacketSupport213
import Yulang.GeneralDictionaryDefaultPointRegression213
import Yulang.GeneralDictionaryDefaultRawSupport213
import Yulang.GeneralDictionaryDefaultReservationRegression213
import Yulang.GeneralDictionaryDefaultSemanticBinders213
import Yulang.GeneralDictionaryDefaultSemanticTerminal213
import Yulang.GeneralDictionaryDefaultTightGlue213
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryDefaultModeEffects213, `Yulang.GeneralDictionaryDefaultModeSupport213, `Yulang.GeneralDictionaryDefaultRawSeparation213, `Yulang.GeneralDictionaryDefaultCollapseBinders213, `Yulang.GeneralDictionaryDefaultCollapseCertificate213, `Yulang.GeneralDictionaryDefaultCollapseFrame213, `Yulang.GeneralDictionaryDefaultCollapseReplay213, `Yulang.GeneralDictionaryDefaultHeadGap213, `Yulang.GeneralDictionaryDefaultJournalSupport213, `Yulang.GeneralDictionaryDefaultPacketSupport213, `Yulang.GeneralDictionaryDefaultPointRegression213, `Yulang.GeneralDictionaryDefaultRawSupport213, `Yulang.GeneralDictionaryDefaultReservationRegression213, `Yulang.GeneralDictionaryDefaultSemanticBinders213, `Yulang.GeneralDictionaryDefaultSemanticTerminal213, `Yulang.GeneralDictionaryDefaultTightGlue213]
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
