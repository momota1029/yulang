import Yulang.GeneralDictionaryVersionedEvidence232
import Yulang.GeneralDictionaryVersionedInstalled232
import Yulang.GeneralDictionaryVersionedNovel232
import Yulang.GeneralDictionaryVersionedStep232
import Yulang.GeneralNominalVersionedChildren232
import Yulang.GeneralNominalVersionedCommitted232
import Yulang.GeneralNominalVersionedFrameTransport232
import Yulang.GeneralNominalVersionedInstall232
import Yulang.GeneralNominalVersionedInstallProperties232
import Yulang.GeneralNominalVersionedInstallStep232
import Yulang.GeneralNominalVersionedJournal232
import Yulang.GeneralNominalVersionedReplayEffects232
import Yulang.GeneralNominalVersionedTerminal232
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryVersionedEvidence232,`Yulang.GeneralDictionaryVersionedInstalled232,`Yulang.GeneralDictionaryVersionedNovel232,`Yulang.GeneralDictionaryVersionedStep232,`Yulang.GeneralNominalVersionedChildren232,`Yulang.GeneralNominalVersionedCommitted232,`Yulang.GeneralNominalVersionedFrameTransport232,`Yulang.GeneralNominalVersionedInstall232,`Yulang.GeneralNominalVersionedInstallProperties232,`Yulang.GeneralNominalVersionedInstallStep232,`Yulang.GeneralNominalVersionedJournal232,`Yulang.GeneralNominalVersionedReplayEffects232,`Yulang.GeneralNominalVersionedTerminal232]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE232-FIRST-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE232-FIRST-FAIL: no constants checked"
  logInfo m!"CYCLE232-FIRST-PASS: {checked} constants in {modules.size} modules"
