import Yulang.GeneralDictionaryJournalRefinement228Trusted
import Yulang.GeneralDictionaryJournalRefinement228Cycles
import Yulang.GeneralDictionaryJournalRefinement228Enable
import Yulang.GeneralDictionaryJournalRefinement228Reachable
import Yulang.GeneralDictionaryJournalRefinement228RawStage
import Yulang.GeneralDictionaryJournalAggregateGuard228
import Yulang.GeneralDictionaryJournalRefinement228Source
import Yulang.GeneralDictionaryJournalRefinement228Initial
import Yulang.GeneralDictionaryJournalRefinement228Install
import Yulang.GeneralDictionaryJournalRefinement228Reobserve
import Yulang.GeneralDictionaryJournalRefinement228Current
import Yulang.GeneralDictionaryJournalRefinement228Raw
import Yulang.GeneralDictionaryJournalRefinement228Stage
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryJournalRefinement228Trusted,`Yulang.GeneralDictionaryJournalRefinement228Cycles,`Yulang.GeneralDictionaryJournalRefinement228Enable,`Yulang.GeneralDictionaryJournalRefinement228Reachable,`Yulang.GeneralDictionaryJournalRefinement228RawStage,`Yulang.GeneralDictionaryJournalAggregateGuard228,`Yulang.GeneralDictionaryJournalRefinement228Source,`Yulang.GeneralDictionaryJournalRefinement228Initial,`Yulang.GeneralDictionaryJournalRefinement228Install,`Yulang.GeneralDictionaryJournalRefinement228Reobserve,`Yulang.GeneralDictionaryJournalRefinement228Current,`Yulang.GeneralDictionaryJournalRefinement228Raw,`Yulang.GeneralDictionaryJournalRefinement228Stage]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE228-PROBE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE228-PROBE-FAIL: no constants checked"
  logInfo m!"CYCLE228-PROBE-PASS: {checked} constants in {modules.size} modules"
