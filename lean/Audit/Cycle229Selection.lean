import Yulang.GeneralDictionaryJournalRefinement229Cycles
import Yulang.GeneralDictionaryJournalRefinement229StageSafety
import Yulang.GeneralDictionaryJournalRefinement229Selected
import Yulang.GeneralDictionaryJournalRefinement229Regression
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryJournalRefinement229Cycles,`Yulang.GeneralDictionaryJournalRefinement229StageSafety,`Yulang.GeneralDictionaryJournalRefinement229Selected,`Yulang.GeneralDictionaryJournalRefinement229Regression]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE229-SELECTION-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE229-SELECTION-FAIL: no constants checked"
  logInfo m!"CYCLE229-SELECTION-PASS: {checked} constants in {modules.size} modules"
