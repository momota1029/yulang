import Yulang.GeneralDictionaryJournalRefinement229Snapshot
import Yulang.GeneralDictionaryJournalRefinement229Refresh
import Yulang.GeneralDictionaryJournalRefinement229Raw
import Yulang.GeneralDictionaryJournalRefinement229Diagnostic
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryJournalRefinement229Snapshot,`Yulang.GeneralDictionaryJournalRefinement229Refresh,`Yulang.GeneralDictionaryJournalRefinement229Raw,`Yulang.GeneralDictionaryJournalRefinement229Diagnostic]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE229-CLOSURE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE229-CLOSURE-FAIL: no constants checked"
  logInfo m!"CYCLE229-CLOSURE-PASS: {checked} constants in {modules.size} modules"
