import Yulang.GeneralDictionaryRecorded168Relocation
import Yulang.GeneralDictionaryCapturedJournal168
import Lean

/-! Read-only audit of journal relocation and its actual captured certificate. -/
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryRecorded168Relocation, `Yulang.GeneralDictionaryCapturedJournal168]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if wanted.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "AXIOM-GATE-FAIL: no declarations checked"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"

#check @Yulang.GeneralDictionaryRecorded168Relocation.current_instance
#check @Yulang.GeneralDictionaryRecorded168Relocation.recorded_tree
#check @Yulang.GeneralDictionaryRecorded168Relocation.current_evidence
#check @Yulang.GeneralDictionaryRecorded168Relocation.of_recorded_tree
#check @Yulang.GeneralDictionaryRecorded168Relocation.recorded_current_evidence
#check @Yulang.GeneralDictionaryRecorded168Relocation.discharged
#check @Yulang.GeneralDictionaryCapturedJournal168.relocation
#check @Yulang.GeneralDictionaryCapturedJournal168.journal_tree
#check @Yulang.GeneralDictionaryCapturedJournal168.current_dictionary
#check @Yulang.GeneralDictionaryCapturedJournal168.nonvacuous_journal_replay
