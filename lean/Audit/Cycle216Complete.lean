import Yulang.GeneralDictionaryCountedBracket216
import Yulang.GeneralDictionaryCountedCandidate216
import Yulang.GeneralDictionaryCountedInspection216
import Yulang.GeneralDictionaryCountedObservation216
import Yulang.GeneralDictionaryCountedProjection216
import Yulang.GeneralDictionaryCountedRawHead216
import Yulang.GeneralDictionaryCountedRoot216
import Yulang.GeneralDictionaryCurrentCompletion216
import Yulang.GeneralDictionaryInitialMerge216
import Yulang.GeneralDictionaryJournalMerge216
import Yulang.GeneralDictionaryLiveSupport216
import Yulang.GeneralDictionaryMergeCompletion216
import Yulang.GeneralDictionaryMergeCriterion216
import Yulang.GeneralDictionaryMergeSlots216
import Yulang.GeneralDictionaryMixedMerge216
import Yulang.GeneralDictionaryOwnedMerges216
import Yulang.GeneralDictionaryPointExtrema216
import Yulang.GeneralDictionaryRecordBracket216
import Yulang.GeneralDictionarySharingBoundary216
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryCountedBracket216, `Yulang.GeneralDictionaryCountedCandidate216, `Yulang.GeneralDictionaryCountedInspection216, `Yulang.GeneralDictionaryCountedObservation216, `Yulang.GeneralDictionaryCountedProjection216, `Yulang.GeneralDictionaryCountedRawHead216, `Yulang.GeneralDictionaryCountedRoot216, `Yulang.GeneralDictionaryCurrentCompletion216, `Yulang.GeneralDictionaryInitialMerge216, `Yulang.GeneralDictionaryJournalMerge216, `Yulang.GeneralDictionaryLiveSupport216, `Yulang.GeneralDictionaryMergeCompletion216, `Yulang.GeneralDictionaryMergeCriterion216, `Yulang.GeneralDictionaryMergeSlots216, `Yulang.GeneralDictionaryMixedMerge216, `Yulang.GeneralDictionaryOwnedMerges216, `Yulang.GeneralDictionaryPointExtrema216, `Yulang.GeneralDictionaryRecordBracket216, `Yulang.GeneralDictionarySharingBoundary216]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if modules.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE216-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE216-GATE-FAIL: no constants checked"
  logInfo m!"CYCLE216-GATE-PASS: {checked} constants in {modules.size} modules"
