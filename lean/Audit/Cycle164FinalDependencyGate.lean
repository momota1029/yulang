import Yulang.GeneralDictionaryExactRefreshChain
import Yulang.GeneralDictionarySettledTerminalEvidence
import Yulang.GeneralDictionarySharedCurrentEvidence
import Yulang.GeneralDictionarySharedDisplayInstallation
import Yulang.GeneralDictionarySharedEvidenceTrace
import Yulang.GeneralDictionarySharedInstallEvidence
import Yulang.GeneralDictionarySharedLenCommitted
import Yulang.GeneralDictionarySharedRecordedEvidence
import Yulang.GeneralDictionarySharedRecordedTree
import Yulang.GeneralDictionarySharedRecursiveExample
import Yulang.GeneralDictionarySharedSemanticSettlement
import Yulang.GeneralDictionarySharedSiblingPrefix
import Yulang.GeneralDictionarySharedTerminalInstallation
import Yulang.GeneralDictionarySharedTerminalObstruction
import Yulang.GeneralDictionaryTerminalRefreshObstruction
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryExactRefreshChain, `Yulang.GeneralDictionarySettledTerminalEvidence, `Yulang.GeneralDictionarySharedCurrentEvidence, `Yulang.GeneralDictionarySharedDisplayInstallation, `Yulang.GeneralDictionarySharedEvidenceTrace, `Yulang.GeneralDictionarySharedInstallEvidence, `Yulang.GeneralDictionarySharedLenCommitted, `Yulang.GeneralDictionarySharedRecordedEvidence, `Yulang.GeneralDictionarySharedRecordedTree, `Yulang.GeneralDictionarySharedRecursiveExample, `Yulang.GeneralDictionarySharedSemanticSettlement, `Yulang.GeneralDictionarySharedSiblingPrefix, `Yulang.GeneralDictionarySharedTerminalInstallation, `Yulang.GeneralDictionarySharedTerminalObstruction, `Yulang.GeneralDictionaryTerminalRefreshObstruction]
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
