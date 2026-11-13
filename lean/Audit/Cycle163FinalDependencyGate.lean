import Yulang.GeneralDictionaryAliasSettlement
import Yulang.GeneralDictionaryRecordedSettlement
import Yulang.GeneralDictionaryRecursiveConsumerObstruction
import Yulang.GeneralDictionarySettledConsumerResume
import Yulang.GeneralDictionarySettledFiniteCoverage
import Yulang.GeneralDictionarySettledFiniteCoverageExample
import Yulang.GeneralDictionarySettledReservationTimeline
import Yulang.GeneralDictionarySettledTerminalPrefix
import Yulang.GeneralDictionarySettlementExamples
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryAliasSettlement, `Yulang.GeneralDictionaryRecordedSettlement, `Yulang.GeneralDictionaryRecursiveConsumerObstruction, `Yulang.GeneralDictionarySettledConsumerResume, `Yulang.GeneralDictionarySettledFiniteCoverage, `Yulang.GeneralDictionarySettledFiniteCoverageExample, `Yulang.GeneralDictionarySettledReservationTimeline, `Yulang.GeneralDictionarySettledTerminalPrefix, `Yulang.GeneralDictionarySettlementExamples]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if wanted.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} (module {moduleName}) depends on {dependency}"
  if checked = 0 then throwError "AXIOM-GATE-FAIL: no declarations checked"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"
