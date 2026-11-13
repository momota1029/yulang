import Yulang.GeneralDictionarySettledCutExclusion
import Yulang.GeneralDictionarySettledEvidence
import Yulang.GeneralDictionarySettledGuardClosure
import Yulang.GeneralDictionarySettledGuardedClassification
import Yulang.GeneralDictionarySettledNamedExample
import Yulang.GeneralDictionarySettledPendingExclusion
import Yulang.GeneralDictionarySettledProjection
import Yulang.GeneralDictionarySettledRecursiveExample
import Yulang.GeneralDictionarySettledReservedExample
import Yulang.GeneralDictionarySettledSourceGuard
import Yulang.GeneralDictionarySettledTreeEvidence
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionarySettledCutExclusion, `Yulang.GeneralDictionarySettledEvidence, `Yulang.GeneralDictionarySettledGuardClosure, `Yulang.GeneralDictionarySettledGuardedClassification, `Yulang.GeneralDictionarySettledNamedExample, `Yulang.GeneralDictionarySettledPendingExclusion, `Yulang.GeneralDictionarySettledProjection, `Yulang.GeneralDictionarySettledRecursiveExample, `Yulang.GeneralDictionarySettledReservedExample, `Yulang.GeneralDictionarySettledSourceGuard, `Yulang.GeneralDictionarySettledTreeEvidence]
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
