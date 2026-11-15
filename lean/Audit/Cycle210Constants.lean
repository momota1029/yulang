import Yulang.GeneralDictionaryDefaultActualHead210
import Yulang.GeneralDictionaryDefaultBinderShape210
import Yulang.GeneralDictionaryDefaultCollapseExpression210
import Yulang.GeneralDictionaryDefaultCollapseRegression210
import Yulang.GeneralDictionaryDefaultExistentialReplay210
import Yulang.GeneralDictionaryDefaultMergeRevisionGuard210
import Yulang.GeneralDictionaryDefaultMergeRevisionProbe210
import Yulang.GeneralDictionaryDefaultNonpointCertificate210
import Yulang.GeneralDictionaryDefaultNonpointCollapse210
import Yulang.GeneralDictionaryDefaultNonpointTerminal210
import Yulang.GeneralDictionaryDefaultReplayRegression210
import Yulang.GeneralDictionaryDefaultRetainedCenter210
import Yulang.GeneralDictionaryDefaultRevisionEquivalence210
import Yulang.GeneralDictionaryDefaultRevisionEvidence210
import Yulang.GeneralDictionaryDefaultRevisionFrames210
import Yulang.GeneralDictionaryDefaultRevisionTrace210
import Yulang.GeneralDictionaryDefaultScopedRevision210
import Yulang.GeneralDictionaryDefaultStructuralReobserve210
import Yulang.GeneralDictionaryDefaultTerminalOutputs210
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryDefaultActualHead210, `Yulang.GeneralDictionaryDefaultBinderShape210, `Yulang.GeneralDictionaryDefaultCollapseExpression210, `Yulang.GeneralDictionaryDefaultCollapseRegression210, `Yulang.GeneralDictionaryDefaultExistentialReplay210, `Yulang.GeneralDictionaryDefaultMergeRevisionGuard210, `Yulang.GeneralDictionaryDefaultMergeRevisionProbe210, `Yulang.GeneralDictionaryDefaultNonpointCertificate210, `Yulang.GeneralDictionaryDefaultNonpointCollapse210, `Yulang.GeneralDictionaryDefaultNonpointTerminal210, `Yulang.GeneralDictionaryDefaultReplayRegression210, `Yulang.GeneralDictionaryDefaultRetainedCenter210, `Yulang.GeneralDictionaryDefaultRevisionEquivalence210, `Yulang.GeneralDictionaryDefaultRevisionEvidence210, `Yulang.GeneralDictionaryDefaultRevisionFrames210, `Yulang.GeneralDictionaryDefaultRevisionTrace210, `Yulang.GeneralDictionaryDefaultScopedRevision210, `Yulang.GeneralDictionaryDefaultStructuralReobserve210, `Yulang.GeneralDictionaryDefaultTerminalOutputs210]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if modules.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE210-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE210-GATE-FAIL: no constants checked"
  logInfo m!"CYCLE210-GATE-PASS: {checked} constants in {modules.size} modules"
