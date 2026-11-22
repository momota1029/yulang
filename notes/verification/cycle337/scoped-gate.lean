-- Scoped replay of the unmodified gate body.
import Yulang.GeneralDeclarativeDeleteShell337
import Yulang.GeneralDeclarativeExactClash337
import Yulang.GeneralDeclarativeExactCompatibility337
import Yulang.GeneralDeclarativeExactCompose337
import Yulang.GeneralDeclarativeExactDelete337
import Yulang.GeneralDeclarativeExactDeleteAuth337
import Yulang.GeneralDeclarativeExactDeleteFinite337
import Yulang.GeneralDeclarativeExactDeleteRigid337
import Yulang.GeneralDeclarativeExactDictionary337
import Yulang.GeneralDeclarativeExactNested337
import Yulang.GeneralDeclarativeExactOverlay337
import Yulang.GeneralDeclarativeExactRegression337
import Yulang.GeneralDeclarativeExactSupport337
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let system : List Name := [`Init, `Std, `Lean, `Lake]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      unless system.any (·.isPrefixOf moduleName) do
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} (module {moduleName}) depends on {dependency}"
  if checked = 0 then throwError "AXIOM-GATE-FAIL: no declarations checked"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"
