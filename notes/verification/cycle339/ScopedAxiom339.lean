import Yulang.GeneralDeclarativeMixedCompiler339
import Yulang.GeneralDeclarativeMixedDictionary339
import Yulang.GeneralDeclarativeMixedEndpoint339
import Yulang.GeneralDeclarativeMixedFixtureBase339
import Yulang.GeneralDeclarativeMixedFixtureModel339
import Yulang.GeneralDeclarativeMixedFixtureRoutes339
import Yulang.GeneralDeclarativeMixedFixtureSelection339
import Yulang.GeneralDeclarativeMixedInputs339
import Yulang.GeneralDeclarativeMixedLeaf339
import Yulang.GeneralDeclarativeMixedLeafGrowth339
import Yulang.GeneralDeclarativeMixedSources339
import Yulang.GeneralDeclarativeMixedTree339
import Yulang.GeneralDeclarativeOpenExec339
import Yulang.GeneralDeclarativeOpenFixtureBase339
import Yulang.GeneralDeclarativeOpenFixtureModel339
import Yulang.GeneralDeclarativeOpenFixtureRoutes339
import Yulang.GeneralDeclarativeOpenFixtureSelection339
import Yulang.GeneralDeclarativeOpenFixtureWitness339
import Yulang.GeneralDeclarativeOpenReadiness339
import Yulang.GeneralDeclarativeOpenReceipt339
import Yulang.GeneralDeclarativeOpenSelected339
import Yulang.GeneralDeclarativeOpenTraversal339
import Yulang.GeneralDeclarativeOpenUnresolved339
import Yulang.GeneralDeclarativeStoppedFixture339
import Yulang.GeneralDeclarativeStoppedLower339
import Yulang.GeneralDeclarativeStoppedOrder339
import Yulang.GeneralDeclarativeStoppedOrigins339
import Yulang.GeneralDeclarativeStoppedOutput339
import Yulang.GeneralDeclarativeStoppedStructural339
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
