-- Scoped replay of the supervisor's original body.
import Yulang.GeneralDeclarativeCompoundBatch338
import Yulang.GeneralDeclarativeCompoundCompiler338
import Yulang.GeneralDeclarativeCompoundDictionary338
import Yulang.GeneralDeclarativeCompoundEndpoints338
import Yulang.GeneralDeclarativeCompoundFixture338
import Yulang.GeneralDeclarativeCompoundFixtureModel338
import Yulang.GeneralDeclarativeCompoundFixtureRoutes338
import Yulang.GeneralDeclarativeCompoundFixtureSelection338
import Yulang.GeneralDeclarativeCompoundHeads338
import Yulang.GeneralDeclarativeCompoundInputs338
import Yulang.GeneralDeclarativeCompoundOpenFixture338
import Yulang.GeneralDeclarativeCompoundOpenPrefix338
import Yulang.GeneralDeclarativeCompoundOpenReceipt338
import Yulang.GeneralDeclarativeCompoundPattern338
import Yulang.GeneralDeclarativeCompoundReadback338
import Yulang.GeneralDeclarativeCompoundRoutes338
import Yulang.GeneralDeclarativeCompoundSources338
import Yulang.GeneralDeclarativeCompoundTree338
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
