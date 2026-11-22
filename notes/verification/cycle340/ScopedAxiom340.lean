import Yulang.GeneralDeclarativeStoppedCurrent340
import Yulang.GeneralDeclarativeStoppedFold340
import Yulang.GeneralDeclarativeStoppedIntervals340
import Yulang.GeneralDeclarativeStoppedLeaf340
import Yulang.GeneralDeclarativeStoppedLeafFixture340
import Yulang.GeneralDeclarativeStoppedNominalNoPoint340
import Yulang.GeneralDeclarativeStoppedProjection340
import Yulang.GeneralDeclarativeStoppedRetarget340
import Yulang.GeneralDeclarativeStoppedSelected340
import Yulang.GeneralDeclarativeTaggedDictionary340
import Yulang.GeneralDeclarativeTaggedElection340
import Yulang.GeneralDeclarativeTaggedField340
import Yulang.GeneralDeclarativeTaggedFixture340
import Yulang.GeneralDeclarativeTaggedFixtureModel340
import Yulang.GeneralDeclarativeTaggedFixtureSelection340
import Yulang.GeneralDeclarativeTaggedInputs340
import Yulang.GeneralDeclarativeTaggedLegacyCut340
import Yulang.GeneralDeclarativeTaggedNamed340
import Yulang.GeneralDeclarativeTaggedNamedPatch340
import Yulang.GeneralDeclarativeTaggedNamedRoute340
import Yulang.GeneralDeclarativeTaggedParent340
import Yulang.GeneralDeclarativeTaggedPatch340
import Yulang.GeneralDeclarativeTaggedSelected340
import Yulang.GeneralDeclarativeTaggedSources340
import Yulang.GeneralDeclarativeTaggedWhole340
import Yulang.GeneralDeclarativeTaggedWithheld340
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
