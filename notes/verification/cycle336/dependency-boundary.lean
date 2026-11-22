import Yulang.GeneralDeclarativeEndpointBatch336
import Yulang.GeneralDeclarativeEndpointBody336
import Yulang.GeneralDeclarativeEndpointCase336
import Yulang.GeneralDeclarativeEndpointChildModels336
import Yulang.GeneralDeclarativeEndpointChildren336
import Yulang.GeneralDeclarativeEndpointClash336
import Yulang.GeneralDeclarativeEndpointClashChecked336
import Yulang.GeneralDeclarativeEndpointCompatibility336
import Yulang.GeneralDeclarativeEndpointConserve336
import Yulang.GeneralDeclarativeEndpointDictionary336
import Yulang.GeneralDeclarativeEndpointInput336
import Yulang.GeneralDeclarativeEndpointLink336
import Yulang.GeneralDeclarativeEndpointMixedTail336
import Yulang.GeneralDeclarativeEndpointNames336
import Yulang.GeneralDeclarativeEndpointOverlay336
import Yulang.GeneralDeclarativeEndpointProgram336
import Yulang.GeneralDeclarativeEndpointRecord336
import Yulang.GeneralDeclarativeEndpointRegression336
import Yulang.GeneralDeclarativeEndpointResidual336
import Yulang.GeneralDeclarativeEndpointResidualFixture336
import Yulang.GeneralDeclarativeEndpointResidualLift336
import Yulang.GeneralDeclarativeEndpointResidualReflect336
import Yulang.GeneralDeclarativeEndpointResidualSemantics336
import Yulang.GeneralDeclarativeEndpointSelected336
import Yulang.GeneralDeclarativeEndpointSupport336
import Lean.Util.FoldConsts
set_option maxHeartbeats 0
set_option maxRecDepth 24000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forb : List String :=
    ["Yulang.GeneralNominalState.", "Yulang.GeneralNominalSaturationState.",
     "Yulang.GeneralNominalSaturationSteps.", "Yulang.GeneralNominalCenteredSteps.",
     "Yulang.GeneralNominalVersionedJournal", "Yulang.GeneralNominalVersionedMixed",
     "Yulang.GeneralNominalVersionedInstall", "Yulang.GeneralNominalReobservationSteps.",
     "Yulang.GeneralWherePhysical", "Yulang.GeneralWhereVersionInstall",
     "Yulang.GeneralSourceState.State", "Yulang.CommonRoleOutermostResolver.resolve"]
  let roots := env.constants.toList.filterMap fun (n, _) =>
    if let some i := env.getModuleIdxFor? n then
      let mod := env.header.moduleNames[i.toNat]!.toString
      if mod.startsWith "Yulang.GeneralDeclarativeEndpoint" && mod.endsWith "336" then some n else none
    else none
  let mut pending := roots.toArray
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless visited.contains name do
      visited := visited.insert name
      if forb.any (fun pref => name.toString.startsWith pref) then
        throwError "DECLARATIVE-DEPENDENCY-FAIL: {name}"
      if let some info := env.find? name then
        pending := pending ++ info.getUsedConstantsAsSet.toList.toArray
  if roots.isEmpty then throwError "No roots"
  logInfo m!"DECLARATIVE-DEPENDENCY-PASS: {roots.length} C336 constants, {visited.size} transitive type/value dependencies"
