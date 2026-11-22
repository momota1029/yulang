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
      if mod.startsWith "Yulang.GeneralDeclarativeCompound" && mod.endsWith "338" then some n else none
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
  logInfo m!"DECLARATIVE-DEPENDENCY-PASS: {roots.length} C338 constants, {visited.size} transitive type/value dependencies"
