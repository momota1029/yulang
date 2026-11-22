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
      if mod.startsWith "Yulang.GeneralDeclarative" && mod.endsWith "337" then some n else none
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
  logInfo m!"DECLARATIVE-DEPENDENCY-PASS: {roots.length} C337 constants, {visited.size} transitive type/value dependencies"
