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
  let env ← getEnv
  let forbidden := ["Yulang.GeneralNominalVersioned","Yulang.GeneralStopped", "Yulang.GeneralDeclarativeStopped", "Yulang.GeneralNominalRebaseRaw", "Yulang.Runtime"]
  let mut pending : List Name := []
  for (n, _) in env.constants.toList do
    let k := toString n
    if (k.startsWith "Yulang.GeneralDeclarativeTagged") && (k.splitOn "340.").length > 1 then
      pending := n :: pending
  let roots := pending.length
  let mut visited : NameSet := {}
  repeat
    match pending with
    | [] => break
    | n::other =>
      pending := other
      if visited.contains n then continue
      visited := visited.insert n
      if forbidden.any (fun p => (toString n).startsWith p) then
        throwError "DECLARATIVE-BOUNDARY-FAIL: {n}"
      if let some decl := env.find? n then
        pending := decl.type.getUsedConstants.toList ++ pending
        if let some v := decl.value? then
          pending := v.getUsedConstants.toList ++ pending
  if roots = 0 then throwError "DECLARATIVE-BOUNDARY-FAIL: no roots found"
  logInfo m!"DECLARATIVE-BOUNDARY-PASS: {roots} roots, {visited.toList.length} reachable declarations"
