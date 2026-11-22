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
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden := ["Yulang.GeneralNominalVersioned","Yulang.GeneralStopped", "Yulang.GeneralDeclarativeStopped", "Yulang.GeneralNominalRebaseRaw", "Yulang.Runtime"]
  let mut pending : List Name := []
  for (n, _) in env.constants.toList do
    let k := toString n
    if (k.startsWith "Yulang.GeneralDeclarativeOpen" || k.startsWith "Yulang.GeneralDeclarativeMixed") && (k.splitOn "339.").length > 1 then
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
