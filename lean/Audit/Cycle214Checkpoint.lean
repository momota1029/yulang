import Yulang.GeneralDictionaryDefault214ActualBodyFrame
import Yulang.GeneralDictionaryDefault214ActualEffects
import Yulang.GeneralDictionaryDefault214ActualJournal
import Yulang.GeneralDictionaryDefault214ActualReadback
import Yulang.GeneralDictionaryDefault214ActualShadowRegression
import Yulang.GeneralDictionaryDefault214ActualSites
import Yulang.GeneralDictionaryDefault214ActualSupport
import Yulang.GeneralDictionaryDefaultCandidateActual214
import Yulang.GeneralDictionaryDefaultChoice214
import Yulang.GeneralDictionaryDefaultFreshActual214
import Yulang.GeneralDictionaryDefaultIdentityCenters214
import Yulang.GeneralDictionaryDefaultOverlap214
import Yulang.GeneralDictionaryDefaultOverlapRegression214
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryDefault214ActualBodyFrame, `Yulang.GeneralDictionaryDefault214ActualEffects, `Yulang.GeneralDictionaryDefault214ActualJournal, `Yulang.GeneralDictionaryDefault214ActualReadback, `Yulang.GeneralDictionaryDefault214ActualShadowRegression, `Yulang.GeneralDictionaryDefault214ActualSites, `Yulang.GeneralDictionaryDefault214ActualSupport, `Yulang.GeneralDictionaryDefaultCandidateActual214, `Yulang.GeneralDictionaryDefaultChoice214, `Yulang.GeneralDictionaryDefaultFreshActual214, `Yulang.GeneralDictionaryDefaultIdentityCenters214, `Yulang.GeneralDictionaryDefaultOverlap214, `Yulang.GeneralDictionaryDefaultOverlapRegression214]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if modules.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE214-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE214-GATE-FAIL: no constants checked"
  logInfo m!"CYCLE214-GATE-PASS: {checked} constants in {modules.size} modules"
