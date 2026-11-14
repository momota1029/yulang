import Yulang.GeneralNominalOriginAgreement183
import Yulang.GeneralNominalCaptureCoverage183
import Yulang.GeneralNominalQueryProvenance183
import Yulang.GeneralNominalCompleteNames183
import Yulang.GeneralNominalRegisteredCoverage183
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if moduleName.toString.endsWith "183" then
        checked := checked + 1
        for dependency in ← collectAxioms name do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked == 0 then throwError "empty gate"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations (definitions/private/generated included)"
