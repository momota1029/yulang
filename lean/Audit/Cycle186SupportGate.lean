import Yulang.GeneralNominalChildSemantic186
import Yulang.GeneralNominalHeadCandidateExtension186
import Yulang.GeneralNominalHeadCandidateOverlap186
import Yulang.GeneralNominalHeadCandidateSemantic186
import Yulang.GeneralNominalHeadCandidateSupport186
import Yulang.GeneralNominalHeadConservativeExtension186
import Yulang.GeneralNominalHeadIdentityCenters186
import Yulang.GeneralNominalHeadIdentityInduction186
import Yulang.GeneralNominalHeadSchemaNames186
import Yulang.GeneralNominalHeadSchemaSemantic186
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if moduleName.toString.endsWith "186" then
        checked := checked + 1
        for dependency in ← collectAxioms name do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked == 0 then throwError "empty gate"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations (definitions/private/generated included)"
