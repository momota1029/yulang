import Yulang.GeneralNominalCandidateCoverage184
import Yulang.GeneralNominalCenterCoherence184
import Yulang.GeneralNominalChildCoherence184
import Yulang.GeneralNominalGeneratedSupport184
import Yulang.GeneralNominalGroundCandidateReadback184
import Yulang.GeneralNominalGroundHistoricalExtension184
import Yulang.GeneralNominalGroundLedgerExtension184
import Yulang.GeneralNominalGroundSiteCoherence184
import Yulang.GeneralNominalGroundSiteSupport184
import Yulang.GeneralNominalHeadTransport184
import Yulang.GeneralNominalOverlapIdentity184
import Yulang.GeneralNominalOverlapProvenance184
import Yulang.GeneralNominalRawSeparation184
import Yulang.GeneralNominalRootExtension184
import Yulang.GeneralNominalRootOverlap184
import Yulang.GeneralNominalSiteSeparation184
import Yulang.GeneralNominalSiteSupport184
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if moduleName.toString.endsWith "184" then
        checked := checked + 1
        for dependency in ← collectAxioms name do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked == 0 then throwError "empty gate"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations (definitions/private/generated included)"
