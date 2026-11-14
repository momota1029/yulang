import Yulang.GeneralNominalCaptureEnrichment188
import Yulang.GeneralNominalHeadInitialCommon188
import Yulang.GeneralNominalHeadInitialEffects188
import Yulang.GeneralNominalHeadInitialFrame188
import Yulang.GeneralNominalHeadMixedExtension188
import Yulang.GeneralNominalHeadNominalExtension188
import Yulang.GeneralNominalHeadPointBounds188
import Yulang.GeneralNominalHeadRecursiveExtension188
import Yulang.GeneralNominalHeadStructuralExtension188
import Yulang.GeneralNominalHeadVariableExtension188
import Yulang.GeneralNominalInspectionTransport188
import Yulang.GeneralNominalMixedOriginEnrichment188
import Yulang.GeneralNominalPointOriginEnrichment188
import Yulang.GeneralNominalPointProjection188
import Yulang.GeneralNominalRecursiveEnrichment188
import Yulang.GeneralNominalReportTransport188
import Yulang.GeneralNominalSemanticEnrichment188
import Yulang.GeneralNominalStructuralEnrichment188
import Yulang.GeneralNominalStructuralOrigin188
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if moduleName.toString.endsWith "188" then
        checked := checked + 1
        for dependency in ← collectAxioms name do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked == 0 then throwError "empty gate"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations including generated/private"
