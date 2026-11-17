import Yulang.GeneralNominalInspectionSupport237
import Yulang.GeneralNominalReportSupport237
import Yulang.GeneralNominalVersionedChildLabels237
import Yulang.GeneralNominalVersionedCurrentHead237
import Yulang.GeneralNominalVersionedCurrentProjection237
import Yulang.GeneralNominalVersionedHeadMass237
import Yulang.GeneralNominalVersionedHeadReadback237
import Yulang.GeneralNominalVersionedMixedAncestry237
import Yulang.GeneralNominalVersionedMixedReplay237
import Yulang.GeneralNominalVersionedModelSupport237
import Yulang.GeneralNominalVersionedModelSupportSteps237
import Yulang.GeneralNominalVersionedProjectionBounds237
import Yulang.GeneralNominalVersionedResidualFrame237
import Yulang.GeneralNominalVersionedResidualSupportSteps237
import Yulang.GeneralNominalVersionedSelectiveChild237
import Yulang.GeneralNominalVersionedSelectiveHead237
import Yulang.GeneralNominalVersionedSupportedCompletion237
import Yulang.GeneralNominalVersionedTraceSupport237
import Yulang.GeneralNominalVersionedWeightedHead237
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalInspectionSupport237, `Yulang.GeneralNominalReportSupport237, `Yulang.GeneralNominalVersionedChildLabels237, `Yulang.GeneralNominalVersionedCurrentHead237, `Yulang.GeneralNominalVersionedCurrentProjection237, `Yulang.GeneralNominalVersionedHeadMass237, `Yulang.GeneralNominalVersionedHeadReadback237, `Yulang.GeneralNominalVersionedMixedAncestry237, `Yulang.GeneralNominalVersionedMixedReplay237, `Yulang.GeneralNominalVersionedModelSupport237, `Yulang.GeneralNominalVersionedModelSupportSteps237, `Yulang.GeneralNominalVersionedProjectionBounds237, `Yulang.GeneralNominalVersionedResidualFrame237, `Yulang.GeneralNominalVersionedResidualSupportSteps237, `Yulang.GeneralNominalVersionedSelectiveChild237, `Yulang.GeneralNominalVersionedSelectiveHead237, `Yulang.GeneralNominalVersionedSupportedCompletion237, `Yulang.GeneralNominalVersionedTraceSupport237, `Yulang.GeneralNominalVersionedWeightedHead237]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE237-FIRST-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE237-FIRST-FAIL: no constants checked"
  logInfo m!"CYCLE237-FIRST-PASS: {checked} constants in {modules.size} modules"
