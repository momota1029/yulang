import Yulang.GeneralDictionaryVersionedAcyclic232
import Yulang.GeneralDictionaryVersionedEvidenceAt232
import Yulang.GeneralDictionaryVersionedGuarded232
import Yulang.GeneralDictionaryVersionedGuardedRegression232
import Yulang.GeneralDictionaryVersionedInstallClosed232
import Yulang.GeneralDictionaryVersionedRawAcyclic232
import Yulang.GeneralDictionaryVersionedReachable232
import Yulang.GeneralDictionaryVersionedSelected232
import Yulang.GeneralDictionaryVersionedSelectionFacts232
import Yulang.GeneralDictionaryVersionedSourceRegression232
import Yulang.GeneralNominalVersionedAcyclic232
import Yulang.GeneralNominalVersionedAdministrative232
import Yulang.GeneralNominalVersionedBoundary232
import Yulang.GeneralNominalVersionedCycles232
import Yulang.GeneralNominalVersionedDiagnostic232
import Yulang.GeneralNominalVersionedDiagnosticLaws232
import Yulang.GeneralNominalVersionedFrameFunctional232
import Yulang.GeneralNominalVersionedFrontiers232
import Yulang.GeneralNominalVersionedHeadSharing232
import Yulang.GeneralNominalVersionedKernel232
import Yulang.GeneralNominalVersionedMergedConflict232
import Yulang.GeneralNominalVersionedMigration232
import Yulang.GeneralNominalVersionedRecorded232
import Yulang.GeneralNominalVersionedRefresh232
import Yulang.GeneralNominalVersionedSourceBoundary232
import Yulang.GeneralNominalVersionedSourceFrontiers232
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryVersionedAcyclic232,`Yulang.GeneralDictionaryVersionedEvidenceAt232,`Yulang.GeneralDictionaryVersionedGuarded232,`Yulang.GeneralDictionaryVersionedGuardedRegression232,`Yulang.GeneralDictionaryVersionedInstallClosed232,`Yulang.GeneralDictionaryVersionedRawAcyclic232,`Yulang.GeneralDictionaryVersionedReachable232,`Yulang.GeneralDictionaryVersionedSelected232,`Yulang.GeneralDictionaryVersionedSelectionFacts232,`Yulang.GeneralDictionaryVersionedSourceRegression232,`Yulang.GeneralNominalVersionedAcyclic232,`Yulang.GeneralNominalVersionedAdministrative232,`Yulang.GeneralNominalVersionedBoundary232,`Yulang.GeneralNominalVersionedCycles232,`Yulang.GeneralNominalVersionedDiagnostic232,`Yulang.GeneralNominalVersionedDiagnosticLaws232,`Yulang.GeneralNominalVersionedFrameFunctional232,`Yulang.GeneralNominalVersionedFrontiers232,`Yulang.GeneralNominalVersionedHeadSharing232,`Yulang.GeneralNominalVersionedKernel232,`Yulang.GeneralNominalVersionedMergedConflict232,`Yulang.GeneralNominalVersionedMigration232,`Yulang.GeneralNominalVersionedRecorded232,`Yulang.GeneralNominalVersionedRefresh232,`Yulang.GeneralNominalVersionedSourceBoundary232,`Yulang.GeneralNominalVersionedSourceFrontiers232]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE232-SECOND-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE232-SECOND-FAIL: no constants checked"
  logInfo m!"CYCLE232-SECOND-PASS: {checked} constants in {modules.size} modules"
