import Yulang.GeneralDictionaryMixedUpperEvidence234
import Yulang.GeneralDictionaryMixedUpperFrame234
import Yulang.GeneralDictionaryMixedUpperPlan234
import Yulang.GeneralDictionaryMixedUpperSemantics234
import Yulang.GeneralDictionaryMixedUpperStep234
import Yulang.GeneralDictionaryMixedUpperTransport234
import Yulang.GeneralNominalVersionedMixedBoundary234
import Yulang.GeneralNominalVersionedMixedEmbedding234
import Yulang.GeneralNominalVersionedMixedEvidenceTransport234
import Yulang.GeneralNominalVersionedMixedGrowth234
import Yulang.GeneralNominalVersionedMixedKernel234
import Yulang.GeneralNominalVersionedMixedKernelCache234
import Yulang.GeneralNominalVersionedMixedRecorded234
import Yulang.GeneralNominalVersionedMixedRefreshEquality234
import Yulang.GeneralNominalVersionedMixedRegistry234
import Yulang.GeneralNominalVersionedMixedSourceBoundary234
import Yulang.GeneralNominalVersionedMixedSourceFrontiers234
import Yulang.GeneralNominalVersionedMixedTerminalStable234
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryMixedUpperEvidence234,`Yulang.GeneralDictionaryMixedUpperFrame234,`Yulang.GeneralDictionaryMixedUpperPlan234,`Yulang.GeneralDictionaryMixedUpperSemantics234,`Yulang.GeneralDictionaryMixedUpperStep234,`Yulang.GeneralDictionaryMixedUpperTransport234,`Yulang.GeneralNominalVersionedMixedBoundary234,`Yulang.GeneralNominalVersionedMixedEmbedding234,`Yulang.GeneralNominalVersionedMixedEvidenceTransport234,`Yulang.GeneralNominalVersionedMixedGrowth234,`Yulang.GeneralNominalVersionedMixedKernel234,`Yulang.GeneralNominalVersionedMixedKernelCache234,`Yulang.GeneralNominalVersionedMixedRecorded234,`Yulang.GeneralNominalVersionedMixedRefreshEquality234,`Yulang.GeneralNominalVersionedMixedRegistry234,`Yulang.GeneralNominalVersionedMixedSourceBoundary234,`Yulang.GeneralNominalVersionedMixedSourceFrontiers234,`Yulang.GeneralNominalVersionedMixedTerminalStable234]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE234-FIRST-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE234-FIRST-FAIL: no constants checked"
  logInfo m!"CYCLE234-FIRST-PASS: {checked} constants in {modules.size} modules"
