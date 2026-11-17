import Yulang.GeneralDictionaryMixedGround218Point235
import Yulang.GeneralDictionaryMixedGround218PointAllModels235
import Yulang.GeneralDictionaryMixedGround218PointChildren235
import Yulang.GeneralDictionaryMixedGround218PointFrame235
import Yulang.GeneralDictionaryMixedGround218PointInstall235
import Yulang.GeneralDictionaryMixedGround218PointLeaf235
import Yulang.GeneralDictionaryMixedGround218PointPacket235
import Yulang.GeneralDictionaryMixedGround218PointRefresh235
import Yulang.GeneralDictionaryMixedGround218PointSafety235
import Yulang.GeneralDictionaryMixedGround218PointStable235
import Yulang.GeneralDictionaryMixedGround218PointUniform235
import Yulang.GeneralDictionaryMixedGround218Refresh235
import Yulang.GeneralDictionaryMixedGround218Reobserve235
import Yulang.GeneralNominalVersionedMixedCommon235
import Yulang.GeneralNominalVersionedMixedCompletionRequests235
import Yulang.GeneralNominalVersionedMixedEqualityClosure235
import Yulang.GeneralNominalVersionedMixedInstallRequests235
import Yulang.GeneralNominalVersionedMixedQuietInstall235
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryMixedGround218Point235,`Yulang.GeneralDictionaryMixedGround218PointAllModels235,`Yulang.GeneralDictionaryMixedGround218PointChildren235,`Yulang.GeneralDictionaryMixedGround218PointFrame235,`Yulang.GeneralDictionaryMixedGround218PointInstall235,`Yulang.GeneralDictionaryMixedGround218PointLeaf235,`Yulang.GeneralDictionaryMixedGround218PointPacket235,`Yulang.GeneralDictionaryMixedGround218PointRefresh235,`Yulang.GeneralDictionaryMixedGround218PointSafety235,`Yulang.GeneralDictionaryMixedGround218PointStable235,`Yulang.GeneralDictionaryMixedGround218PointUniform235,`Yulang.GeneralDictionaryMixedGround218Refresh235,`Yulang.GeneralDictionaryMixedGround218Reobserve235,`Yulang.GeneralNominalVersionedMixedCommon235,`Yulang.GeneralNominalVersionedMixedCompletionRequests235,`Yulang.GeneralNominalVersionedMixedEqualityClosure235,`Yulang.GeneralNominalVersionedMixedInstallRequests235,`Yulang.GeneralNominalVersionedMixedQuietInstall235]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE235-FOURTH-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE235-FOURTH-FAIL: no constants checked"
  logInfo m!"CYCLE235-FOURTH-PASS: {checked} constants in {modules.size} modules"
