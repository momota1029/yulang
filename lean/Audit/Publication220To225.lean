import Yulang.GeneralDictionaryAdministrativeSemanticSupport222
import Yulang.GeneralDictionarySemanticDelta223
import Yulang.GeneralDictionaryTightProjection224
import Yulang.GeneralDictionaryTightPacket224
import Yulang.GeneralDictionaryRelativePacket225
import Yulang.GeneralDictionaryHeadSharingSemanticSupport220
import Yulang.GeneralDictionaryHeadSharingRawSupport220
import Yulang.B4TargetV8
import Yulang.B4SkeletonV8
import Yulang.GeneralDictionaryHeadSharing220
import Yulang.GeneralDictionaryHeadSharingAccessible220
import Yulang.GeneralDictionaryHeadSharingAmalgamation220
import Yulang.GeneralDictionaryHeadSharingBoundary220
import Yulang.GeneralDictionaryHeadSharingCanonical220
import Yulang.GeneralDictionaryHeadSharingComposition220
import Yulang.GeneralDictionaryHeadSharingConflict220
import Yulang.GeneralDictionaryHeadSharingExecutor220
import Yulang.GeneralDictionaryHeadSharingLaws220
import Yulang.GeneralDictionaryHeadSharingPrecision220
import Yulang.GeneralDictionaryHeadSharingPrior220
import Yulang.GeneralDictionaryHeadSharingRegression220
import Yulang.GeneralDictionaryHeadSharingSemantic220
import Yulang.GeneralDictionaryHeadSharingSoundness220
import Yulang.GeneralDictionaryHeadSharingSpecification220
import Yulang.GeneralDictionaryHeadSharingTransport220
import Yulang.GeneralDictionaryHeadSharingWitness220
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[ `Yulang.GeneralDictionaryHeadSharingSemanticSupport220, `Yulang.GeneralDictionaryHeadSharingRawSupport220, `Yulang.B4TargetV8, `Yulang.B4SkeletonV8, `Yulang.GeneralDictionaryHeadSharing220, `Yulang.GeneralDictionaryHeadSharingAccessible220, `Yulang.GeneralDictionaryHeadSharingAmalgamation220, `Yulang.GeneralDictionaryHeadSharingBoundary220, `Yulang.GeneralDictionaryHeadSharingCanonical220, `Yulang.GeneralDictionaryHeadSharingComposition220, `Yulang.GeneralDictionaryHeadSharingConflict220, `Yulang.GeneralDictionaryHeadSharingExecutor220, `Yulang.GeneralDictionaryHeadSharingLaws220, `Yulang.GeneralDictionaryHeadSharingPrecision220, `Yulang.GeneralDictionaryHeadSharingPrior220, `Yulang.GeneralDictionaryHeadSharingRegression220, `Yulang.GeneralDictionaryHeadSharingSemantic220, `Yulang.GeneralDictionaryHeadSharingSoundness220, `Yulang.GeneralDictionaryHeadSharingSpecification220, `Yulang.GeneralDictionaryHeadSharingTransport220, `Yulang.GeneralDictionaryHeadSharingWitness220, `Yulang.GeneralDictionaryAdministrativeSemanticSupport222, `Yulang.GeneralDictionarySemanticDelta223, `Yulang.GeneralDictionaryTightProjection224, `Yulang.GeneralDictionaryTightPacket224, `Yulang.GeneralDictionaryRelativePacket225 ]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "PUBLICATION220-225-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "PUBLICATION220-225-FAIL: no constants checked"
  logInfo m!"PUBLICATION220-225-PASS: {checked} constants in {modules.size} modules"
