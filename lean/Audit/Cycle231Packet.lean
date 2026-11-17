import Yulang.GeneralDictionaryVersionedEvidence231
import Yulang.GeneralDictionaryVersionedPacket231
import Yulang.GeneralDictionaryVersionedPrepared231
import Yulang.GeneralDictionaryVersionedProjection231
import Yulang.GeneralNominalVersionedCandidates231
import Yulang.GeneralNominalVersionedEffects231
import Yulang.GeneralNominalVersionedEvidence231
import Yulang.GeneralNominalVersionedFrame231
import Yulang.GeneralNominalVersionedPlans231
import Yulang.GeneralNominalVersionedPool231
import Yulang.GeneralNominalVersionedRefinement231
import Yulang.GeneralNominalVersionedRevisit231
import Yulang.GeneralNominalVersionedTransport231
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryVersionedEvidence231,`Yulang.GeneralDictionaryVersionedPacket231,`Yulang.GeneralDictionaryVersionedPrepared231,`Yulang.GeneralDictionaryVersionedProjection231,`Yulang.GeneralNominalVersionedCandidates231,`Yulang.GeneralNominalVersionedEffects231,`Yulang.GeneralNominalVersionedEvidence231,`Yulang.GeneralNominalVersionedFrame231,`Yulang.GeneralNominalVersionedPlans231,`Yulang.GeneralNominalVersionedPool231,`Yulang.GeneralNominalVersionedRefinement231,`Yulang.GeneralNominalVersionedRevisit231,`Yulang.GeneralNominalVersionedTransport231]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE231-PACKET-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE231-PACKET-FAIL: no constants checked"
  logInfo m!"CYCLE231-PACKET-PASS: {checked} constants in {modules.size} modules"
