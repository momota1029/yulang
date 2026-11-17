import Yulang.GeneralDictionaryVersionedTrusted233
import Yulang.GeneralNominalVersionedMixedObservations233
import Yulang.GeneralNominalVersionedObservationTransport233
import Yulang.GeneralNominalVersionedObservations233
import Yulang.GeneralNominalVersionedRegistry233
import Yulang.GeneralNominalVersionedSupport233
import Yulang.GeneralNominalVersionedSupportCache233
import Yulang.GeneralNominalVersionedSupportGrowth233
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryVersionedTrusted233,`Yulang.GeneralNominalVersionedMixedObservations233,`Yulang.GeneralNominalVersionedObservationTransport233,`Yulang.GeneralNominalVersionedObservations233,`Yulang.GeneralNominalVersionedRegistry233,`Yulang.GeneralNominalVersionedSupport233,`Yulang.GeneralNominalVersionedSupportCache233,`Yulang.GeneralNominalVersionedSupportGrowth233]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE233-THIRD-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE233-THIRD-FAIL: no constants checked"
  logInfo m!"CYCLE233-THIRD-PASS: {checked} constants in {modules.size} modules"
