import Yulang.GeneralNominalSelectiveEquationRealization236
import Yulang.GeneralNominalVersionedAggregateActual236
import Yulang.GeneralNominalVersionedAggregateEntries236
import Yulang.GeneralNominalVersionedAggregateLedger236
import Yulang.GeneralNominalVersionedMixedLedgerCompletion236
import Yulang.GeneralNominalVersionedMixedSelectiveCompletion236
import Yulang.GeneralNominalVersionedSelectiveActual236
import Yulang.GeneralNominalVersionedSelectiveAggregate236
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalSelectiveEquationRealization236, `Yulang.GeneralNominalVersionedAggregateActual236, `Yulang.GeneralNominalVersionedAggregateEntries236, `Yulang.GeneralNominalVersionedAggregateLedger236, `Yulang.GeneralNominalVersionedMixedLedgerCompletion236, `Yulang.GeneralNominalVersionedMixedSelectiveCompletion236, `Yulang.GeneralNominalVersionedSelectiveActual236, `Yulang.GeneralNominalVersionedSelectiveAggregate236]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE236-FOURTH-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE236-FOURTH-FAIL: no constants checked"
  logInfo m!"CYCLE236-FOURTH-PASS: {checked} constants in {modules.size} modules"
