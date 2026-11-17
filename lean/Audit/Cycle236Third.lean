import Yulang.GeneralNominalVersionedAggregateReuse236
import Yulang.GeneralNominalVersionedDependency236
import Yulang.GeneralNominalVersionedExpressionFrame236
import Yulang.GeneralNominalVersionedHeadFrame236
import Yulang.GeneralNominalVersionedInitialCompletion236
import Yulang.GeneralNominalVersionedJournalFrame236
import Yulang.GeneralNominalVersionedMixedFreshCompletion236
import Yulang.GeneralNominalVersionedMixedSelectedWitness236
import Yulang.GeneralNominalVersionedPacketFrame236
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalVersionedAggregateReuse236, `Yulang.GeneralNominalVersionedDependency236, `Yulang.GeneralNominalVersionedExpressionFrame236, `Yulang.GeneralNominalVersionedHeadFrame236, `Yulang.GeneralNominalVersionedInitialCompletion236, `Yulang.GeneralNominalVersionedJournalFrame236, `Yulang.GeneralNominalVersionedMixedFreshCompletion236, `Yulang.GeneralNominalVersionedMixedSelectedWitness236, `Yulang.GeneralNominalVersionedPacketFrame236]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE236-THIRD-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE236-THIRD-FAIL: no constants checked"
  logInfo m!"CYCLE236-THIRD-PASS: {checked} constants in {modules.size} modules"
