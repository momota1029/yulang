import Yulang.GeneralNominalRebaseScheduler242
import Yulang.GeneralNominalRebaseSchedulerOrder242
import Yulang.GeneralDictionaryRebase230Scheduler242
import Yulang.GeneralNominalRebaseAggregateFinite242
import Yulang.GeneralNominalRebaseBirth242
import Yulang.GeneralNominalRebaseGenealogy242
import Yulang.GeneralNominalRebaseOwnerUniverse242
import Yulang.GeneralNominalRebaseGround242
import Yulang.GeneralNominalRebaseBatch242
import Yulang.GeneralNominalRebaseEscapedProjection242
import Yulang.GeneralNominalRebaseEscapedReplace242
import Yulang.GeneralNominalRebaseEscapedStore242
import Yulang.GeneralNominalRebaseEscapedMerges242
import Yulang.GeneralDictionaryRebaseEscapedExample242
import Yulang.GeneralNominalRebaseInstall242
import Yulang.GeneralNominalRebaseOperational242
import Yulang.GeneralNominalRebaseOperationalOwners242
import Yulang.GeneralNominalRebaseBirthWitness242
import Yulang.GeneralNominalRebaseRawProjection242
import Yulang.GeneralNominalRebaseOwnerIndex242
import Yulang.GeneralNominalRebaseDistinctOwners242
import Yulang.GeneralNominalRebasePrivateUniverse242
import Yulang.GeneralDictionaryRebaseNewCellObstruction242
import Yulang.GeneralNominalRebaseExecutor242
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalRebaseScheduler242, `Yulang.GeneralNominalRebaseSchedulerOrder242, `Yulang.GeneralDictionaryRebase230Scheduler242, `Yulang.GeneralNominalRebaseAggregateFinite242, `Yulang.GeneralNominalRebaseBirth242, `Yulang.GeneralNominalRebaseGenealogy242, `Yulang.GeneralNominalRebaseOwnerUniverse242, `Yulang.GeneralNominalRebaseGround242, `Yulang.GeneralNominalRebaseBatch242, `Yulang.GeneralNominalRebaseEscapedProjection242, `Yulang.GeneralNominalRebaseEscapedReplace242, `Yulang.GeneralNominalRebaseEscapedStore242, `Yulang.GeneralNominalRebaseEscapedMerges242, `Yulang.GeneralDictionaryRebaseEscapedExample242, `Yulang.GeneralNominalRebaseInstall242, `Yulang.GeneralNominalRebaseOperational242, `Yulang.GeneralNominalRebaseOperationalOwners242, `Yulang.GeneralNominalRebaseBirthWitness242, `Yulang.GeneralNominalRebaseRawProjection242, `Yulang.GeneralNominalRebaseOwnerIndex242, `Yulang.GeneralNominalRebaseDistinctOwners242, `Yulang.GeneralNominalRebasePrivateUniverse242, `Yulang.GeneralDictionaryRebaseNewCellObstruction242, `Yulang.GeneralNominalRebaseExecutor242]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE242-FOURTH-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE242-FOURTH-FAIL: no constants checked"
  logInfo m!"CYCLE242-FOURTH-PASS: {checked} constants in {modules.size} modules"
