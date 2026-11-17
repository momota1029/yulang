import Yulang.GeneralNominalRebaseScheduler242
import Yulang.GeneralNominalRebaseSchedulerOrder242
import Yulang.GeneralNominalRebaseBirth242
import Yulang.GeneralNominalRebaseGenealogy242
import Yulang.GeneralNominalRebaseOwnerUniverse242
import Yulang.GeneralNominalRebaseEscapedProjection242
import Yulang.GeneralNominalRebaseEscapedReplace242
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalRebaseScheduler242, `Yulang.GeneralNominalRebaseSchedulerOrder242, `Yulang.GeneralNominalRebaseBirth242, `Yulang.GeneralNominalRebaseGenealogy242, `Yulang.GeneralNominalRebaseOwnerUniverse242, `Yulang.GeneralNominalRebaseEscapedProjection242, `Yulang.GeneralNominalRebaseEscapedReplace242]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE242-FIRST-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE242-FIRST-FAIL: no constants checked"
  logInfo m!"CYCLE242-FIRST-PASS: {checked} constants in {modules.size} modules"
