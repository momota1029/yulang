import Yulang.GeneralFiniteWitnessSupport244
import Yulang.GeneralFiniteWitnessReadback244
import Yulang.GeneralNominalRebaseSyntaxGrowth244
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let modules := #[`Yulang.GeneralFiniteWitnessSupport244, `Yulang.GeneralFiniteWitnessReadback244, `Yulang.GeneralNominalRebaseSyntaxGrowth244]
 let mut checked : Nat := 0
 for (name, _) in environment.constants.toList do
  if let some index := environment.getModuleIdxFor? name then
   if modules.contains environment.header.moduleNames[index.toNat]! then
    checked := checked + 1
    for dependency in ← collectAxioms name do
     unless allowed.contains dependency do
      throwError "CYCLE244-FAIL: {name} depends on {dependency}"
 if checked = 0 then throwError "CYCLE244-FAIL: empty audit"
 logInfo m!"CYCLE244-PASS: {checked} constants in {modules.size} modules"
