import Yulang.GeneralDictionaryMixedGround218Resolution236
import Yulang.GeneralDictionaryMixedGround218RootFrame236
import Yulang.GeneralDictionaryMixedGround218RootSelected236
import Yulang.GeneralNominalFiniteEquationRealization236
import Yulang.GeneralNominalSemanticRawFrame236
import Yulang.GeneralNominalVersionedAggregateRealization236
import Yulang.GeneralNominalVersionedMixedChoice236
import Yulang.GeneralNominalVersionedMixedChoiceHistory236
import Yulang.GeneralNominalVersionedPrivateCompletion236
import Yulang.GeneralNominalVersionedSemanticCompletion236
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryMixedGround218Resolution236, `Yulang.GeneralDictionaryMixedGround218RootFrame236, `Yulang.GeneralDictionaryMixedGround218RootSelected236, `Yulang.GeneralNominalFiniteEquationRealization236, `Yulang.GeneralNominalSemanticRawFrame236, `Yulang.GeneralNominalVersionedAggregateRealization236, `Yulang.GeneralNominalVersionedMixedChoice236, `Yulang.GeneralNominalVersionedMixedChoiceHistory236, `Yulang.GeneralNominalVersionedPrivateCompletion236, `Yulang.GeneralNominalVersionedSemanticCompletion236]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE236-SECOND-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE236-SECOND-FAIL: no constants checked"
  logInfo m!"CYCLE236-SECOND-PASS: {checked} constants in {modules.size} modules"
