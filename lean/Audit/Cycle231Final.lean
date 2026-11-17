import Yulang.GeneralDictionaryVersionedModelExtension231
import Yulang.GeneralDictionaryVersionedCompletion231
import Yulang.GeneralDictionaryVersionedFinal231
import Yulang.GeneralDictionaryVersionedReconstruction231
import Yulang.GeneralDictionaryVersionedUniversal231
import Yulang.GeneralNominalVersionedConservative231
import Yulang.GeneralNominalVersionedFiniteBindings231
import Yulang.GeneralNominalVersionedInstallation231
import Yulang.GeneralNominalVersionedPreparedTransport231
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryVersionedModelExtension231,`Yulang.GeneralDictionaryVersionedCompletion231,`Yulang.GeneralDictionaryVersionedFinal231,`Yulang.GeneralDictionaryVersionedReconstruction231,`Yulang.GeneralDictionaryVersionedUniversal231,`Yulang.GeneralNominalVersionedConservative231,`Yulang.GeneralNominalVersionedFiniteBindings231,`Yulang.GeneralNominalVersionedInstallation231,`Yulang.GeneralNominalVersionedPreparedTransport231]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE231-FINAL-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE231-FINAL-FAIL: no constants checked"
  logInfo m!"CYCLE231-FINAL-PASS: {checked} constants in {modules.size} modules"
