import Yulang.GeneralDictionaryCapturedSettledProducerTrust
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryCapturedSettledProducerTrust]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if wanted.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "AXIOM-GATE-FAIL: no declarations checked"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"

#check @Yulang.GeneralDictionaryCapturedSettledProducerTrust.parent_trusted
#check @Yulang.GeneralDictionaryCapturedSettledProducerTrust.terminal_settled
#check @Yulang.GeneralDictionaryCapturedSettledProducerTrust.input_variables_empty
#check @Yulang.GeneralDictionaryCapturedSettledProducerTrust.endpoint_observation
#check @Yulang.GeneralDictionaryCapturedSettledProducerTrust.input_readback
#check @Yulang.GeneralDictionaryCapturedSettledProducerTrust.int_recipe
#check @Yulang.GeneralDictionaryCapturedSettledProducerTrust.producer_output_trusted
