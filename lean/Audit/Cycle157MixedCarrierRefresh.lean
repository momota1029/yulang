import Yulang.GeneralDictionaryMixedCarrierRefresh
import Lean
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.target_fresh
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.output_int
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.snapshot_models
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.target_reserved
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.output_member
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.output_not_known
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.output_known
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.refresh_step
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.refreshed_models
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.refreshed_reachable
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.refreshed_inhabited
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.report_current
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.bindings_exact
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.origins
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.packet_recorded
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.replay
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.carrier_changed
#print axioms Yulang.GeneralDictionaryMixedCarrierRefresh.nonvacuous_replay

open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryMixedCarrierRefresh]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if wanted.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} (module {moduleName}) depends on {dependency}"
  if checked = 0 then throwError "AXIOM-GATE-FAIL: no declarations checked"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"
