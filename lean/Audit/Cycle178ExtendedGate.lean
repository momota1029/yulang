import Yulang.GeneralDictionaryNominalPairJoint178
import Yulang.GeneralDictionaryNominalPairDiscovery178
import Yulang.GeneralDictionaryCenteredNominalExample178
import Yulang.GeneralDictionaryCenteredNominal178
import Yulang.GeneralDictionaryNominalPairExtrema178
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if moduleName.toString.endsWith "178" then
        checked := checked + 1
        for dependency in ← collectAxioms name do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "empty gate"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations (definitions/private/generated included)"
#print axioms Yulang.GeneralDictionaryNominalPair178.branch_models_iff_residual
#print axioms Yulang.GeneralDictionaryCenteredNominal178.candidate_holds_iff_extrema
#print axioms Yulang.GeneralDictionaryCenteredNominal178.candidate_evidence_node
#print axioms Yulang.GeneralDictionaryNominalPairExtrema178.merges_iff_pair_extrema

#print axioms Yulang.GeneralDictionaryCenteredNominalExample178.evidence_not_from_candidate_alone

#print axioms Yulang.GeneralDictionaryNominalPairJoint178.stable_not_selected
#print axioms Yulang.GeneralDictionaryNominalPairDiscovery178.candidate_evidence
