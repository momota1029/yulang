import Yulang.GeneralDictionaryCenteredNominal178
import Yulang.GeneralDictionaryCenteredNominalExample178
import Yulang.GeneralDictionaryCenteredNominalPoint178
import Yulang.GeneralDictionaryCenteredNominalPointExample178
import Yulang.GeneralDictionaryCenteredNullary178
import Yulang.GeneralDictionaryCenteredSharedNominal178
import Yulang.GeneralDictionaryNominalPair178
import Yulang.GeneralDictionaryNominalPairDiscovery178
import Yulang.GeneralDictionaryNominalPairExample178
import Yulang.GeneralDictionaryNominalPairExtrema178
import Yulang.GeneralDictionaryNominalPairInitial178
import Yulang.GeneralDictionaryNominalPairJoint178
import Yulang.GeneralDictionaryNominalPairShared178
import Yulang.GeneralDictionaryNominalPairSourceSupport178
import Yulang.GeneralDictionaryNominalPairSupport178
import Yulang.GeneralNominalMergeResidual178
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

#print axioms Yulang.GeneralDictionaryCenteredNominalPoint178.nullary_evidence
#print axioms Yulang.GeneralDictionaryNominalPairInitial178.stable_instance_of_joint

#print axioms Yulang.GeneralDictionaryNominalPairShared178.branch_models_iff_shared_residual
#print axioms Yulang.GeneralDictionaryCenteredSharedNominal178.candidate_evidence
#print axioms Yulang.GeneralDictionaryCenteredNullary178.evidence_at_G
