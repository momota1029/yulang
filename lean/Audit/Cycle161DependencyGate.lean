import Yulang.GeneralDictionaryChildCaptureExample
import Yulang.GeneralDictionaryChildCaptureTransport
import Yulang.GeneralDictionaryEmissionRequestIdentity
import Yulang.GeneralDictionaryNonterminalCertifiedEvidence
import Yulang.GeneralDictionaryNonterminalChildEvidence
import Yulang.GeneralDictionaryNonterminalNamedEvidence
import Yulang.GeneralDictionaryNonterminalNamedExample
import Yulang.GeneralDictionaryNonterminalNonpointBranch
import Yulang.GeneralDictionaryNonterminalNonpointEvidence
import Yulang.GeneralDictionaryNonterminalNonpointExample
import Yulang.GeneralDictionaryNonterminalOldObstruction
import Yulang.GeneralDictionaryNonterminalRecordedRevision
import Yulang.GeneralDictionaryNonterminalScope
import Yulang.GeneralDictionaryRecordedLeafPlans
import Yulang.GeneralDictionaryRequestSnapshot
import Yulang.GeneralDictionaryValuePendingExclusion
import Yulang.GeneralDictionaryVariableIntervalLeaf
import Yulang.GeneralDictionaryVariableLeafPlans
import Yulang.GeneralDictionaryVariableWhereRequests
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryChildCaptureExample, `Yulang.GeneralDictionaryChildCaptureTransport, `Yulang.GeneralDictionaryEmissionRequestIdentity, `Yulang.GeneralDictionaryNonterminalCertifiedEvidence, `Yulang.GeneralDictionaryNonterminalChildEvidence, `Yulang.GeneralDictionaryNonterminalNamedEvidence, `Yulang.GeneralDictionaryNonterminalNamedExample, `Yulang.GeneralDictionaryNonterminalNonpointBranch, `Yulang.GeneralDictionaryNonterminalNonpointEvidence, `Yulang.GeneralDictionaryNonterminalNonpointExample, `Yulang.GeneralDictionaryNonterminalOldObstruction, `Yulang.GeneralDictionaryNonterminalRecordedRevision, `Yulang.GeneralDictionaryNonterminalScope, `Yulang.GeneralDictionaryRecordedLeafPlans, `Yulang.GeneralDictionaryRequestSnapshot, `Yulang.GeneralDictionaryValuePendingExclusion, `Yulang.GeneralDictionaryVariableIntervalLeaf, `Yulang.GeneralDictionaryVariableLeafPlans, `Yulang.GeneralDictionaryVariableWhereRequests]
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
